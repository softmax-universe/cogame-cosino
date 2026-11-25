import cosino/prompts
## The scripted baselines are the completion path: they are the
## no-credentials fallback (offline certification), the fallback whenever a
## model decision fails, AND two fieldable policies. They must be legal at
## every rung and every seat count, always.

import std/[json, monotimes, strutils, times, unicode, unittest]
import cosino/[llm, sim]

proc fixture(variant: Variant, seats: int, seed: int,
    hands = 8): GameConfig =
  result = defaultGameConfig()
  result.variantDefaults(variant)
  result.seed = seed
  result.hands = hands
  ## Pinned, so these tests exercise the rules rather than the budget cap.
  result.sampled = true
  for index in 0 ..< seats:
    result.players.add(PlayerConfig(name: "P" & $(index + 1)))
    result.tokens.add("t" & $index)

suite "bounded orders: the baseline is always legal":
  test "house and rock play 200 matches at every rung and seat count":
    ## 4 tables x 2 baselines x 200 matches. `applyAction` raises on ANY
    ## illegal move, so a single bad amount or an out-of-turn action fails
    ## this test.
    for (variant, seats) in [(vKuhn, 2), (vLeduc, 2), (vHoldem, 2),
        (vHoldem, 6)]:
      for baseline in [blHouse, blRock]:
        for run in 0 ..< 200:
          var config = fixture(variant, seats, 1000 + run)
          let client = newLlmClient(config)
          var match = initMatch(config)
          let chips = seats * config.startingStack
          var actions = 0
          while not match.done:
            while not match.sim.done:
              let seat = match.sim.actingSeat
              check seat >= 0
              let decision = client.scriptedAction(match.sim, seat, baseline)
              ## Every amount must already be inside the engine's own bounds.
              case decision.action.kind
              of akBet:
                check decision.action.amount >= match.sim.minBet(seat)
                check decision.action.amount <= match.sim.maxRaiseTo(seat)
              of akRaise:
                check decision.action.amount >= match.sim.minRaiseTo(seat)
                check decision.action.amount <= match.sim.maxRaiseTo(seat)
              else: discard
              match.sim.applyAction(seat, decision.action)
              inc actions
              check actions < 20_000
            var onTable = 0
            for seat in match.sim.seats:
              onTable += seat.stack
            check onTable == chips
            match.finishHand()
            if not match.done:
              match.nextHand()
          check match.handsPlayed == config.hands
          ## Zero-sum, and the score share therefore sums to exactly 1.
          ## (The recorded tail -- calib and audit -- is exercised by
          ## test_sim and test_audit; running the exact solver and the
          ## 2000-runout equity Monte Carlo 1600 times over would say
          ## nothing new and would cost minutes.)
          var netSum = 0
          var total = 0.0
          for slot in 0 ..< seats:
            netSum += match.net[slot]
            total += 1.0 / seats.float + match.net[slot].float /
              (seats.float * config.startingStack.float *
                match.handsScored.float)
          check netSum == 0
          check abs(total - 1.0) < 1e-9

suite "strict decision contract: no implicit fallbacks":
  test "decide with no credentials raises transport failure instead of scripted fallback":
    var config = fixture(vHoldem, 3, 11)
    let client = newScriptedClient(config)
    check not client.credentialled()
    var match = initMatch(config)
    let seat = match.sim.actingSeat
    let started = getMonoTime()
    var raised = false
    var transport = false
    try:
      discard client.decide(match.sim, seat, "raise every hand",
        selection = PromptSelection(), scripted = false)
    except CosinoFailureError as err:
      raised = true
      transport = err.transportFailure
    let elapsed = (getMonoTime() - started).inMilliseconds
    check raised
    check transport
    check elapsed < 500

  test "explicit scripted seats still run their chosen baseline":
    var config = fixture(vHoldem, 3, 11)
    let client = newScriptedClient(config)
    var match = initMatch(config)
    let seat = match.sim.actingSeat
    let decision = client.decide(match.sim, seat, "",
      selection = PromptSelection(), scripted = true, baseline = blHouse)
    check not decision.fallback
    match.sim.applyAction(seat, decision.action)

  test "extractJsonObject accepts plain JSON and standard outer markdown fence only":
    let plain = extractJsonObject("""{"say": "", "action": "check"}""")
    check plain["action"].getStr() == "check"
    let fenced = extractJsonObject("```json\n{\"say\": \"hi\", \"action\": \"fold\"}\n```")
    check fenced["action"].getStr() == "fold"
    let bareFence = extractJsonObject("```\n{\"action\": \"call\"}\n```")
    check bareFence["action"].getStr() == "call"
    for garbage in [
      "",
      "I think I will raise",
      "```\nnope\n```",
      "Here is my move: {\"action\": \"fold\"}",
      "{\"action\": \"fold\"} thanks!",
      "```yaml\n{\"action\": \"fold\"}\n```",
      "[1, 2, 3]"
    ]:
      expect CosinoError:
        discard extractJsonObject(garbage)

  test "an illegal action raises without mutating sim or substituting baseline":
    var config = fixture(vHoldem, 3, 12)
    let client = newScriptedClient(config)
    var match = initMatch(config)
    let seat = match.sim.actingSeat
    let beforeEvents = match.sim.events.len
    ## A raise far beyond the stack: the engine rejects it outright.
    let bogus = Decision(say: "shove",
      action: PlayerAction(kind: akRaise, amount: 10_000))
    expect CosinoError:
      discard client.applyDecision(match.sim, seat, bogus)
    check match.sim.actingSeat == seat
    check match.sim.events.len == beforeEvents

  test "call when facing zero stays akCall and is rejected by the engine":
    var config = fixture(vKuhn, 2, 13)
    let client = newScriptedClient(config)
    var match = initMatch(config)
    let seat = match.sim.actingSeat
    check match.sim.callAmount(seat) == 0
    let parsed = parseDecision(match.sim, seat, %*{"action": "call", "say": ""})
    check parsed.action.kind == akCall
    expect CosinoError:
      discard client.applyDecision(match.sim, seat, parsed)

suite "hostile model output":
  test "a 5 kB emoji say is capped at 120 runes and the replay stays UTF-8":
    var config = fixture(vHoldem, 3, 15)
    var match = initMatch(config)
    let seat = match.sim.actingSeat
    let hostile = "\u{1F0A1}\u{1F0D2}\u{1F0B3}".repeat(700)
    check hostile.len > 5000
    let payload = %*{"say": hostile, "action": "fold"}
    let decision = parseDecision(match.sim, seat, payload)
    check decision.say.runeLen == MaxSayLen
    check decision.say.validateUtf8() == -1
    match.sim.recordSay(seat, decision.say)
    match.sim.applyAction(seat, decision.action)
    var events = newJArray()
    for event in match.allEvents():
      events.add(event.eventToJson())
    let replay = $ %*{"events": events}
    check replay.validateUtf8() == -1
    ## And it survives a strict round trip through the JSON parser.
    let reparsed = parseJson(replay)
    var found = false
    for node in reparsed["events"]:
      if node{"kind"}.getStr() == "say":
        found = true
        check node["text"].getStr().runeLen == MaxSayLen
    check found

  test "unknown verbs and non-canonical aliases are rejected":
    var config = fixture(vHoldem, 3, 16)
    var match = initMatch(config)
    let seat = match.sim.actingSeat
    for alias in ["teleport", "allin", "all-in", "all in", "shove", ""]:
      expect CosinoError:
        discard parseDecision(match.sim, seat, %*{"action": alias})
    expect CosinoError:
      discard parseDecision(match.sim, seat, %*{"action": "fold", "say": false})
    expect CosinoError:
      discard parseDecision(match.sim, seat, %*{"action": "bet", "amount": "10"})

  test "baselines require explicit house or rock":
    check parseBaseline("rock") == blRock
    check parseBaseline("ROCK") == blRock
    check parseBaseline("house") == blHouse
    check parseBaseline("HOUSE") == blHouse
    for bad in ["", "whatever", "true", "1"]:
      expect CosinoError:
        discard parseBaseline(bad)
