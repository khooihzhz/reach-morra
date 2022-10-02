'reach 0.1';

const [ isOutcome, ALICE_WINS, DRAW, BOB_WINS ] = makeEnum(3);

const matchOutcome = (fingersAlice, fingersBob, guessAlice, guessBob) => {
  if (guessAlice == guessBob) {
    const outcome = DRAW;
    return outcome;
  } else {
    if ((fingersAlice + fingersBob) == guessAlice) {
      // Alice Guess correctly
      const outcome = ALICE_WINS;
      return outcome;
    } 
    else {
      // Bob Guess Correctly
      if ((fingersAlice + fingersBob) == guessBob){
        const outcome = BOB_WINS;
        return outcome;
      }else {
        // Neither Won
        const outcome = DRAW;
        return outcome;
      }
    }
  }
}

assert(matchOutcome(0, 4, 0, 4) == BOB_WINS)
assert(matchOutcome(4, 0, 4, 0) == ALICE_WINS)
assert(matchOutcome(0, 1, 0, 4) == DRAW)
assert(matchOutcome(5, 5, 5, 5) == DRAW)

forall(UInt, a =>
  forall(UInt, b =>
    forall(UInt, c =>
      forall(UInt, d =>
        assert(isOutcome(matchOutcome(a, b, c, d)))))));

forall(UInt, a =>
  forall(UInt, b =>
    forall(UInt, c =>
        assert(matchOutcome(a, b, c, c) == DRAW ))));

const Player = {
  ...hasRandom,
  getFingers: Fun([], UInt),
  getGuess: Fun([], UInt),
  seeOutcome: Fun([UInt], Null),
  informTimeout: Fun([], Null)
}

export const main = Reach.App(() => {          
  const Alice = Participant('Alice', {
    ...Player,
    wager: UInt,
    deadline: UInt,
  });

  const Bob = Participant('Bob', {
    ...Player,
    acceptWager: Fun([UInt], Null),
  });
  init(); // Deploy 

  const informTimeout = () => {
    each([Alice, Bob], () => {
      interact.informTimeout();
    })
  }
  // Alice Interactions
  Alice.only(() => {
    const amt = declassify(interact.wager);
    const time = declassify(interact.deadline);
  })

  Alice.publish(amt, time)
    .pay(amt);

  commit();

  // Bob accept Wager
  Bob.only(() => {
    interact.acceptWager(amt);
  })

  Bob.pay(amt)
    .timeout(relativeTime(time), () => closeTo(Alice, informTimeout));

  var outcome = DRAW;
  // variable that does not change
  invariant(balance() == 2 * amt && isOutcome(outcome))
  // Continue to play while Draw
  while (outcome == DRAW)
  {
    commit();

    // start from Alice
    Alice.only(() => {
      const _fingersAlice = interact.getFingers();
      const _guessAlice = interact.getGuess();

      const [_commitAlice, _saltAlice] = makeCommitment(interact, _fingersAlice);
      const commitAlice = declassify(_commitAlice);
      const [_guessCommitAlice, _guessSaltAlice] = makeCommitment(interact, _guessAlice);
      const guessCommitAlice = declassify(_guessCommitAlice);
    });

    Alice.publish(commitAlice, guessCommitAlice)
      .timeout(relativeTime(time), () => closeTo(Bob, informTimeout));
    
    commit();

    unknowable(Bob, Alice(_fingersAlice, _saltAlice));
    unknowable(Bob, Alice(_guessAlice, _guessSaltAlice));

    Bob.only(() => {
      const _fingersBob = interact.getFingers();
      const _guessBob = interact.getGuess();

      // Alice ald committed we can already declassify it
      const fingersBob = declassify(_fingersBob);
      const guessBob = declassify(_guessBob);
    });

    Bob.publish(fingersBob, guessBob)
      .timeout(relativeTime(time), () => closeTo(Alice, informTimeout));
    
    commit();

    Alice.only(() => {
      const [saltAlice, fingersAlice] = declassify([_saltAlice, _fingersAlice])
      const [guessSaltAlice, guessAlice] = declassify([_guessSaltAlice, _guessAlice]); 
    })

    // Alice revealing Hands
    Alice.publish(saltAlice, guessAlice, fingersAlice, guessSaltAlice);

    outcome = matchOutcome(fingersAlice, fingersBob, guessAlice, guessBob);
    continue;
  }

  assert(outcome == ALICE_WINS || outcome == BOB_WINS);

  transfer(2 * amt).to(outcome == ALICE_WINS ? Alice : Bob);
  commit();

  each([Alice, Bob], () => {
    interact.seeOutcome(outcome);
  });

  exit();
});
