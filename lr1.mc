-- LR(1) parser example from the book by Appel 2nd edition, see pages 58-61
-- https://www.cambridge.org/se/academic/subjects/computer-science/programming-languages-and-applied-logic/modern-compiler-implementation-java-2nd-edition?format=HB&isbn=9780521820608

include "bool.mc"
include "common.mc"
include "map.mc"
include "name.mc"
include "option.mc"
include "set.mc"

-- TODO: Add these things to stdlib
let optionCmp: all a. all b. (a -> b -> Int) -> Option a -> Option b -> Int =
  lam cmp. lam o1. lam o2.
  switch (o1, o2)
  case (None (), None ()) then 0
  case (None (), Some _) then negi 1
  case (Some _, None ()) then 1
  case (Some v1, Some v2) then cmp v1 v2
  end

let cmp3tuple : all a. all b. all c. (a -> a -> Int) -> (b -> b -> Int) -> (c -> c -> Int) -> ((a, b, c) -> (a, b, c) -> Int) =
    lam cmpa. lam cmpb. lam cmpc. (lam x. lam y.
        let ra = cmpa x.0 y.0 in
        if neqi ra 0 then ra else --continue
        let rb = cmpb x.1 y.1 in
        if neqi rb 0 then rb else --continue
        cmpc x.2 y.2
    )


lang LexerToken
  syn Token =
  | EOF ()
  | LParen ()
  | RParen ()
  | Comma ()
  | Equality ()
  | Star ()
  | StringLiteral String

  sem tokenListAll : () -> [Token]
  sem tokenListAll =
  | _ -> [EOF (), LParen (), RParen (), Comma (), Equality (), Star (), StringLiteral ""]

  sem token2string : Token -> String
  sem token2string =
  | EOF _ -> "EOF"
  | LParen _ -> "\'(\'"
  | RParen _ -> "\')\'"
  | Comma _ -> "\',\'"
  | Equality _ -> "\'=\'"
  | Star _ -> "\'*\'"
  | StringLiteral s -> join ["\"", s, "\""]

  sem tokenId : Token -> Int
  sem tokenId =
  | EOF _ -> 0
  | LParen _ -> 1
  | RParen _ -> 2
  | Comma _ -> 3
  | Equality _ -> 4
  | Star _ -> 5
  | StringLiteral _ -> 6

  sem cmpTokenKind : Token -> Token -> Int
  sem cmpTokenKind other =
  | t -> subi (tokenId t) (tokenId other)

  sem eqTokenKind : Token -> Token -> Bool
  sem eqTokenKind other =
  | t -> eqi (cmpTokenKind other t) 0
end

lang LR1Base = LexerToken
  syn LR1Term =
  | Terminal Token
  | NonTerminal Name

  type LR1Rule = {
    name: Name,
    terms: [LR1Term]
  }

  type LR1SyntaxDef = {
    entrypoint: Name,
    rules: [LR1Rule]
  }

  type LR1StateItem = {
    name: Name,
    terms: [LR1Term],
    stackPointer: Int,
    lookahead: Token,
    ruleIdx: Int -- index of the rule that this item originates from
  }

  type LR1ParseTable = {
    entrypointIdx: Int,
    _debugStates: [Set LR1StateItem],
    nStates: Int,
    transitions: Map Int [{term: LR1Term, toIdx: Int}],
    reductions: Map Int [{lookahead: Token, ruleIdx: Int}]
  }

  sem lr1term2string : LR1Term -> String
  sem lr1term2string =
  | Terminal t -> token2string t
  | NonTerminal n -> join (["NonTerminal(", nameGetStr n, ")"])

  sem cmpLR1Term2 : (LR1Term, LR1Term) -> Int
  sem cmpLR1Term2 =
  | (Terminal t1, Terminal t2) -> cmpTokenKind t1 t2
  | (Terminal _, NonTerminal _) -> negi 1
  | (NonTerminal n1, NonTerminal n2) -> nameCmp n1 n2
  | (NonTerminal _, Terminal _) -> 1

  sem cmpLR1Term : LR1Term -> LR1Term -> Int
  sem cmpLR1Term other =
  | t -> cmpLR1Term2 (other, t)

  sem eqLR1Term : LR1Term -> LR1Term -> Bool
  sem eqLR1Term other =
  | t -> eqi (cmpLR1Term other t) 0
end

-- <start lr1TableBuilder>
-- (This is a long one...)

let lr1TableBuilder = lam syntaxDef.
  use LR1Base in
  let cmpLR1StateItem = lam lhs. lam rhs.
    let cName = nameCmp lhs.name rhs.name in
    if neqi cName 0 then cName else
    let cTerms = seqCmp cmpLR1Term lhs.terms rhs.terms in
    if neqi cTerms 0 then cTerms else
    let cStackPointer = subi lhs.stackPointer rhs.stackPointer in
    if neqi cStackPointer 0 then cStackPointer else
    let cLookahead = cmpTokenKind lhs.lookahead rhs.lookahead in
    cLookahead
  in

  -- Add entrypoint rule to the end of the syntax definition
  let _entrypoint = nameSym "EntryPoint" in
  let _entrypointRule = {name = _entrypoint, terms = [NonTerminal syntaxDef.entrypoint, Terminal (EOF ())]} in
  let syntaxDef = {syntaxDef with rules = snoc syntaxDef.rules _entrypointRule} in

  let ruleLookup : Map Name [{idx: Int, terms: [LR1Term]}] =
    let res =
      foldl (lam acc. lam rule: LR1Rule.
        match acc with (ruleIdx, accLookup) in
        let ruleItems = mapLookupOrElse (lam. []) rule.name accLookup in
        let ruleItems = snoc ruleItems {idx = ruleIdx, terms = rule.terms} in
        (addi ruleIdx 1, mapInsert rule.name ruleItems accLookup)
      ) (0, (mapEmpty nameCmp)) syntaxDef.rules
    in
    res.1
  in

  -- Compute NULLABLE, FIRST, and FOLLOW
  let nullable: Map LR1Term Bool = mapEmpty cmpLR1Term in
  let first: Map LR1Term (Set Token) = mapEmpty cmpLR1Term in
  let follow: Map LR1Term (Set Token) = mapEmpty cmpLR1Term in
  let computeNFF =
    let allTerminals = map (lam t. Terminal t) (tokenListAll ()) in
    let allNonTerminals = map (lam n. NonTerminal n) (mapKeys ruleLookup) in
    let allTerms = concat allTerminals allNonTerminals in
    -- initialize NULLABLE to false (except for empty and EOF, which by definition is nullable)
    let nullable = foldl (lam nullable. lam term. mapInsert term false nullable) nullable allTerms in
    -- initialize FIRST and FOLLOW to empty sets
    let follow = foldl (lam follow. lam term. mapInsert term (setEmpty cmpTokenKind) follow) follow allTerms in
    let first = foldl (lam first. lam term.
      match term with Terminal t then
        -- Set first property for all terminals
        mapInsert term (setInsert t (setEmpty cmpTokenKind)) first
      else
        mapInsert term (setEmpty cmpTokenKind) first
    ) first allTerms in

    recursive let repeat = lam nullable. lam first. lam follow.
      let res = foldl (lam acc. lam rule: LR1Rule.
        -- for each production X -> Y_1 Y_2 ... Y_k
        match acc with (hasUpdated, nullable, first, follow) in
        let nameTerm = NonTerminal rule.name in
        let k_termIdx = subi (length rule.terms) 1 in
        let allNullable = lam nullable. lam fromIdx. lam toIdx. -- "toIdx" is exclusive
            forAll (lam term. mapLookupOrElse (lam. false) term nullable)
                   (subsequence rule.terms fromIdx (subi toIdx fromIdx))
        in
        -- First check if we are NULLABLE
        let nullableCheck =
          -- if Y_1 ... Y_k are all nullable (or if k = 0)
          --   then nullable[X] <- true
          match mapLookup nameTerm nullable with Some true
            then (hasUpdated, nullable) -- Already marked as nullable, no update here
            else if allNullable nullable 0 (addi k_termIdx 1)
              then (true, mapInsert nameTerm true nullable) -- All terms in rule are nullable, updating!
              else (hasUpdated, nullable)
        in
        match nullableCheck with (hasUpdated, nullable) in
        -- Perform the FIRST and FOLLOW checks
        let firstFollowCheck =
          foldl (lam acc. lam i_termIdx.
            let i_term = get rule.terms i_termIdx in
            match acc with (hasUpdated, first, follow) in
            -- Perform the FIRST update
            let mapSetOPERATION = lam op. lam m. lam k1. lam k2.
              let s1 = mapLookupOrElse (lam. setEmpty cmpTokenKind) k1 m in
              let s2 = mapLookupOrElse (lam. setEmpty cmpTokenKind) k2 m in
              op s1 s2
            in
            let mapSetSubset = lam m. lam k1. lam k2. mapSetOPERATION setSubset m k1 k2 in
            let mapSetUnion = lam m. lam k1. lam k2. mapSetOPERATION (lam s1. lam s2. mapInsert k1 (setUnion s1 s2) m) m k1 k2 in
            let firstCheck =
              -- if Y_1 ... Y_{i-1} are all nullable (or if i = 1)
              --   then FIRST[X] <- FIRST[X] U FIRST[Y_i]
              if mapSetSubset first i_term nameTerm
                then (hasUpdated, first) -- all of FIRST[Y_i] is already in FIRST[X]
                else if allNullable nullable 0 i_termIdx
                  then (true, mapSetUnion first nameTerm i_term) -- added FIRST[Y_i]
                  else (hasUpdated, first)
            in
            match firstCheck with (hasUpdated, first) in
            -- Perform the FOLLOW updates
            foldl (lam acc. lam j_termIdx.
              let j_term = get rule.terms j_termIdx in
              match acc with (hasUpdated, first, follow) in
              let followCheck1 =
                -- if Y_{i+1} ... Y_k are all nullable (or if i = k)
                --   then FOLLOW[Y_i] <- FOLLOW[Y_i] U FOLLOW[X]
                if mapSetSubset follow nameTerm i_term
                  then (hasUpdated, follow) -- all of FOLLOW[X] is already in FOLLOW[Y_i]
                  else if allNullable nullable (addi i_termIdx 1) (addi k_termIdx 1)
                    then (true, mapSetUnion follow i_term nameTerm) -- added FOLLOW[X]
                    else (hasUpdated, follow)
              in
              match followCheck1 with (hasUpdated, follow) in
              let followCheck2 =
                -- if Y_{i+1} ... Y_{j-1} are all nullable (or if i+1 = j)
                --   then FOLLOW[Y_i] <- FOLLOW[Y_i] U FOLLOW[Y_j]
                if mapSetSubset follow j_term i_term
                  then (hasUpdated, follow) -- all of FOLLOW[Y_j] is already in FOLLOW[Y_i]
                  else if allNullable nullable (addi i_termIdx 1) j_termIdx
                    then (true, mapSetUnion follow i_term j_term) -- added FOLLOW[Y_j]
                    else (hasUpdated, follow)
              in
              match followCheck2 with (hasUpdated, follow) in
              (hasUpdated, first, follow)
            ) acc (subsequence (mapi (lam i. lam term. i) rule.terms) (addi i_termIdx 1) (length rule.terms))
          ) (hasUpdated, first, follow) (mapi (lam i. lam term. i) rule.terms)
        in
        match firstFollowCheck with (hasUpdated, first, follow) in
        (hasUpdated, nullable, first, follow)
      ) (false, nullable, first, follow) syntaxDef.rules in
      match res with (hasUpdated, nullable, first, follow) in
      if hasUpdated
        then repeat nullable first follow
        else (nullable, first, follow) -- no more updates, we are done
    in
    repeat nullable first follow
  in
  match computeNFF with (nullable, first, follow) in

  let isNullable = lam term. mapLookupOrElse (lam. false) term nullable in
  let getFirst = lam term. mapLookupOrElse (lam. setEmpty cmpTokenKind) term first in
  let getFollow = lam term. mapLookupOrElse (lam. setEmpty cmpTokenKind) term follow in

  -- Closure(I) =
  --   repeat
  --     for any item (A -> a.Xb, z) in I
  --       for any production X -> y
  --         for any w in FIRST (bz)
  --           I <- I U {(X -> .y, w)}
  --   until I does not change
  --   return I
  let closure = lam inSet: Set LR1StateItem.
    recursive let repeat = lam curSet.
      let res = setFold (lam acc. lam item: LR1StateItem.
        let beyondStackPointer =
          if lti item.stackPointer (length item.terms)
            then subsequence item.terms item.stackPointer (length item.terms)
            else []
        in
        match beyondStackPointer with [NonTerminal x] ++ rest then
          let allFirsts =
            match rest with [bTerm] ++ _ then
              if isNullable bTerm
                then setInsert item.lookahead (getFirst bTerm)
                else getFirst bTerm
            else
              setInsert item.lookahead (setEmpty cmpTokenKind)
          in
          let allRules = mapLookupOrElse (lam. []) x ruleLookup in
          foldl (lam acc. lam rule.
            setFold (lam acc. lam w.
              match acc with (hasUpdated, curSet) in
              let newItem: LR1StateItem = {
                name = x,
                terms = rule.terms,
                stackPointer = 0,
                lookahead = w,
                ruleIdx = rule.idx
              } in
              if setMem newItem curSet
                then acc
                else (true, setInsert newItem curSet)
            ) acc allFirsts
          ) acc allRules
        else
          acc
      ) (false, curSet) curSet in
      match res with (hasUpdated, resSet) in
      if hasUpdated
        then repeat resSet
        else resSet
    in
    repeat inSet
  in

  -- GOTO(I, X) =
  --   J <- {}
  --   for any item (A -> a.Xb, z) in I
  --     add (A -> aX.b, z) to J
  --   return Closure(J)
  let goto = lam inSet. lam x.
    let j = setFold (lam jAcc. lam item: LR1StateItem.
      if lti item.stackPointer (length item.terms) then
        if eqLR1Term x (get item.terms item.stackPointer) then
          let newItem = {item with stackPointer = addi item.stackPointer 1} in
          setInsert newItem jAcc
        else
          jAcc
      else
        jAcc
    ) (setEmpty cmpLR1StateItem) inSet in
    closure j
  in

  -- Initialize T to {Closure(({S' -> .S$}, $))}
  -- Initialize E to empty
  -- repeat
  --  for each state I in T
  --    for each item (A -> a.Xb, z) in I
  --      let J be GOTO(I, X)
  --      T <- T U {J}
  --      E <- E U {I --X-> J}
  -- until E and T did not change in this iteration
  let buildLR1States =
    let _entrypointItem: LR1StateItem = {
      name = _entrypointRule.name,
      terms = _entrypointRule.terms,
      stackPointer = 0,
      lookahead = EOF (),
      ruleIdx = (let x: {idx: Int, terms: [LR1Term]} = head (mapLookupOrElse (lam. error "internal error") _entrypointRule.name ruleLookup) in x).idx
    } in
    -- Initialize T to {Closure(({S' -> .S$}, None))}
    let t: [Set LR1StateItem] = [closure (setInsert _entrypointItem (setEmpty cmpLR1StateItem))] in
    -- Membership helper map to get index from an item
    let tLookup: Map (Set LR1StateItem) Int = foldl (lam m. lam k. mapInsert k 0 m) (mapEmpty setCmp) t in
    -- Initialize E to empty
    --   a transition is a 3-tuple (fromStateIdx in T, term, toStateIdx in T)
    let e: Set (Int, LR1Term, Int) = setEmpty (cmp3tuple subi cmpLR1Term subi) in
    recursive let repeat = lam iIdx. lam t. lam tLookup. lam e.
      if lti iIdx (length t) then
        let iState = get t iIdx in
        let res =
          setFold (lam acc. lam item: LR1StateItem.
            if lti item.stackPointer (length item.terms) then
              match acc with (t, tLookup, e) in
              let xItem = get item.terms item.stackPointer in
              match xItem with (Terminal (EOF ())) then
                -- Generate an accept action here (i.e. transition to state -1)
                let e = setInsert (iIdx, xItem, negi 1) e in
                (t, tLookup, e)
              else
                let j = goto iState xItem in
                let existsCheck =
                  match mapLookup j tLookup with Some jIdx then
                    (jIdx, t, tLookup)
                  else
                    let jIdx = length t in
                    (jIdx, snoc t j, mapInsert j jIdx tLookup)
                in
                match existsCheck with (jIdx, t, tLookup) in
                let e = setInsert (iIdx, xItem, jIdx) e in
                (t, tLookup, e)
            else
              -- Item is _not_ on the form of A -> a.Xb
              acc
          ) (t, tLookup, e) iState
        in
        match res with (t, tLookup, e) in
        repeat (addi iIdx 1) t tLookup e
      else
        -- We've finished iterating
        (t, e)
    in
    repeat 0 t tLookup e
  in

  match buildLR1States with (t, e) in

  -- R <- {}
  -- for each state I in T
  --   for each item (A -> a., z) in I
  --     R <- R U {(I, z, A -> a)}
  let buildReductions =
    let cmpReduction: {stateIdx: Int, lookahead: Token, ruleIdx: Int} -> {stateIdx: Int, lookahead: Token, ruleIdx: Int} -> Int =
      lam lhs. lam rhs.
      cmp3tuple subi cmpTokenKind subi
                (lhs.stateIdx, lhs.lookahead, lhs.ruleIdx)
                (rhs.stateIdx, rhs.lookahead, rhs.ruleIdx)
    in
    let r: Set {stateIdx: Int, lookahead: Token, ruleIdx: Int} = setEmpty cmpReduction in
    foldl (lam r. lam i_idx: Int.
      let iState: Set LR1StateItem = get t i_idx in
      setFold (lam r. lam item: LR1StateItem.
        if eqi item.stackPointer (length item.terms) then
          let newReduction = {
            stateIdx = i_idx,
            lookahead = item.lookahead,
            ruleIdx = item.ruleIdx
          } in
          setInsert newReduction r
        else
          r
      ) r iState
    ) r (mapi (lam i. lam x. i) t)
  in

  let r = buildReductions in

  -- now (t, e, r) is complete

  let parseTable = {
    entrypointIdx = 0,
    _debugStates = t,
    nStates = length t,
    transitions = setFold (lam transitions: Map Int [{term: LR1Term, toIdx: Int}]. lam tup.
      match tup with (fromIdx, term, toIdx) in
      let fromTransitions = mapLookupOrElse (lam. []) fromIdx transitions in
      let fromTransitions = snoc fromTransitions {term = term, toIdx = toIdx} in
      mapInsert fromIdx fromTransitions transitions
    ) (mapEmpty subi) e,
    reductions = setFold (lam reductions: Map Int [{lookahead: Token, ruleIdx: Int}]. lam red.
      let stateReductions = mapLookupOrElse (lam. []) red.stateIdx reductions in
      let stateReductions = snoc stateReductions {lookahead = red.lookahead, ruleIdx = red.ruleIdx} in
      mapInsert red.stateIdx stateReductions reductions
    ) (mapEmpty subi) r
  } in
  -- Return the updated syntax def and the parse table
  (syntaxDef, parseTable)

-- </end lr1TableBuilder>

-- Test Parsing with LR1
let lr1ParseTest =
  use LR1Base in
  lam syntaxDef: LR1SyntaxDef. lam parseTable: LR1ParseTable. lam tokens: [Token].

  -- A nextToken function that returns the next token if it exists, otherwise EOF
  let nextToken: [Token] -> (Token, [Token]) = lam tokens.
    match tokens with [nxt] ++ remaining
    then (nxt, remaining)
    else (EOF (), [])
  in

  type StackObject in
  con SOTerminal : Token -> StackObject in
  con SONonTerminal : {name: Name, ruleIdx: Int, terms: [StackObject]} -> StackObject in
  recursive let so2string = lam so. switch so
    case SOTerminal t then token2string t
    case SONonTerminal d then join [
        nameGetStr d.name, "[", int2string d.ruleIdx, "]<",
        strJoin ", " (map so2string d.terms), ">"
      ]
  end in
  let token2so = lam t. SOTerminal t in

  recursive let work =
    lam stack: [StackObject].
    lam stateTrace: [Int].
    lam lookahead: Token.
    lam tokens: [Token].

    let currentState = head stateTrace in
    -- Debug printing:
    printLn (join ["currentState: ", int2string currentState, ""]);
    printLn (join ["[[ lookahead: ", so2string (token2so lookahead), " ]]"]);
    printLn (join ["[[ stack: [", strJoin ", " (reverse (map so2string stack)), "] ]]"]);

    let matchingReductions =
      let reduceList = mapLookupOrElse (lam. []) currentState parseTable.reductions in
      foldl (lam acc. lam e.
        if eqTokenKind lookahead e.lookahead
          then cons e acc
          else acc
      ) [] reduceList
    in
    let matchingShifts =
      let transitionList = mapLookupOrElse (lam. []) currentState parseTable.transitions in
      foldl (lam acc. lam e.
        match e.term with Terminal t then
          if eqTokenKind lookahead t
            then cons e acc
            else acc
        else acc
      ) [] transitionList
    in
    switch (matchingReductions, matchingShifts)
    case ([reduction], []) then
      printLn (join ["[[ reducing by rule: ", int2string reduction.ruleIdx, " ]]"]);
      let rule: LR1Rule = get syntaxDef.rules reduction.ruleIdx in

      let reduceTerms = reverse (subsequence stack 0 (length rule.terms)) in
      let stack = subsequence stack (length rule.terms) (length stack) in
      let stateTrace = subsequence stateTrace (length rule.terms) (length stateTrace) in
      let reduceResult = SONonTerminal {name = rule.name, ruleIdx = reduction.ruleIdx, terms = reduceTerms} in

      -- Now to shift the generated non-terminal
      let currentState = head stateTrace in
      printLn "[[ shifting produced non-terminal ]]";
      printLn (join ["[[ currentState: ", int2string currentState, "]]"]);
      printLn (join ["[[ reduceResult: ", so2string reduceResult, " ]]"]);
      printLn (join ["[[ stack: [", strJoin ", " (reverse (map so2string stack)), "] ]]"]);
      let matchingShifts =
        let transitionList = mapLookupOrElse (lam. []) currentState parseTable.transitions in
        foldl (lam acc. lam e.
          match e.term with NonTerminal n then
            if nameEq rule.name n
              then cons e acc
              else acc
          else acc
        ) [] transitionList
      in
      switch matchingShifts
      case [shift] then
        let nextState = shift.toIdx in
        let stack = cons reduceResult stack in
        let stateTrace = cons nextState stateTrace in
        -- note: Lookahead and tokens remains untouched
        work stack stateTrace lookahead tokens
      case [s1, s2] ++ _ then
        error "shift-shift conflict"
      case [] then
        error "no action to take"
      end
    case ([], [shift]) then
      let nextState = shift.toIdx in
      if eqi nextState (negi 1) then
        printLn "[[ reached accept condition ]]";
        head stack -- return the only token left on the stack
      else
        printLn (join ["[[ shifting into state: ", int2string nextState, " ]]"]);
        let stack = cons (SOTerminal lookahead) stack in
        let stateTrace = cons nextState stateTrace in
        match nextToken tokens with (lookahead, tokens) in
        work stack stateTrace lookahead tokens
    case ([r1, r2] ++ _, []) then
      error "reduce-reduce conflict"
    case ([], [s1, s2] ++ _) then
      error "shift-shift conflict"
    case ([r1] ++ _, [s1] ++ _) then
      error "shift-reduce conflict"
    case _ then
      error "no action to take"
    end
  in
  match nextToken tokens with (lookahead, tokens) in
  work [] [parseTable.entrypointIdx] lookahead tokens;
  ()

/-
    _debugStates: [Set LR1StateItem],
    nStates: Int,
    transitions: Map Int [{term: LR1Term, toIdx: Int}],
    reductions: Map Int [{lookahead: Token, ruleIdx: Int}]
-/

let printStates = use LR1Base in
  lam t: [Set LR1StateItem].
  foldl (lam i: Int. lam state: Set LR1StateItem.
    printLn (join ["state ", int2string i, ":"]);
    setFold (lam. lam item: LR1StateItem.
      let out = join [
        "  (rule ", int2string item.ruleIdx, ") ",
        nameGetStr item.name, " -> ",
        strJoin " " (map lr1term2string (subsequence item.terms 0 item.stackPointer)),
        " . ",
        strJoin " " (map lr1term2string (subsequence item.terms item.stackPointer (length item.terms)))
      ] in
      let indent = if lti (length out) 60 then make (subi 60 (length out)) ' ' else "" in
      let out = join [out, indent, "<lookahead: ", token2string item.lookahead, " >"] in
      printLn out
    ) () state;
    addi i 1
  ) 0 t; ()

let printTransitions = use LR1Base in
  lam e: Map Int [{term: LR1Term, toIdx: Int}].
  mapFoldWithKey (lam. lam stateIdx: Int. lam transitions: [{term: LR1Term, toIdx: Int}].
    printLn (join ["state ", int2string stateIdx, ":"]);
    foldl (lam. lam trans: {term: LR1Term, toIdx: Int}.
      printLn (join [
        "  ", lr1term2string trans.term, " -> ", int2string trans.toIdx
      ])
    ) () transitions
  ) () e; ()

let printReductions = use LR1Base in
  lam r: Map Int [{lookahead: Token, ruleIdx: Int}].
  mapFoldWithKey (lam. lam stateIdx: Int. lam reductions: [{lookahead: Token, ruleIdx: Int}].
    printLn (join ["state ", int2string stateIdx, ":"]);
    foldl (lam. lam red: {lookahead: Token, ruleIdx: Int}.
      printLn (join [
        "  ", token2string red.lookahead, "  (by rule ", int2string red.ruleIdx, ")"
      ])
    ) () reductions
  ) () r; ()

mexpr

use LR1Base in

-- Syntax definition from LR0 example
let syntaxDef_LR0_example =
  let _S = nameSym "S" in
  let _L = nameSym "L" in
  {
    entrypoint = _S,
    rules = [
      {name = _S, terms = [Terminal (LParen ()), NonTerminal _L, Terminal (RParen ())]},
      {name = _S, terms = [Terminal (StringLiteral "")]},
      {name = _L, terms = [NonTerminal _S]},
      {name = _L, terms = [NonTerminal _L, Terminal (Comma ()), NonTerminal _S]}
    ]
  }
in

let #var"((x),x)": [Token] = [
  LParen (),
    LParen (), StringLiteral "x", RParen (),
    Comma (),
    StringLiteral "x",
  RParen ()
] in

-- Syntax definition from LR1 example
let syntaxDef_LR1_example =
  let _S = nameSym "S" in
  let _E = nameSym "E" in
  let _V = nameSym "V" in
  {
    entrypoint = _S,
    rules = [
      {name = _S, terms = [NonTerminal _V, Terminal (Equality ()), NonTerminal _E]},
      {name = _S, terms = [NonTerminal _E]},
      {name = _E, terms = [NonTerminal _V]},
      {name = _V, terms = [Terminal (StringLiteral "")]},
      {name = _V, terms = [Terminal (Star ()), NonTerminal _E]}
    ]
  }
in

let #var"*s = **a": [Token] = [
  Star (), StringLiteral "s", Equality (), Star (), Star (), StringLiteral "a"
] in


-- Example with empty rule
let syntaxDef_Empty_example =
  let _S = nameSym "S" in
  --let _E = nameSym "E" in
  --let _V = nameSym "V" in
  {
    entrypoint = _S,
    rules = [
      {name = _S, terms = [Terminal (Star ()), NonTerminal _S]},
      {name = _S, terms = []}
    ]
  }
in

let #var"***": [Token] = [
  Star (), Star (), Star ()
] in

-- Example of LR(2) grammar from here: https://stackoverflow.com/questions/62075086/what-is-an-lr2-parser-how-does-it-differ-from-an-lr1-parser
let syntaxDef_LR2_example =
  let _S = nameSym "S" in
  let _R = nameSym "R" in
  let _T = nameSym "T" in
  {
    entrypoint = _S,
    rules = [
      {name = _S, terms = [NonTerminal _R, NonTerminal _S]},
      {name = _S, terms = [NonTerminal _R]},
      {name = _R, terms = [Terminal (Star ()), Terminal (StringLiteral ""), NonTerminal _T]},
      {name = _T, terms = [Terminal (Star ())]},
      {name = _T, terms = [Terminal (Equality ())]},
      {name = _T, terms = []}
    ]
  }
in

let #var"*a*b=": [Token] = [
  Star (), StringLiteral "a", Star (), StringLiteral "b", Equality ()
] in


-- Set the syntax and input tokens to use
-- LR0 Example:
--let syntaxDef = syntaxDef_LR0_example in
--let tokens = #var"((x),x)" in
-- LR1 Example:
let syntaxDef = syntaxDef_LR1_example in
let tokens = #var"*s = **a" in
-- Empty Example:
--let syntaxDef = syntaxDef_Empty_example in
--let tokens = #var"***" in
-- LR2 Example: (This should fail since we are only LR1!)
--let syntaxDef = syntaxDef_LR2_example in
--let tokens = #var"*a*b=" in

let res = lr1TableBuilder syntaxDef in
match res with (syntaxDef, parseTable) in

printLn "\n======= STATES =======";
printStates parseTable._debugStates;
printLn "======================";

printLn "\n======= TRANSITIONS =======";
printTransitions parseTable.transitions;
printLn "===========================";

printLn "\n======= REDUCTIONS =======";
printReductions parseTable.reductions;
printLn "============================";

printLn "\n parsing...";
lr1ParseTest syntaxDef parseTable tokens;

printLn "DONE"
