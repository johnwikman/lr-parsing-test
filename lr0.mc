-- LR(0) parser example from the book by Appel 2nd edition, see pages 58-61
-- https://www.cambridge.org/se/academic/subjects/computer-science/programming-languages-and-applied-logic/modern-compiler-implementation-java-2nd-edition?format=HB&isbn=9780521820608

include "char.mc"
include "common.mc"
include "option.mc"
include "seq.mc"
include "set.mc"
include "string.mc"

type LRSymbol
con Terminal : Char -> LRSymbol
con NonTerminal : String -> LRSymbol
con StackMarker : () -> LRSymbol
con EOF : () -> LRSymbol

type LRItem = [LRSymbol]

type LRProduction = (String, LRItem)

let showLRSymbol = lam x. switch x
    case Terminal c then join ["Terminal(\'", [c], "\')"]
    case NonTerminal s then join ["NonTerminal(\"", s, "\")"]
    case StackMarker _ then join ["STACK"]
    case EOF _ then join ["EOF"]
    end
let showLRItem = lam x. join ["LRItem[", strJoin ", " (map showLRSymbol x), "]"]
let showLRProduction = lam x. join ["LRProduction(", x.0, ", ", showLRItem x.1, ")"]

let cmpLRSymbol : LRSymbol -> LRSymbol -> Int = lam lhs. lam rhs.
    let weight : LRSymbol -> Int = lam s.
        switch s
        case Terminal _ then 0
        case NonTerminal _ then 1
        case StackMarker _ then 2
        case EOF _ then 3
        end
    in
    switch (lhs, rhs)
    case (Terminal a, Terminal b) then cmpChar a b
    case (NonTerminal a, NonTerminal b) then cmpString a b
    case (StackMarker _, StackMarker _) then 0
    case (EOF _, EOF _) then 0
    case _ then subi (weight lhs) (weight rhs)
    end

let cmpLRItem : LRItem -> LRItem -> Int = seqCmp cmpLRSymbol

let cmpLRProduction : LRProduction -> LRProduction -> Int = lam lhs. lam rhs.
    match (lhs, rhs) with ((lname, litems), (rname, ritems)) in
    let nameres = cmpString lname rname in
    if neqi nameres 0
    then nameres
    else cmpLRItem litems ritems

let cmp3tuple : all a. all b. all c. (a -> a -> Int) -> (b -> b -> Int) -> (c -> c -> Int) -> ((a, b, c) -> (a, b, c) -> Int) =
    lam cmpa. lam cmpb. lam cmpc. (lam x. lam y.
        let ra = cmpa x.0 y.0 in
        if neqi ra 0 then ra else --continue
        let rb = cmpb x.1 y.1 in
        if neqi rb 0 then rb else --continue
        cmpc x.2 y.2
    )

-- partitions the item at the instance of the first dot
let partitionDot : LRItem -> (Bool, LRItem, LRItem) = lam item.
    foldl (lam acc. lam e: LRSymbol.
        match acc with (foundDot, preDot, postDot) in
        match e with StackMarker () then
            (true, preDot, postDot)
        else
            if foundDot then
                (foundDot, preDot, snoc postDot e)
            else
                (foundDot, snoc preDot e, postDot)
    ) (false, [], []) item



let syntaxDef: [LRProduction] = [
    ("S'", [NonTerminal "S", EOF ()]),
    ("S",  [Terminal '(', NonTerminal "L", Terminal ')']),
    ("S",  [Terminal 'x']),
    ("L",  [NonTerminal "S"]),
    ("L",  [NonTerminal "L", Terminal ',', NonTerminal "S"])
]

--let syntaxLookup : Map String [LRItem] =
--    foldl (lam acc. lam e.
--        match e with (name, item) in
--        let newV = mapFindApplyOrElse (lam v. snoc v item) (lam. [item]) name acc in
--        mapInsert name newV acc
--    ) (mapEmpty cmpString) syntaxDef

let syntaxLookup : String -> [LRItem] = lam k.
    foldl (lam acc. lam e.
        match e with (name, items) in
        if eqString k name
          then snoc acc items
          else acc
    ) [] syntaxDef


let emptyClosure : Set LRProduction = setEmpty cmpLRProduction

let closure: Set LRProduction -> Set LRProduction = lam inSet.
    recursive let work = lam curSet.
        let res = setFold (lam accStatus. lam prod.
            -- Here check the syntax lookup for any productions that we can find
            match prod with (_, item) in
            -- Find the position of the StackMarker in the item, there has to be at least one...
            match partitionDot item with (true, _, [NonTerminal name] ++ _) then
                -- Do something with the non-terminal that came after the dot
                foldl (lam acc. lam items.
                    match acc with (_, accSet) in
                    let newprod: LRProduction = (name, cons (StackMarker ()) items) in
                    if setMem newprod accSet then
                        acc
                    else
                        (true, setInsert newprod accSet)
                ) accStatus (syntaxLookup name)
            else
                -- No non-terminal after the dot/stackmarker
                accStatus
        ) (false, curSet) curSet in
        match res with (hasUpdated, accSet) in
        if hasUpdated then
            work accSet
        else
            accSet
    in
    work inSet
    -- OPTIMIZATION NOTES:
    --  1. Only need to iterate over each item once. What each item A -> a.Xb
    --     will produce will not change depend on whatelse is added to I
    --  2. We do not need to look for a production X more than once. Should
    --     have a linear complexity O(|I| + |Syntax|)

let goto : Set LRProduction -> LRSymbol -> Set LRProduction = lam inSet. lam x.
    -- for all items in I (inSet), with symbol/token X
    let j = setFold (lam jAcc. lam prod.
        -- for the production A -> something (prodname -> item)
        match prod with (prodname, item) in
        match partitionDot item with (_, preDot, postDot) in
        match postDot with [xCheck] ++ rest then
            -- if item on the form A -> a.Xb
            if eqi (cmpLRSymbol x xCheck) 0 then
                -- add new production A -> aX.b
                let newprod: LRProduction = (prodname, join [preDot, [xCheck, StackMarker ()], rest]) in
                setInsert newprod jAcc
            else
                jAcc
        else
            jAcc
    ) emptyClosure inSet in
    closure j

let buildLR0states : (Map Int (Set LRProduction), Set (Int, LRSymbol, Int)) =
    let t: Map Int (Set LRProduction) = mapEmpty subi in
    let t = mapInsert 0 (closure (setInsert ("S'", [StackMarker (), NonTerminal "S", EOF ()]) emptyClosure)) t in
    -- need to have indexed for the closured probably...
    let e: Set (Int, LRSymbol, Int) = setEmpty (cmp3tuple subi cmpLRSymbol subi) in
    recursive let work = lam nextIdx. lam t. lam e.
        -- for each state I in T
        --   for each item A -> a.Xb in I
        --     let J be Goto(I, X) if X != '$'
        --     T <- T u {J}
        --     E <- E u {I -X-> J}
        --     if X = '$' then produce an accept (accept is the -1 state)
        let res = foldl (lam acc. lam entry: (Int, Set LRProduction).
            match entry with (i, iProds) in
            setFold (lam acc. lam prod.
                match acc with (hasUpdated, nextIdx, t, e) in
                match prod with (prodName, item) in
                -- find index of next dot in the production
                match partitionDot item with (foundDot, preDot, postDot) in
                match postDot with [EOF ()] ++ _ then
                    -- End of file after dot, generate an accept edge (goto -1)
                    if setMem (i, EOF (), negi 1) e then
                        acc
                    else
                        let e = setInsert (i, EOF (), negi 1) e in
                        (true, nextIdx, t, e)
                else match postDot with [xSymbol] ++ _ then
                    -- If there exists a token after the dot...
                    let jClosure = goto iProds xSymbol in
                    -- Check also if this is a new state or if we have rediscovered an existing state
                    let jIdx = mapFoldWithKey (lam acc. lam k. lam v.
                        match acc with Some _ then acc else
                        if setEq jClosure v then Some k else acc
                    ) (None ()) t in
                    match jIdx with Some j then
                        -- This rule already exists, check if edge exists!
                        if setMem (i, xSymbol, j) e then
                            -- edge and j already exists...
                            acc
                        else
                            -- just add the edge
                            let e = setInsert (i, xSymbol, j) e in
                            (true, nextIdx, t, e)
                    else
                        -- This does not exist, allocate new index and edge
                        let j = nextIdx in
                        let nextIdx = addi nextIdx 1 in
                        let t = mapInsert j jClosure t in
                        let e = setInsert (i, xSymbol, j) e in
                        (true, nextIdx, t, e)
                else
                    -- No token after the dot...
                    acc
            ) acc iProds
        ) (false, nextIdx, t, e) (mapBindings t) in
        match res with (hasUpdated, nextIdx, t, e) in
        if hasUpdated then
            work nextIdx t e
        else
            (t, e)
    in
    work 1 t e
    -- Optimization NOTES:
    -- We do not need to iterate over each I in T more than once.
    -- About LR(k), for simplicity, maybe the LR(k)
    -- May also be able to generate the necessary reduce actions here as well...


let buildReduceActions: (Map Int (Set LRProduction), Set (Int, LRSymbol, Int), Set (Int, LRProduction, Int)) =
    -- R <- {}
    -- for each state I in T
    --   for each item A -> a. in I
    --     R <- R u {(I, A -> a)}
    let rInit: Set (Int, LRProduction, Int) = setEmpty (cmp3tuple subi cmpLRProduction subi) in
    match buildLR0states with (t, e) in
    let r =
        -- for each state I in T
        foldl (lam r. lam i_entry: (Int, Set LRProduction).
            match i_entry with (i_idx, i_prods) in
            -- for each item A -> a. in I
            setFold (lam r. lam a_entry: LRProduction.
                match a_entry with (name, item) in
                match partitionDot item with (true, items, []) then
                    -- R <- R u {(I, A -> a)}
                    let matchingRules =
                        foldl (lam acc. lam rule.
                            match acc with (ruleIdx, prev) in
                            if and (eqString rule.0 name) (eqi (cmpLRItem rule.1 items) 0) then
                                (addi ruleIdx 1, snoc prev ruleIdx)
                            else
                                (addi ruleIdx 1, prev)
                        ) (0, []) syntaxDef
                    in
                    match matchingRules with (_, [ruleIdx]) then
                        setInsert (i_idx, a_entry, ruleIdx) r
                    else match matchingRules with (_, []) then
                        error "No matching rule for reduce... Impossible?"
                    else
                        error "No reduce reduce conflict..."
                else
                    r -- does not match the A -> a. format
            ) r i_prods
        ) rInit (mapBindings t)
    in
    (t, e, r)


-- Test parsing a string
let parseTest: String -> () = lam s.
    match buildReduceActions with (t, e, r) in
    type StackObject in
    con SOTerminal : Char -> StackObject in
    con SONonTerminal : (String, Int, [StackObject]) -> StackObject in
    con SOEOF : () -> StackObject in
    recursive let so2string = lam so. switch so
      case SOTerminal c then ['\'', c, '\'']
      case SOEOF () then "EOF"
      case SONonTerminal (name, ruleIdx, subObjs) then join [
          name, "[", int2string ruleIdx, "]<",
          strJoin ", " (map so2string subObjs), ">"
        ]
    end in
    let token2so = lam t. switch t case Terminal c then SOTerminal c case EOF () then SOEOF () case _ then error "Invalid token" end in
    let tokenStream: [LRSymbol] = snoc (map (lam c. Terminal c) s) (EOF ()) in
    recursive let work = lam stack: [StackObject]. lam stateTrace: [Int]. lam currentToken: LRSymbol. lam tokenStream: [LRSymbol].
        let currentState = head stateTrace in
        -- Debug printing:
        printLn (join ["currentState: ", int2string currentState, ""]);
        printLn (join ["[[ currentToken: ", so2string (token2so currentToken), " ]]"]);
        printLn (join ["[[ stack: [", strJoin ", " (reverse (map so2string stack)), "] ]]"]);
        -- Check if current state is a reduce state
        let reductions = setFold (lam acc. lam r_entry.
            if eqi currentState r_entry.0
              then cons r_entry acc
              else acc
        ) [] r in
        let shifts = setFold (lam acc. lam e_entry.
            match (currentToken, e_entry.1) with (Terminal c1, Terminal c2) then
                if and (eqi currentState e_entry.0) (eqChar c1 c2)
                  then cons e_entry acc
                  else acc
            else
                acc
        ) [] e in
        let accepts = setFold (lam acc. lam e_entry.
            match (currentToken, e_entry.1) with (EOF (), EOF ()) then
                if eqi currentState e_entry.0
                  then cons e_entry acc
                  else acc
            else
                acc
        ) [] e in
        let totalActions = foldl addi 0 [length reductions, length shifts, length accepts] in
        --if eqi totalActions 0 then
        --    error (join ["No action to take in state ", int2string state])
        --else
        if gti totalActions 1 then
            error (join ["Conflicting actions to take in state ", int2string currentState])
        else --continue
        match reductions with [r_entry] then
          let rule = get syntaxDef r_entry.2 in
          printLn (join ["[[ reducing by rule: ", int2string r_entry.2, " ]]"]);
          match rule with (rulename, symbollist) in
          --let stack = cons currentToken stack in
          let ntTokens = reverse (subsequence stack 0 (length symbollist)) in
          let stack = subsequence stack (length symbollist) (length stack) in
          let stateTrace = subsequence stateTrace (length symbollist) (length stateTrace) in
          let reducedNT = SONonTerminal (rulename, r_entry.2, ntTokens) in
          let currentState = head stateTrace in
          -- Now to find the appropriate goto's
          printLn "  [[ GOTO operation ]]";
          printLn (join ["     currentState: ", int2string currentState]);
          printLn (join ["     [[ reducedNT: ", so2string reducedNT, " ]]"]);
          printLn (join ["     [[ stack: [", strJoin ", " (reverse (map so2string stack)), "] ]]"]);
          let gotos = setFold (lam acc. lam e_entry.
              match (reducedNT, e_entry.1) with (SONonTerminal x1, NonTerminal s2) then
                  if and (eqi currentState e_entry.0) (eqString x1.0 s2)
                    then cons e_entry acc
                    else acc
              else
                  acc
          ) [] e in
          match gotos with [e_entry] then
            let nextState = e_entry.2 in
            let stack = cons reducedNT stack in
            let stateTrace = cons nextState stateTrace in
            work stack stateTrace currentToken tokenStream
          else match gotos with [] then
            error (join ["Could not find a matching goto in state ", int2string currentState])
          else
            error (join ["Conflicting gotos in state ", int2string currentState])
        else match shifts with [e_entry] then
          let nextState = e_entry.2 in
          printLn (join ["[[ shifting into state: ", int2string nextState, " ]]"]);
          let stack = cons (token2so currentToken) stack in
          let stateTrace = cons nextState stateTrace in
          let currentToken = head tokenStream in
          let tokenStream = tail tokenStream in
          work stack stateTrace currentToken tokenStream
        else match accepts with [e_entry] then
          if neqi (length stack) 1 then
            error "Expected a stack of length 1"
          else if neqi (length tokenStream) 0 then
            error "Expected only to have the EOF token left!"
          else
            head stack
        else
          error (join ["No action to take in state ", int2string currentState])
    in
    let result = work [] [0] (head tokenStream) (tail tokenStream) in
    printLn "DONE"


/-
-- Sketch for interface against the tool
lang LRParserTokens
    syn LRToken =
    | EOF ()
    | LParen ()
    | RParen ()
    | Comma ()
    | StringLiteral String
    | NonTerminal Name

    syn LRProduction =
    | StringName String
    | Parenthesis ([LRProduction])

    sem eqToken =
    | (EOF (), EOF ()) -> true
    | (LParen (), LParen ()) -> true
    | (RParen (), RParen ()) -> true
    | (Comma (), Comma ()) -> true
    | (StringLiteral a, StringLiteral b) -> eqString a b
    | (NonTerminal a, NonTerminal b) -> eqName a b
    | _ -> false

    -- A map over all the productions
    type LRGrammar = Map Name ([LRToken], LRProduction)

    -- first argument is the lookahead, then the grammar
    sem parse : Int -> LRGrammar -> LRProduction

    -- how would the return here look? An MCore ast?
    sem generateParser : Int -> LRGrammar -> ParserAST?
end
-/

mexpr
print "TODO\n";
match buildReduceActions with (t, e, r) in

let showSet: all a. (Int -> a -> String) -> Int -> Set a -> String = lam showfunc. lam indent. lam s.
    let newline = cons '\n' (make (addi indent 4) ' ') in
    let final_newline = cons '\n' (make indent ' ') in
    let parts = map (showfunc (addi indent 4)) (mapKeys s) in
    join ["{", newline, strJoin (cons ',' newline) parts, final_newline, "}"]
in
let showSeq: all a. (Int -> a -> String) -> Int -> [a] -> String = lam showfunc. lam indent. lam s.
    let newline = cons '\n' (make (addi indent 4) ' ') in
    let final_newline = cons '\n' (make indent ' ') in
    let parts = map (showfunc (addi indent 4)) s in
    join ["[", newline, strJoin (cons ',' newline) parts, final_newline, "]"]
in
let showMap: all k. all v. (Int -> k -> String) -> (Int -> v -> String) -> Int -> Map k v -> String = lam show_k. lam show_v. lam indent. lam m.
    let newline = cons '\n' (make (addi indent 4) ' ') in
    let final_newline = cons '\n' (make indent ' ') in
    let parts = map (lam kv. 
        match kv with (mk, mv) in
        join [show_k (addi indent 4) mk, ": ", show_v (addi indent 4) mv]
    ) (mapBindings m) in
    join ["{", newline, strJoin (cons ',' newline) parts, final_newline, "}"]
in
let show3tuple: all a. all b. all c. (Int -> a -> String) -> (Int -> b -> String) -> (Int -> c -> String) -> Int -> (a,b,c) -> String =
    lam show_a. lam show_b. lam show_c. lam indent. lam tup.
    let newline = cons '\n' (make (addi indent 4) ' ') in
    let final_newline = cons '\n' (make indent ' ') in
    join ["(", newline,
          show_a (addi indent 4) tup.0, cons ',' newline,
          show_b (addi indent 4) tup.1, cons ',' newline,
          show_c (addi indent 4) tup.2, final_newline,
          ")"]
in
let showLRSymbol = lam indent. lam x. showLRSymbol x in
let showLRItem = lam indent. lam x. showLRItem x in
let showLRProduction = lam indent. lam x. showLRProduction x in
let showInt = lam indent. lam i. int2string i in

let showT = showMap showInt (showSet showLRProduction) 0 in
let showE = showSet (show3tuple showInt showLRSymbol showInt) 0 in
let showR = showSet (show3tuple showInt showLRProduction showInt) 0 in

print "syntax: ";
printLn (showSeq showLRProduction 0 syntaxDef);
print "states (T): ";
printLn (showT t);
print "transitions (E): ";
printLn (showE e);
print "reductions (R): ";
printLn (showR r);

printLn "parsing ((x),x):";
parseTest "((x),x)";

()
