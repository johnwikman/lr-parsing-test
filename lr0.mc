-- LR(0) parser example from the book by Appel 2nd edition, see pages 58-61
-- https://www.cambridge.org/se/academic/subjects/computer-science/programming-languages-and-applied-logic/modern-compiler-implementation-java-2nd-edition?format=HB&isbn=9780521820608

include "char.mc"
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

let cmp3tuple : (a -> a -> Int) -> (b -> b -> Int) -> (c -> c -> Int) -> ((a, b, c) -> (a, b, c) -> Int) =
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

let syntaxLookup : Map String [LRItem] =
    foldl (lam acc. lam e.
        match e with (name, item) in
        let newV = mapFindApplyOrElse (lam v. snoc v item) (lam. [item]) name acc in
        mapInsert name newV acc
    ) (mapEmpty cmpString) syntaxDef

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
                ) accStatus (mapLookupOrElse (lam. []) name syntaxLookup)
            else
                -- No non-terminal after the dot/stackmarker
                accStatus
        ) (false, curSet) inSet in
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
    let t = mapInsert 0 (closure (setInsert ("S'", [NonTerminal "S", EOF ()]) emptyClosure)) t in
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
                    if setMem (i, EOF (), -1) e then
                        acc
                    else
                        let e = setInsert (i, EOF (), -1) in
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
                        if setMem (i, xSymbol, j) then
                            -- edge and j already exists...
                            acc
                        else
                            -- just add the edge
                            let e = setInsert (i, xSymbol, j) in
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