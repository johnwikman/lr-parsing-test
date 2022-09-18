-- LR(0) parser example from the book by Appel 2nd edition, see pages 58-61
-- https://www.cambridge.org/se/academic/subjects/computer-science/programming-languages-and-applied-logic/modern-compiler-implementation-java-2nd-edition?format=HB&isbn=9780521820608

include "char.mc"
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
            let postDot = foldl (lam acc. lam e: LRSymbol.
                    match acc with Some vs then Some (snoc vs e) else
                    match e with StackMarker ()
                    then Some []
                    else acc
                ) (None ()) item
            in
            match postDot with Some([NonTerminal name] ++ _) then
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

let goto : Set LRProduction -> String -> Set LRProduction = lam inSet. lam nontermName.
    -- for all items in I (inSet), with nonterminal X (nontermName)
    let j = setFold (lam jAcc. lam prod.
        -- for the production A -> something (prodname -> item)
        match prod with (prodname, item) in
        let partitionDot = foldl (lam acc. lam e: LRSymbol.
            match acc with (foundDot, preDot, postDot) in
            match e with StackMarker () then
                (true, preDot, postDot)
            else
                if foundDot then
                    (foundDot, preDot, snoc postDot e)
                else
                    (foundDot, snoc preDot e, postDot)
        ) (false, [], []) item in
        match acc with (_, preDot, postDot) in
        match postDot with [NonTerminal name] ++ rest then
            -- if item on the form A -> a.Xb
            if eqString name nontermName then
                -- add new production A -> aX.b
                let newprod: LRProduction = (prodname, join [preDot, [NonTerminal name, StackMarker ()], rest]) in
                setInsert newprod jAcc
            else
                jAcc
        else
            jAcc
    ) emptyClosure inSet in
    closure j

let buildLR0states =
    let t: Set (Set LRProduction) = setEmpty setCmp in
    let t = setInsert (closure (setInsert ("S'", [NonTerminal "S", EOF ()]) emptyClosure)) t in
    -- need to have indexed for the closured probably...
    let e: Set (Int, String, Int) = TODO () in
    ...

