-- LR(k >= 1) Basic definitions

lang LRKTokens
  syn Token =
  | EOF ()

  sem token2string : Token -> String
  sem token2string =
  | EOF _ -> "EOF"

  sem tokenId : Token -> Int
  sem tokenId =
  | EOF _ -> negi 100

  sem cmpToken : Token -> Token -> Int
  sem cmpToken other =
  | t -> subi (tokenId other) (tokenId t)

  sem eqToken : Token -> Token -> Bool
  sem eqToken other =
  | t -> eqi (tokenId other) (tokenId t)
end

lang LRKBase = LRKTokens
  syn LRKTerm =
  | Terminal Token
  | NonTerminal Name

  type LRKRule = {
    name: Name,
    terms: [LRKTerm]
  }

  type LRKSyntaxDef = {
    entrypoint: Name,
    rules: [LRKRule]
  }

  type LRKStateItem = {
    name: Name,
    terms: [LRKTerm],
    stackPointer: Int,
    lookahead: [Token],
    ruleIdx: Int -- index of the rule that this item originates from
  }

  type LRKParseTable = {
    k_lookahead: Int,
    entrypointIdx: Int,
    _debugStates: [Set LRKStateItem],
    nStates: Int,
    syntaxDef: LRKSyntaxDef,
    transitions: Map Int [{term: LRKTerm, toIdx: Int}],
    reductions: Map Int [{lookahead: [Token], ruleIdx: Int}]
  }

  sem lrkterm2string : LRKTerm -> String
  sem lrkterm2string =
  | Terminal t -> join (["Term(", token2string t, ")"])
  | NonTerminal n -> join (["NonTerminal(", nameGetStr n, ")"])

  sem cmpLRKTerm2 : (LRKTerm, LRKTerm) -> Int
  sem cmpLRKTerm2 =
  | (Terminal t1, Terminal t2) -> cmpToken t1 t2
  | (NonTerminal n1, NonTerminal n2) -> nameCmp n1 n2
  | (Terminal _, NonTerminal _) -> negi 1
  | (NonTerminal _, Terminal _) -> 1

  sem cmpLRKTerm : LRKTerm -> LRKTerm -> Int
  sem cmpLRKTerm other =
  | t -> cmpLRKTerm2 (other, t)

  sem eqLRKTerm : LRKTerm -> LRKTerm -> Bool
  sem eqLRKTerm other =
  | t -> eqi (cmpLRKTerm2 (other, t)) 0

  sem computeFirstK : Int -> LRKSyntaxDef -> Map Name (Set [Token])
  sem computeFirstK k =
  | syntaxDef ->
    let nullable: Set Name = setEmpty nameCmp in
    let firstK: Map Name (Set [Token]) = mapEmpty nameCmp in
    let isNullable = lam nullable. lam term. switch term
      case Terminal _ then false
      case NonTerminal n then setMem n nullable
    end in
    let getFirstK = lam firstK. lam term. switch term
      case Terminal t then setInsert [t] (setEmpty (seqCmp cmpToken))
      case NonTerminal n then
        mapLookupOrElse (lam. setEmpty (seqCmp cmpToken)) n firstK
    end in
    -- Need to think a bit here... how to extend the FIRST_1[X] to FIRST_k[X]
    -- in a neat way...?
    TODO ()
end
