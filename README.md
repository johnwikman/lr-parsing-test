# lr-parsing-test
Testing some LR implementation techniques

# FIRST_k(A)
Here is pseudo-code for how to compute the FIRST_k set for all symbols
```
for all terminals t:
  FIRSK_k(t) = {[t]}
for all nonterminals S:
  FIRST_k(S) = {}

loop until convergence:
  for each production S -> Y_1 Y_2 ... Y_n do:
    if n = 0:
      FIRST_k(S) <- FIRST_k(S) U {[]}  -- empty production
    else if for all Y_i, FIRST_k(Y_i) != ø:
      FIRST_k(S) <- FIRST_k(S) U build_first(k, [Y_1,Y_2,...,Y_n])

function build_first(n, seq):
  if seq = [Y_1]:
    -- take the FIRST_n available
    return {[t_1,...,t_n] | [t_1,t_2,t_3,t_4,...] in FIRST_k(Y_1)}
  else if seq = [Y_1] ++ rest:
    ret <- {}
    for [t_1,..t_i] in FIRST_k(Y_1):
      if i >= n:
        ret <- ret U {[t_1,...,t_n]}
      else:
        for [t_{i+1},...t_j] in build_first(n - i, rest):
          ret <- ret U {[t_1,..t_i,t_{i+1},...t_j]}
    return ret
```

This can also be used to define the nullable property:
```
NULLABLE(S) <- bool([] in FIRST_k(S))
```


