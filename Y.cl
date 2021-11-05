let
  ssk = \x\y.x y x;
  foo = \y\x.y (x y x)
in ssk foo

-- ./blc comb Y.cl
-- now correctly outputs
-- S S K (S (K (S S (S (S S K)))) K)
-- with the added bracket abstraction rules
