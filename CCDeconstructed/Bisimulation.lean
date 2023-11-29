import CCDeconstructed.CC

structure State (i : CC) where
  store : Env

class Eval (i : CC) where
  Eval : State i → State i → Prop
