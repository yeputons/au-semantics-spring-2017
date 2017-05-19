data SecdCommand =
    S_Access Int
  | S_Apply
  | S_Return
  | S_Closure Int
  | S_End

type SecdState = (Context Int, Context Int)
type SecdProg = [SecdCommand]

--computeSecd :: [SecdCommand] -> SecdState -> 
