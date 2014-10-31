theory FaultModellingTypes
imports Complex_Main

begin

type_synonym 'a binop = "'a \<Rightarrow> 'a \<Rightarrow> 'a" 

datatype FMode = Omission | Commission

datatype Values = 
  FMNominal real 
  | FMFailure FMode 


end
