theory FaultModellingTypes
imports Complex_Main

begin

datatype FMode = Omission

datatype Values = N real | F FMode

end
