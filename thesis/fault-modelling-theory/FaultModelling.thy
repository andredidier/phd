theory FaultModelling
imports Complex_Main

begin

text{* O Conteúdo deste diretório foi obtido através dos comandos: 
isabelle mkroot -d fault-modelling-theory/ 
e
isabelle build -D fault-modelling-theory/
*}



datatype FMode = Omission

datatype Values = N real | F FMode

end
