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

type_synonym PortFunction = "Values list \<Rightarrow> Values"

datatype Port = FreePort Values | FunctionalPort PortFunction

(* Component Index x Port Index within the component *)
type_synonym PortIndex = "(nat \<times> nat)"

type_synonym ComponentPort = "(nat \<times> Port)"

type_synonym Component = "(nat \<times> (ComponentPort set \<times> ComponentPort set))"

definition ComponentInputPortIndexes :: "Component \<Rightarrow> PortIndex set" where
  "ComponentInputPortIndexes C \<equiv> { (c,p). c = fst C \<and> p \<in> Domain (snd (snd C)) }"

definition ComponentOutputPortIndexes :: "Component \<Rightarrow> PortIndex set" where
  "ComponentOutputPortIndexes C \<equiv> { (c,p). c = fst C \<and> p \<in> Domain (fst (snd C)) }"

type_synonym Connections = "(PortIndex \<times> PortIndex) set"

type_synonym System = "(Component set \<times> Connections)"

definition ValidConnection :: "Connections \<Rightarrow> bool"  where 
  "ValidConnection A \<equiv> \<forall> m j om oj ik. \<not> (\<exists> k. ((m, om), (k, ik)) \<in> A \<and> ((j, oj), (k, ik)) \<in> A)"

definition SystemComponentsInputs :: "System \<Rightarrow> PortIndex set" where
  "SystemComponentsInputs S \<equiv> {p. p \<in> (\<Union> C \<in> fst S. ComponentInputPortIndexes C)}"

definition SystemComponentsOutputs :: "System \<Rightarrow> PortIndex set" where
  "SystemComponentsOutputs S \<equiv> {p. p \<in> (\<Union> C \<in> fst S. ComponentOutputPortIndexes C)}"

definition ValidComponents :: "System \<Rightarrow> bool" where
  "ValidComponents S \<equiv> 
    (fst S) \<noteq> Set.empty \<and> 
    Domain (snd S) \<subseteq> {p. p \<in> (\<Union> C \<in> fst S. ComponentOutputPortIndexes C)} \<and>
    Range (snd S) \<subseteq> {p. p \<in> (\<Union> C \<in> fst S. ComponentInputPortIndexes C)} "

definition ValidSystem :: "System \<Rightarrow> bool" where "ValidSystem S \<equiv> ValidConnection (snd S) \<and> ValidComponents S"

definition SystemInputs :: "System \<Rightarrow> PortIndex set" where 
  "SystemInputs S \<equiv> { (m,k). \<not> (\<exists> j oj. 
    (m,k) \<in> SystemComponentsInputs S \<and> 
    ((j,oj),(m,k)) \<in> snd S) }"

definition SystemOutputs :: "System \<Rightarrow> PortIndex set" where
  "SystemOutputs S \<equiv> { (m,k). \<not> (\<exists> j ij. 
    (m,k) \<in> SystemComponentsOutputs S \<and> 
    ((m,k),(j,ij)) \<in> snd S) }"

lemma inputs_completeness: "ValidSystem (Cs,A) \<Longrightarrow> \<forall> m i. (m,i) \<in> (SystemInputs (Cs,A) \<union> Range A)"
apply(auto simp add: ValidSystem_def ValidConnection_def ValidComponents_def 
  ComponentOutputPortIndexes_def ComponentInputPortIndexes_def SystemInputs_def
  SystemComponentsInputs_def SystemComponentsOutputs_def)
done

lemma outputs_completeness: "ValidSystem (Cs,A) \<Longrightarrow> \<forall> m i. (m,i) \<in> (SystemOutputs (Cs,A) \<union> Domain A)"
apply(auto simp add: ValidSystem_def ValidConnection_def ValidComponents_def 
  ComponentOutputPortIndexes_def ComponentInputPortIndexes_def SystemOutputs_def
  SystemComponentsInputs_def SystemComponentsOutputs_def)
done

end
