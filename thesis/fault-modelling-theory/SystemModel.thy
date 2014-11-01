theory SystemModel
imports FaultModellingTypes

begin

text{* O Conteúdo deste diretório foi obtido através dos comandos: 
isabelle mkroot -d fault-modelling-theory/ 
e
isabelle build -D fault-modelling-theory/
*}

type_synonym ('vb, 'vv) Port = "('vb, 'vv) ValuedBoolExp"

(* Component Index x Port Index within the component *)
type_synonym PortIndex = "(nat \<times> nat)"

type_synonym ('vb, 'vv) ComponentPort = "(nat \<times> ('vb, 'vv) Port)"

type_synonym ('vb, 'vv) Component = "(nat \<times> (('vb, 'vv) ComponentPort set \<times> ('vb, 'vv) ComponentPort set))"

definition ComponentInputPortIndexes :: "('vb, 'vv) Component \<Rightarrow> PortIndex set" where
  "ComponentInputPortIndexes C \<equiv> { (c,p). c = fst C \<and> p \<in> Domain (snd (snd C)) }"

definition ComponentOutputPortIndexes :: "('vb, 'vv) Component \<Rightarrow> PortIndex set" where
  "ComponentOutputPortIndexes C \<equiv> { (c,p). c = fst C \<and> p \<in> Domain (fst (snd C)) }"

type_synonym Connections = "(PortIndex \<times> PortIndex) set"

type_synonym ('vb, 'vv) System = "(('vb, 'vv) Component set \<times> Connections)"

definition ValidConnection :: "Connections \<Rightarrow> bool"  where 
  "ValidConnection A \<equiv> \<forall> m j om oj ik. \<not> (\<exists> k. ((m, om), (k, ik)) \<in> A \<and> ((j, oj), (k, ik)) \<in> A)"

definition SystemComponentsInputs :: "('vb, 'vv) System \<Rightarrow> PortIndex set" where
  "SystemComponentsInputs S \<equiv> {p. p \<in> (\<Union> C \<in> fst S. ComponentInputPortIndexes C)}"

definition SystemComponentsOutputs :: "('vb, 'vv) System \<Rightarrow> PortIndex set" where
  "SystemComponentsOutputs S \<equiv> {p. p \<in> (\<Union> C \<in> fst S. ComponentOutputPortIndexes C)}"

definition ValidComponents :: "('vb, 'vv) System \<Rightarrow> bool" where
  "ValidComponents S \<equiv> 
    (fst S) \<noteq> Set.empty \<and> 
    Domain (snd S) \<subseteq> {p. p \<in> (\<Union> C \<in> fst S. ComponentOutputPortIndexes C)} \<and>
    Range (snd S) \<subseteq> {p. p \<in> (\<Union> C \<in> fst S. ComponentInputPortIndexes C)} "

definition ValidSystem :: "('vb, 'vv) System \<Rightarrow> bool" where "ValidSystem S \<equiv> ValidConnection (snd S) \<and> ValidComponents S"

definition SystemInputs :: "('vb, 'vv) System \<Rightarrow> PortIndex set" where 
  "SystemInputs S \<equiv> { (m,k). \<not> (\<exists> j oj. 
    (m,k) \<in> SystemComponentsInputs S \<and> 
    ((j,oj),(m,k)) \<in> snd S) }"

definition SystemOutputs :: "('vb, 'vv) System \<Rightarrow> PortIndex set" where
  "SystemOutputs S \<equiv> { (m,k). \<not> (\<exists> j ij. 
    (m,k) \<in> SystemComponentsOutputs S \<and> 
    ((m,k),(j,ij)) \<in> snd S) }"

lemma inputs_completeness1: "ValidSystem (Cs,A) \<Longrightarrow> 
  (m,in_index) \<notin> Range A \<Longrightarrow> (m,in_index) \<in> SystemInputs (Cs,A)"
apply(auto simp add: ValidSystem_def ValidConnection_def ValidComponents_def 
  ComponentOutputPortIndexes_def ComponentInputPortIndexes_def SystemInputs_def
  SystemComponentsInputs_def SystemComponentsOutputs_def)
done

lemma inputs_completeness2: "ValidSystem (Cs,A) \<Longrightarrow> (m,in_index) \<in> (SystemInputs (Cs,A) \<union> Range A)"
apply(auto simp add: inputs_completeness1)
done

lemma outputs_completeness1: "ValidSystem (Cs,A) \<Longrightarrow> 
  (m,out_index) \<notin> Domain A \<Longrightarrow> (m,out_index) \<in> SystemOutputs (Cs,A)"
apply(auto simp add: ValidSystem_def ValidConnection_def ValidComponents_def 
  ComponentOutputPortIndexes_def ComponentInputPortIndexes_def SystemOutputs_def
  SystemComponentsInputs_def SystemComponentsOutputs_def)
done

lemma outputs_completeness2: "ValidSystem (Cs,A) \<Longrightarrow> (m,out_index) \<in> (SystemOutputs (Cs,A) \<union> Domain A)"
apply(auto simp add: outputs_completeness1)
done

theorem io_completeness: "ValidSystem (Cs,A) \<Longrightarrow> 
  (\<forall> m in_index. (m,in_index) \<in> (SystemInputs (Cs,A) \<union> Range A)) \<and> 
  (\<forall> m out_index. (m,out_index) \<in> (SystemOutputs (Cs,A) \<union> Domain A))"
apply (auto simp add: inputs_completeness1 outputs_completeness1)
done

end
