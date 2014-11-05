theory SystemModel
imports FaultModellingTypes

begin

text{* O Conteúdo deste diretório foi obtido através dos comandos: 
isabelle mkroot -d fault-modelling-theory/ 
e
isabelle build -D fault-modelling-theory/
*}

type_synonym ComponentPort = "(nat \<times> nat)"

type_synonym CPValuation = "ComponentPort \<Rightarrow> Values option"

(* Quantidade de entradas e lista de expressões de saída *)
type_synonym 'vb Component = "(nat \<times> ('vb, ComponentPort) ValuesOperand list)"

definition NumberOfInputs :: "'vb Component \<Rightarrow> nat"
where
  "NumberOfInputs C \<equiv> fst C "

definition NumberOfOutputs :: "'vb Component \<Rightarrow> nat"
where
  "NumberOfOutputs C \<equiv> length (snd C)"

text {* Input .> Output  *}
type_synonym 'vv Connections = "'vv \<rightharpoonup> 'vv"

(* Lista de componentes e conexões*)
type_synonym 'vb System = "('vb Component list \<times> ComponentPort Connections)"

definition SystemComponents :: "'vb System \<Rightarrow> 'vb Component list"
where
  "SystemComponents S \<equiv> (fst S)"

definition SystemComponent :: "'vb System \<Rightarrow> nat \<Rightarrow> 'vb Component"
where
  "SystemComponent S i \<equiv> ((SystemComponents S)!i)"

definition SystemConnections :: "'vb System \<Rightarrow> ComponentPort Connections"
where
  "SystemConnections S \<equiv> snd S"

(* Rever se isso faz sentido... *)
definition ValidConnection :: "'vv Connections \<Rightarrow> bool"  where 
  "ValidConnection A \<equiv> \<forall> om oj. \<not> (\<exists> ik. (om \<noteq> oj) \<longrightarrow> (A ik = om \<and> A ik = oj))"

(* [0,n) *)
definition ComponentInputPortIndexes :: "'vb Component \<Rightarrow> nat set"
where
  "ComponentInputPortIndexes C \<equiv> {..<(NumberOfInputs C)} "

definition ComponentOutputPortIndexes :: "'vb Component \<Rightarrow> nat set"
where
  "ComponentOutputPortIndexes C \<equiv> {..<(NumberOfOutputs C)}"

definition SystemComponentsInputs :: "'vb System \<Rightarrow> ComponentPort set" where
  "SystemComponentsInputs S \<equiv> { (c,i). c \<in> {..<(length (SystemComponents S))} \<and> i \<in> ComponentInputPortIndexes (SystemComponent S c)}"

definition SystemComponentsOutputs :: "'vb System \<Rightarrow> ComponentPort set" where
  "SystemComponentsOutputs S \<equiv> { (c,i). c \<in> {..<(length (SystemComponents S))} \<and> i \<in> ComponentOutputPortIndexes (SystemComponent S c)}"

definition ValidPortIndex :: "'vb System \<Rightarrow> ComponentPort \<Rightarrow> ('vb Component \<Rightarrow> nat) \<Rightarrow> bool" 
where
  "ValidPortIndex S cp f \<equiv> 
    let (c,i) = cp 
    in c < length (SystemComponents S) \<and> i < f (SystemComponent S c)"

(*TODO: cpin pertence às conexões união com os *)
definition ValidComponents :: "'vb System \<Rightarrow> bool" where
  "ValidComponents S \<equiv> 
    (fst S) \<noteq> [] \<and> 
    (dom (SystemConnections S) \<subseteq> SystemComponentsInputs S) \<and>
    (ran (SystemConnections S) \<subseteq> SystemComponentsOutputs S)"

definition ValidSystem :: "'vb System \<Rightarrow> bool" 
where 
  "ValidSystem S \<equiv> ValidConnection (SystemConnections S) \<and> ValidComponents S"

definition SystemInputs :: "'vb System \<Rightarrow> ComponentPort set" where 
  "SystemInputs S \<equiv> { ii. ii \<in> SystemComponentsInputs S \<and> \<not> (\<exists> oj.  
    oj \<in> SystemComponentsOutputs S \<and> ((SystemConnections S) ii = Some oj)) }"

definition SystemOutputs :: "'vb System \<Rightarrow> ComponentPort set" where
  "SystemOutputs S \<equiv> { oi. oi \<in> SystemComponentsOutputs S \<and> \<not> (\<exists> ij. ij \<in> SystemComponentsInputs S \<and> 
     ((SystemConnections S) ij = Some oi)) }"

lemma SystemInputs_ComponentInputs : "ValidSystem S \<Longrightarrow> SystemInputs S \<subseteq> SystemComponentsInputs S"
apply (auto simp add: SystemInputs_def)
done

lemma SystemOutputs_ComponentOutputs : "ValidSystem S \<Longrightarrow> SystemOutputs S \<subseteq> SystemComponentsOutputs S"
apply (auto simp add: SystemOutputs_def)
done


lemma inputs_completeness1: "ValidSystem (Cs,A) \<Longrightarrow> (m, i) \<in> SystemComponentsInputs (Cs,A) \<Longrightarrow>
  (m, i) \<notin> dom A \<Longrightarrow> (m, i) \<in> SystemInputs (Cs,A)"
apply (auto simp add: ValidSystem_def ValidConnection_def)
done

lemma inputs_completeness2: "ValidSystem (Cs,A) \<Longrightarrow> (m, i) \<in> SystemComponentsInputs (Cs,A) \<Longrightarrow>
  (m, i) \<notin> SystemInputs (Cs,A) \<Longrightarrow> (m, i) \<in> dom A"
apply (auto simp add: ValidSystem_def ValidConnection_def)
done

lemma inputs_completeness3: "ValidSystem (Cs,A) \<Longrightarrow> (m, i) \<in> SystemComponentsInputs (Cs,A) \<Longrightarrow> 
  (m, i) \<in> (SystemInputs (Cs,A) \<union> dom A)"
apply (auto simp add: ValidSystem_def ValidConnection_def)
done

lemma outputs_completeness1: "ValidSystem (Cs,A) \<Longrightarrow> (m, oi) \<in> SystemComponentsOutputs (Cs,A) \<Longrightarrow>
  (m, oi) \<notin> ran A \<Longrightarrow> (m, oi) \<in> SystemOutputs (Cs,A)"
apply(auto simp add: ValidSystem_def ValidConnection_def)
done

lemma outputs_completeness2: "ValidSystem (Cs,A) \<Longrightarrow> (m, oi) \<in> SystemComponentsOutputs (Cs,A) \<Longrightarrow>
  (m, oi) \<notin> SystemOutputs (Cs,A) \<Longrightarrow> (m, oi) \<in> ran A"
apply(auto simp add: ValidSystem_def ValidConnection_def)
done

lemma outputs_completeness3: "ValidSystem (Cs,A) \<Longrightarrow> (m, oi) \<in> (SystemOutputs (Cs,A) \<union> ran A)"
apply(auto simp add: ValidSystem_def ValidConnection_def)
done

theorem io_completeness: "ValidSystem (Cs,A) \<Longrightarrow> 
  (mi, ini) \<in> SystemComponentsInputs (Cs,A) \<Longrightarrow> (mo, oi) \<in> SystemComponentsOutputs (Cs,A) \<Longrightarrow>
  (mi, ini) \<in> (SystemInputs (Cs,A) \<union> dom A) \<and> 
  (mo, oi) \<in> (SystemOutputs (Cs,A) \<union> ran A)"
apply (auto simp add: ValidSystem_def ValidConnection_def)
done

end
