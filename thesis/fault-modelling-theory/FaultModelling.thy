(*<*)
theory FaultModelling

imports BoolOperand ValuesOperand

begin
(*>*)
(* O Conteúdo deste diretório foi obtido através dos comandos: 
isabelle mkroot -d fault-modelling-theory/ 
e
isabelle build -D fault-modelling-theory/
text {* First test: @{term "VBBVarOp v\<^sub>1"} and @{term "VBBNotOp (VBBVarOp A)"} *}
*)

text {* Input .> Output  *}
type_synonym  'vv Connections = "'vv \<rightharpoonup> 'vv"

type_synonym ('vb, 'vv, 'FMode) Component = "'vv \<rightharpoonup> ('vb, 'vv, 'FMode) ValuesOperand"

definition apply_map :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('a \<rightharpoonup> 'c)"
where
  "apply_map m f \<equiv> (\<lambda> x. Some (f (the (m x))))"

primrec list_of_maps_to_map :: "('a \<rightharpoonup> 'b) list \<Rightarrow> ('a \<rightharpoonup> 'b)"
where
  "list_of_maps_to_map [] = Map.empty" |
  "list_of_maps_to_map (l # ls) = l ++ (list_of_maps_to_map ls)"

(* Lista de componentes e conexões*)
definition System ::
  "'vv Connections \<Rightarrow> ('vb, 'vv, 'FMode) Component list \<Rightarrow> 
    ('vb, 'vv, 'FMode) Component"
where
  "System A Cs \<equiv> (
    let all_cs = list_of_maps_to_map Cs in
    let input_to_out_exp = (map_comp all_cs A) in 
    (map_comp 
      (\<lambda> x. Some (
        normalise_ValuesOperand (
          ValuesOperand_replace_var x input_to_out_exp)
        )
      ) 
      all_cs
    ) 
  )"

(*

definition SystemConnections :: "('vb, 'ComponentPort, 'FMode) System \<Rightarrow> 
  'ComponentPort Connections"
where
  "SystemConnections S \<equiv> snd S"

definition SystemComponentsInputs :: 
  "('vb, 'ComponentPort, 'FMode) System \<Rightarrow> 'ComponentPort set" where
  "SystemComponentsInputs S \<equiv> {  }"

definition SystemComponentsOutputs :: 
  "('vb, 'ComponentPort, 'FMode) System \<Rightarrow> 'ComponentPort set" where
  "SystemComponentsOutputs S \<equiv> { (c,i). c \<in> {..<(length (SystemComponents S))} \<and> i \<in> ComponentOutputPortIndexes (SystemComponent S c)}"

definition ValidConnections :: "('vb, 'FMode) System \<Rightarrow> bool"  where 
  "ValidConnections S \<equiv> 
    (dom (SystemConnections S) \<subseteq> SystemComponentsInputs S \<and>
    ran (SystemConnections S) \<subseteq> SystemComponentsOutputs S)"

definition ValidPortIndex :: "('vb, 'FMode) System \<Rightarrow> ComponentPort \<Rightarrow> (('vb, 'FMode) Component \<Rightarrow> nat) \<Rightarrow> bool" 
where
  "ValidPortIndex S cp f \<equiv> 
    let (c,i) = cp 
    in c < length (SystemComponents S) \<and> i < f (SystemComponent S c)"

(*TODO: cpin pertence às conexões união com os *)
definition ValidComponents :: "('vb, 'FMode) System \<Rightarrow> bool" where
  "ValidComponents S \<equiv> 
    (fst S) \<noteq> [] \<and> 
    (dom (SystemConnections S) \<subseteq> SystemComponentsInputs S) \<and>
    (ran (SystemConnections S) \<subseteq> SystemComponentsOutputs S)"

definition ValidSystem :: "('vb, 'FMode) System \<Rightarrow> bool" 
where 
  "ValidSystem S \<equiv> ValidConnections S \<and> ValidComponents S"

definition SystemInputs :: "('vb, 'FMode) System \<Rightarrow> ComponentPort set" where 
  "SystemInputs S \<equiv> { ii. ii \<in> SystemComponentsInputs S \<and> (ii \<notin> dom (SystemConnections S)) }"

definition SystemOutputs :: "('vb, 'FMode) System \<Rightarrow> ComponentPort set" where
  "SystemOutputs S \<equiv> { oi. oi \<in> SystemComponentsOutputs S \<and> (oi \<notin> ran (SystemConnections S)) }"

lemma SystemInputs_ComponentInputs : "ValidSystem S \<Longrightarrow> SystemInputs S \<subseteq> SystemComponentsInputs S"
using SystemInputs_def SystemComponentsInputs_def ValidSystem_def
apply (auto simp add: SystemInputs_def)
done

lemma SystemOutputs_ComponentOutputs : "ValidSystem S \<Longrightarrow> 
  SystemOutputs S \<subseteq> SystemComponentsOutputs S"
apply (auto simp add: SystemOutputs_def)
done


lemma inputs_completeness1: "
  \<lbrakk> 
    ValidSystem (Cs,A); 
    (m, i) \<in> SystemComponentsInputs (Cs,A);
    (m, i) \<notin> dom A 
  \<rbrakk> \<Longrightarrow> (m, i) \<in> SystemInputs (Cs,A)"
apply (auto simp add: ValidSystem_def ValidConnections_def ValidComponents_def)
apply (auto simp add: SystemComponentsInputs_def SystemInputs_def)
apply (auto simp add: SystemConnections_def)
done

lemma inputs_completeness2: "
  \<lbrakk> 
    ValidSystem (Cs,A); 
    (m, i) \<in> SystemComponentsInputs (Cs,A);
    (m, i) \<notin> SystemInputs (Cs,A) 
  \<rbrakk> \<Longrightarrow> (m, i) \<in> dom A"
apply (auto simp add: ValidSystem_def ValidConnections_def ValidComponents_def)
apply (auto simp add: SystemComponentsInputs_def SystemInputs_def)
apply (auto simp add: SystemConnections_def)
done

lemma inputs_completeness3: "
  \<lbrakk> 
    ValidSystem (Cs,A);
    (m, i) \<in> SystemComponentsInputs (Cs,A) 
  \<rbrakk> \<Longrightarrow> (m, i) \<in> (SystemInputs (Cs,A) \<union> dom A)"
apply (auto simp add: ValidSystem_def ValidConnections_def ValidComponents_def)
apply (auto simp add: SystemComponentsInputs_def SystemInputs_def)
apply (auto simp add: SystemConnections_def)
done

lemma outputs_completeness1: "
  \<lbrakk> 
    ValidSystem (Cs,A);
    (m, oi) \<in> SystemComponentsOutputs (Cs,A);
    (m, oi) \<notin> ran A 
  \<rbrakk> \<Longrightarrow> (m, oi) \<in> SystemOutputs (Cs,A)"
apply (auto simp add: ValidSystem_def ValidConnections_def ValidComponents_def)
apply (auto simp add: SystemComponentsOutputs_def SystemOutputs_def)
apply (auto simp add: ComponentOutputPortIndexes_def NumberOfOutputs_def)
apply (auto simp add: SystemConnections_def)
done

lemma outputs_completeness2: "
  \<lbrakk>
  ValidSystem (Cs,A);
  (m, oi) \<in> SystemComponentsOutputs (Cs,A);
  (m, oi) \<notin> SystemOutputs (Cs,A)
  \<rbrakk> \<Longrightarrow> (m, oi) \<in> ran A"
apply (auto simp add: ValidSystem_def ValidConnections_def ValidComponents_def)
apply (auto simp add: SystemComponentsOutputs_def SystemOutputs_def)
apply (auto simp add: ComponentOutputPortIndexes_def NumberOfOutputs_def)
apply (auto simp add: SystemConnections_def)
done

lemma outputs_completeness3: "
  \<lbrakk> 
    ValidSystem (Cs,A);
    (m, oi) \<in> SystemComponentsOutputs (Cs,A) 
  \<rbrakk> \<Longrightarrow> (m, oi) \<in> (SystemOutputs (Cs,A) \<union> ran A)"
apply (auto simp add: ValidSystem_def ValidConnections_def ValidComponents_def)
apply (auto simp add: SystemComponentsOutputs_def SystemOutputs_def)
apply (auto simp add: ComponentOutputPortIndexes_def NumberOfOutputs_def)
apply (auto simp add: SystemConnections_def)
done

theorem io_completeness: "
  \<lbrakk> 
  ValidSystem (Cs,A); 
  (mi, ini) \<in> SystemComponentsInputs (Cs,A);
  (mo, oi) \<in> SystemComponentsOutputs (Cs,A)
  \<rbrakk> \<Longrightarrow>
  (mi, ini) \<in> (SystemInputs (Cs,A) \<union> dom A) \<and> 
  (mo, oi) \<in> (SystemOutputs (Cs,A) \<union> ran A)"
apply (auto simp add: ValidSystem_def ValidConnections_def ValidComponents_def)
apply (auto simp add: SystemComponentsOutputs_def SystemOutputs_def)
apply (auto simp add: ComponentOutputPortIndexes_def NumberOfOutputs_def)
apply (auto simp add: SystemComponentsInputs_def SystemInputs_def)
apply (auto simp add: SystemConnections_def)
done

*)
end
