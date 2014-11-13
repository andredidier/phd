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

type_synonym 'PortName CInput = 'PortName
type_synonym 'PortName COutput = 'PortName

type_synonym  ('pin, 'pout) Connections = "'pin \<rightharpoonup> 'pout"

type_synonym ('vb, 'FMode, 'pin, 'pout) PortValuation = 
  "'pin \<Rightarrow> ('vb, 'FMode, 'pout) ValuesOperand"

(* outputs -. ValuesOperand*)
type_synonym ('vb, 'FMode, 'pin, 'pout) Component = 
  "'pout \<rightharpoonup> 
  ( ('pin \<Rightarrow> ('vb, 'FMode, 'pin) ValuesOperand) \<Rightarrow> ('vb, 'FMode, 'pin) ValuesOperand)"

definition BasicComponent :: "('vb, 'FMode, nat, nat) Component"
where
  "BasicComponent \<equiv> [ 0 \<mapsto> (\<lambda> m. VBVExpOp [ VB (VBBConstOp True) (m 10)])  ]"
value "(the (BasicComponent 0))
  (\<lambda> x. if x = 10 then VBVConstOp (FMNominal 5) else VBVConstOp (FMNominal 2))"

definition apply_map :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('a \<rightharpoonup> 'c)"
where
  "apply_map m f \<equiv> (\<lambda> x. case (m x) of None \<Rightarrow> None | (Some mx) \<Rightarrow> Some (f mx))"

primrec list_of_maps_to_map :: "('a \<rightharpoonup> 'b) list \<Rightarrow> ('a \<rightharpoonup> 'b)"
where
  "list_of_maps_to_map [] = Map.empty" |
  "list_of_maps_to_map (l # ls) = l ++ (list_of_maps_to_map ls)"

primrec convert_elems :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b list"
where
  "convert_elems [] _ = []" |
  "convert_elems (l # ls) f = (f l) # (convert_elems ls f)"

primrec 
  replace_io_ValuesOperand :: 
    "('vb, 'FMode, 'pn) ValuesOperand \<Rightarrow> 
    ('vb, 'FMode, 'pn, 'pn) PortValuation \<Rightarrow> 
    ('vb, 'FMode, 'pn) ValuesOperand" 
  and 
  replace_io_ValuesOperand_list :: 
    "('vb, 'FMode, 'pn) ValuedBool list \<Rightarrow> 
    ('vb, 'FMode, 'pn, 'pn) PortValuation \<Rightarrow> 
    ('vb, 'FMode, 'pn) ValuedBool list" 
  and 
  replace_io_ValuesOperand_VB :: 
    "('vb, 'FMode, 'pn) ValuedBool \<Rightarrow> 
    ('vb, 'FMode, 'pn, 'pn) PortValuation \<Rightarrow> 
    ('vb, 'FMode, 'pn) ValuedBool" 
where
  "replace_io_ValuesOperand (VBVConstOp c) inputs = (
    case c of
      FMVar vvar \<Rightarrow> 
        let vo = (inputs vvar)
        in (replace_io_ValuesOperand vo inputs)|
      _ \<Rightarrow> (VBVConstOp c)
  )" |
  "replace_io_ValuesOperand (VBVExpOp Es) inputs = 
    VBVExpOp (replace_io_ValuesOperand_list Es inputs)" |
  "replace_io_ValuesOperand_list [] _ = []" |
  "replace_io_ValuesOperand_list (E # Es) inputs = 
    (replace_io_ValuesOperand_VB E inputs) # (replace_io_ValuesOperand_list Es inputs)" |
  "replace_io_ValuesOperand_VB (VB e v) inputs = (VB e (replace_io_ValuesOperand v inputs))"
  

(* Lista de componentes e conexões*)
definition System ::
  "('pin, 'pout) Connections \<Rightarrow> 
  (('vb, 'FMode, 'pin, 'pout) PortValuation \<Rightarrow> 
    ('vb, 'FMode, 'pin, 'pout) Component) list \<Rightarrow> 
    ('vb, 'FMode, 'pin, 'pout) Component"
where
  "System A vCs \<equiv> (
    let outputs = (\<lambda> f. 
      list_of_maps_to_map (convert_elems vCs (\<lambda> vC. vC (\<lambda> m. f m) ))
    ) in
    let input_to_out_exp = (
      \<lambda> inp. let outp = A inp in 
        if outp = None then (VBVConstOp (FMVar inp))
        else (outputs (\<lambda> inp2. outp))
    )  in 
    let nCs = list_of_maps_to_map 
      (convert_elems 
        vCs 
        (\<lambda> C. 
          C (\<lambda> x. let r = input_to_out_exp x in if r = None then VBVConstOp (FMVar x) else the r)
        ) 
      ) in
      (map_comp 
        (\<lambda> x. Some ((*normalise_expand_ValuesOperand*) x)) 
        nCs
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
