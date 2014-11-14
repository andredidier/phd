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

type_synonym ('vb, 'FMode, 'pin) PortValuation = 
  "'pin \<Rightarrow> ('vb, 'FMode, 'pin) ValuesOperand"

(* outputs -. ValuesOperand*)
type_synonym ('vb, 'FMode, 'pin, 'pout) Component = 
  "('vb, 'FMode, 'pin) PortValuation \<Rightarrow> ('pout \<rightharpoonup> ('vb, 'FMode, 'pin) ValuesOperand)"

primrec list_of_maps_to_map :: "('a \<rightharpoonup> 'b) list \<Rightarrow> ('a \<rightharpoonup> 'b)"
where
  "list_of_maps_to_map [] = Map.empty" |
  "list_of_maps_to_map (l # ls) = l ++ (list_of_maps_to_map ls)"

primrec convert_elems :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b list"
where
  "convert_elems [] _ = []" |
  "convert_elems (l # ls) f = (f l) # (convert_elems ls f)"

definition SystemComponents :: "
  (('vb, 'FMode, 'pin, 'pout) Component) list \<Rightarrow> ('vb, 'FMode, 'pin, 'pout) Component"
where
  "SystemComponents cs \<equiv> \<lambda> pv. fold (\<lambda> c1 c2. (c1 pv) ++ c2) cs Map.empty"

definition SystemPortValuation :: "
  ('pin, 'pout) Connections \<Rightarrow> 
  ('vb, 'FMode, 'pin, 'pout) Component \<Rightarrow> 
  ('vb, 'FMode, 'pin) PortValuation
  "
where
  "SystemPortValuation A c \<equiv> 
  (
    \<lambda> pin.
    (
      case (A pin) of
        None \<Rightarrow> VBVConstOp (FMVar pin) |
        (Some pout) \<Rightarrow> 
        (
          case (c (\<lambda> x. VBVConstOp (FMVar x))  pout) of
            None \<Rightarrow> VBVConstOp (FMVar pin) |
            (Some vo) \<Rightarrow> vo
        )
    )
  )"

definition fun_upd_fun :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool)  \<Rightarrow> ('a \<Rightarrow> 'b)"
where
  "fun_upd_fun f1 f2 g \<equiv> \<lambda> a. let b1 = f1 a in let b2 = f2 a in if g b1 b2 then b1 else b2"

fun is_ValuesVar :: "('vb, 'FMode, 'pin) ValuesOperand \<Rightarrow> bool"
where
  "is_ValuesVar (VBVConstOp (FMVar x)) = True" |
  "is_ValuesVar _ = False"

(* Lista de componentes e conexões*)
definition System :: "
  ('pin, 'pout) Connections \<Rightarrow> 
  ('vb, 'FMode, 'pin, 'pout) Component list \<Rightarrow> 
  ('vb, 'FMode, 'pin, 'pout) Component"
where
  "System A cs \<equiv> 
  (
    let C = SystemComponents cs in
    let pv = SystemPortValuation A C in
    (\<lambda> xpv.  
      let mpout = C (fun_upd_fun pv xpv (\<lambda> b1 b2. \<not> is_ValuesVar b1 )) in
      (\<lambda> pout. 
        let nvo = mpout pout in
        case nvo of None \<Rightarrow> None | Some vo \<Rightarrow> Some (normalise_expand_ValuesOperand vo)
      )
    )
  )"


(*

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
