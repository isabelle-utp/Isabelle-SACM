theory SACM_Examples
  imports "Isabelle_SACM.Isa_SACM"
begin

subsection \<open> Hazard Logs \<close>

text \<open> Here, we create a new (SACM) ``categories'' for Hazard and Hazard Logs. We are effectively
  extending our meta-model, potentially using bits defined in an ecore meta-model. \<close>

doc_class Hazard = "Artifact" +
  name :: string

doc_class HazardLog = "Artifact" +
  hazards :: "Hazard set"

doc_class FormalHazard = Hazard +
  condition :: "term"

text \<open> Here, we are creating new (SACM) ``terms'' that refer to a particular hazards. \<close>

text*[H1::FormalHazard, condition="@{term \<open>heat > 100\<close>}"] \<open>\<close>
text*[H2::Hazard] \<open>\<close>

text*[Hazard_Log::HazardLog, hazards="{@{docitem ''H1''}, @{docitem ''H2''}}"] \<open>\<close>
abbreviation "Hazard_Log \<equiv> ''Hazard_Log''"

theorem vc1: True by simp

subsection \<open> Hazard Mitigation Argument \<close>

print_doc_items

ArtifactReference ar_Hazard_Log artifacts "{@{docitem Hazard_Log}}"

Artifact FV1 version \<open>1\<close> \<open> Formal Verification Results: @{thm vc1} \<close>

Activity VACT1 startTime \<open>26/06/2020\<close> endTime \<open>27/06/2020\<close> 
  \<open> The activity that created the verification results @{thm vc1}. \<close>

ArtifactRelation AR1 src \<open>{@{Activity VACT1}}\<close> tgt \<open>{@{Artifact FV1}}\<close>
  \<open> The verification activity produced @{Artifact FV1}. \<close>

Resource Isabelle location \<open>http://isabelle.in.tum.de\<close> \<open> The Isabelle/HOL proof assistant. \<close>

Participant Anne_Other \<open> A proof engineer with expertise in the use of Isabelle. \<close>

ArtifactRelation AR2 src \<open>{@{Activity Anne_Other}}\<close> tgt \<open>{@{Artifact VACT1}}\<close>
  \<open> Anne Other led the verification activity. \<close>

Technique Isabelle_Simplifier
  \<open> The Isabelle simplifier tactic (@{method simp}). \<close>

ArtifactReference ar_FV1 artifacts "{@{docitem \<open>FV1\<close>}}"

Claim C1 \<open> The system is acceptably safe. \<close>

Claim C2 \<open> All identified hazards have been mitigated. \<close>

Inference I1 src \<open>{@{Claim C2}}\<close> tgt \<open>{@{Claim C1}}\<close>
  \<open> @{Claim C1} is supported by @{Claim C2}. \<close>

Context ac1 
  src \<open>{@{Artifact Hazard_Log}}\<close> tgt \<open>{@{Claim C2}}\<close>
  \<open> The Hazard Log @{HazardLog Hazard_Log} 
    is context for @{Claim C2} \<close>

Claim C3 \<open> @{Hazard H1} is sufficiently mitigated. \<close>

Evidence E1 
  src \<open>{@{Artifact FV1}}\<close> tgt "{@{Claim C3}}"
  \<open> Formal verification result @{Artifact FV1} 
    is evidence for @{Claim C3}. \<close>

Claim C4 needsSupport 
  \<open> @{Hazard H2} is sufficiently mitigated. \<close>

Artifact T1 \<open> Test Results \<close>

ArtifactReference ar_T1 artifacts "{@{docitem T1}}"

Evidence E2 src "{@{Artifact T1}}" tgt "{@{Claim C4}}"

Inference I2 src "{@{Claim C3}, @{Claim C4}}" tgt "{@{Claim C2}}"

print_doc_items

subsection \<open> DOF Queries \<close>

\<comment> \<open> Retrieve the term that characterises @{Claim C1} \<close>
ML \<open> DOF_core.get_value_global "C1" @{theory} \<close>

\<comment> \<open> Retrieve the term assigned to the @{term source} attribute in @{AssertedInference I1} \<close>
ML \<open> AttributeAccess.compute_attr_access (Context.Theory @{theory}) "source" "I1" @{here} @{here} \<close>

\<comment> \<open> Above, using an ML antiquotation \<close>
ML \<open> YXML.content_of (Syntax.string_of_term_global @{theory} @{docitem_attribute source :: I1}) \<close>

text \<open> How can we generate and prove proof obligations for OCL constraints on a meta-model? \<close>

(* Domain model, DFRS, Grammatico *)

(*
Claim Claim_A \<open> Claim text \<close>
Claim Claim_C \<open> Claim text \<close>

Inference Rel_A
  isCounter
  src \<open>{@{Claim Claim_A}}\<close>
  tgt \<open>{@{Claim Claim_B}}\<close>
  \<open> Reasoning for inference \<close>

text \<open> ... when I try to reference
       @{AssertedInference Rel_A} \<close>
*)

end