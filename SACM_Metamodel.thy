theory SACM_Metamodel
   imports Isabelle_DOF.Isa_COL
begin
section \<open>SACM MISC\<close>

text \<open> We make a design decision not to explicitly represent the content attribute in the SACM
  class LangString. As we understand it, the content of this is always informal and descriptive
  information, which will never be subject to machine processing. Consequently, it seems to make
  sense that this is carried as informal content in the Isabelle type @{ML_type Input.source}
  via the cartouche mechanism.\<close>

record LangString =
  ls_lang    :: "string option"
  ls_content :: "string option"
  ls_expr    :: "term option"

abbreviation "emptyLangString \<equiv> \<lparr> ls_lang = None, ls_content = None, ls_expr = None \<rparr>"

type_synonym MultiLangString = "LangString list"

(*
doc_class LangString =
  lang :: "string" <= "''English''"

doc_class MultiLangString =
  value_assoc :: "LangString set"
*)

section \<open>SACM Elements Metamodel\<close>

subsection\<open>The class \emph{SACMElement}\<close>

doc_class SACMElement =
  gid:: string
  isCitation::bool <= False
  isAbstract::bool <= False

section \<open>SACM Artifacts Metamodel\<close>

subsection\<open>The class \emph{ArtifactElement}\<close>

doc_class ArtifactElement = SACMElement +
  isAbstract::bool <= False

subsection\<open>The class \emph{ArtifactAsset}\<close>

doc_class ArtifactAsset = ArtifactElement +
  taggedValue_assoc:: MultiLangString <= "[]"

subsection\<open>The class \emph{Property}\<close>

doc_class Property = ArtifactAsset +
  taggedValue_assoc:: MultiLangString <= "[]"

subsection\<open>The class \emph{Artifact}\<close>
doc_class Artifact = ArtifactAsset +
  version:: string 
  date   :: string
  property_assoc :: "Property set"

subsection\<open>The class \emph{Activity}\<close>
doc_class Activity = ArtifactAsset +
  startTime:: string 
  endTime  :: string
  property_assoc :: "Property set"

subsection\<open>The class \emph{Event}\<close>
doc_class Event = ArtifactAsset +
  occurence :: string 
  property_assoc :: "Property set"

subsection\<open>The class \emph{Participant}\<close>
doc_class Participant = ArtifactAsset +
  property_assoc :: "Property set"

subsection\<open>The class \emph{Technique}\<close>
doc_class Technique = ArtifactAsset +
  property_assoc :: "Property set"

subsection\<open>The class \emph{Resource}\<close>

doc_class Resource = ArtifactAsset +
  location_attr :: string
  property_assoc :: "Property set"

doc_class Requirement = Artifact +
  property_assoc :: "Property set" <= "{}"

subsection\<open>The class \emph{ArtifactAssetRelationship}\<close>

doc_class ArtifactAssetRelationship = ArtifactAsset +
  source:: "ArtifactElement set"
  target :: "ArtifactElement set"

section \<open>SACM terminology\<close>

subsection \<open>The class TerminologyElement\<close>

doc_class TerminologyElement = ArtifactElement +
  isAbstract::bool <= False

subsection \<open>The class TerminologyGroup\<close>

doc_class TerminologyGroup = SACMElement +
  terminologyElement_assoc ::  \<open>TerminologyElement set\<close>

subsection \<open>The class \emph{TerminologyPackage}\<close>

doc_class TerminologyPackage = SACMElement +
  TrP_terminologyElement_assoc:: "TerminologyElement set"

subsection \<open>The class \emph{TerminologyPackageInterface}\<close>

doc_class TerminologyPackageInterface = TerminologyPackage +
  TrPI_implements_assoc:: "TerminologyPackage"

subsection\<open>The class \emph{TerminologyPackageBinding}\<close>

doc_class TerminologyPackageBinding = TerminologyPackage +
  TrPB_participantPackage:: "TerminologyPackage set" (*The invariant is (card (participantPackage) \<ge> 2)*)

subsection \<open>The class TerminologyAsset\<close>

type_synonym TerminologyAsset = TerminologyElement

doc_class Term = TerminologyElement +
  isAbstract::bool <= False

(*
subsection \<open>The class ExpressionElement\<close>

doc_class ExpressionElement = ArtifactElement +
  value_expr:: "term"

subsection \<open>The class ExpressionLangString\<close>

doc_class ExpressionLangString = LangString +
  expression_element_assoc:: ExpressionElement

subsection \<open>The class Expression\<close>

doc_class Expression = ExpressionElement +
  expr_dummy:: string <= "''expr_dummy''"
*)

section \<open>SACM Argument Metamodel\<close>

subsection\<open>The class \emph{ArgumentationElement}\<close>

type_synonym ArgumentationElement = ArtifactElement

subsection\<open>The class ArgumentGroup\<close> 

doc_class ArgumentGroup = SACMElement +
  AG_argumentationElement_assoc:: "ArgumentationElement set"

subsection \<open>The class \emph{ArgumentPackage}\<close>

doc_class ArgumentPackage = SACMElement +
  AP_argumentationElement_assoc:: "ArgumentationElement set"

subsection \<open>The class \emph{ArgumentPackageInterface}\<close>

doc_class ArgumentPackageInterface = ArgumentPackage +
  API_implements_assoc:: "ArgumentPackage"

subsection\<open>The class \emph{ArgumentPackageBinding}\<close>

doc_class ArgumentPackageBinding = ArgumentPackage +
  APB_participantPackage:: "ArgumentPackage set" (*The invariant is (card (participantPackage) \<ge> 2)*)
    
subsection\<open>The class \emph{ArgumentAssets}\<close>

doc_class ArgumentAsset = ArtifactElement +
  content_assoc :: MultiLangString <= "[]"

subsection\<open>The class \emph{ArtifactReference}\<close>

doc_class ArtifactReference = ArgumentAsset +
  referencedArtifactElement_assoc:: "ArtifactElement set"

subsection\<open>The class \emph{Assertion}\<close>

datatype assertionDeclarations_t = 
  asserted|axiomatic|defeated|assumed|needsSupport(*|AsCited|Abstract*) (*is that a duplication of the value of the attributes?*)

doc_class Assertion = ArgumentAsset +
  assertionDeclaration::assertionDeclarations_t <= asserted

subsection\<open>The class \emph{Claim}\<close>

doc_class Claim = Assertion +
  metaClaim::"Assertion set" <= "{}"

subsection\<open>The class \emph{ArgumentReasoning}\<close>

doc_class ArgumentReasoning = ArgumentAsset +
   structure_assoc  :: "ArgumentPackage option" <= None

subsection\<open>The class \emph{AssertedRelationship}\<close>

text \<open> Unlike in the reference meta-model, the \emph{AssertedInference} class does not contain
  a source and target attribute. Instead, we put them in the individual classes. This allows
  us to specialise their types and so enforce well-formedness. For example, inferences can
  only connect assertions and asserted \<close>

doc_class AssertedRelationship = Assertion +
  isCounter::bool
  reasoning_assoc:: "ArgumentReasoning option"

subsection\<open>The class \emph{AssertedInference}\<close>
text \<open>The class \emph{AssertedInference} is a concrete class that inherit from 
      \emph{AssertedRelationship}. It describes a relation between claims. Since
      it is a concrete class we define the isar command \inlineisar+claim__1::Claim+ \inlineisar+AND+
      \inlineisar+claim__2::Claim+ for it in the front-end.
      The isar command \inlineisar+AND+ will inherit all the base designs of the attributes in the super
      classes, such as, the plus symbol \inlineisar{+} at the beginning and the end of the command if the attribute
      \emph{isCounter} has the value True. As attributes we add we define \emph{target} and \source{source}
      of type \inlineisar+Claim+. \<close>

doc_class AssertedInference = AssertedRelationship +
  isCounter::bool <= False
  source::"Assertion set"
  target::"Assertion set"

subsection\<open>The class \emph{AssertedEvidence}\<close>
text \<open>The class \emph{AssertedEvidence} is a concrete class that inherit from 
      \emph{AssertedRelationship}. It describes a relation between an evidence and a claim. Since
      it is a concrete class we define the isar command \inlineisar+FROM+
      \inlineusar+source::Evidence+ \inlineisar+HAVE+
      \inlineusar+target::Claim+ for it in the front-end.
      The isar commands \inlineisar+FROM+ and \inlineisar+HAVE+  will inherit all the base designs 
      of the attributes in the super classes, such as, the plus symbol at the beginning and the end 
      of the command if the attribute
      \emph{isCounter} has the value True. As attributes we add we define \emph{target} and \source{source}
      of type \inlineisar+Claim+\<close>

doc_class AssertedEvidence = AssertedRelationship +
  isCounter::bool <= False
  source::"ArtifactAsset set"
  target::"Assertion set"

subsection\<open>The class \emph{AssertedContext}\<close>

text \<open>The class \emph{AssertedContext} is a concrete class that inherit from 
      \emph{AssertedRelationship}. It describes a relation between a context and a claim. Since
      it is a concrete class we define the isar command \inlineisar+IN+ \inlineusar+source::Context+ 
      \inlineisar+HAVE+ \inlineisar+target::Claim+ for it in the front-end.
      The isar command \inlineisar+IN+ will inherit all the base designs of the attributes in the super
      classes, such as, the plus symbol at the beginning and the end of the command if the attribute
      \emph{isCounter} has the value True. As attributes we add we define \emph{target} and \source{source}
      of type \inlineisar+Claim+\<close>   

doc_class AssertedContext = AssertedRelationship +
  isCounter::bool <= False
  source::"ArtifactElement set"
  target::"Assertion set"

subsection\<open>The class \emph{AssertedArtifactSupport}\<close>

text \<open>The class \emph{AssertedArtifactSupport} is a concrete class that inherit from
      \emph{AssertedRelationship}. It describes a relation between artifacts. Since
      it is a concrete class we define the isar command  \inlineusar+source::term+ 
     \inlineisar+AND_STAR+ \inlineusar+target::term+ for it in the front-end.
      The isar command \inlineisar+AND_STAR+ will inherit all the base designs of the attributes in the super
      classes, such as, the plus symbol at the beginning and the end of the command if the attribute
      \emph{isCounter} has the value True. As attributes we add we define \emph{target} and \source{source}
      of type \inlineisar+Claim+\<close>   

doc_class AssertedArtifactSupport = AssertedRelationship +
  isCounter::bool <= False
  source::"ArtifactAsset set"
  target::"ArtifactAsset set"

subsection\<open>The class \emph{AssertedArtifactContext}\<close>
text \<open>The class \emph{AssertedArtifactContext} is a concrete class that inherit from 
      \emph{AssertedRelationship}. It describes a relation between context and artifacts. Since
      it is a concrete class we define the isar command  \inlineisar+USING+ \inlineusar+source::term+ 
     \inlineisar+PROVIDES+ \inlineusar+target_ctxt::Context+ \inlineisar+FOR+ 
      \inlineusar+target_art::term+ for it in the front-end.
      The isar command will inherit all the base designs of the attributes in the super
      classes, such as, the plus symbol at the beginning and the end of the command if the attribute
      \emph{isCounter} has the value True. As attributes we add we define \inlineisar+target_ctxt+,
       \inlineisar+target_art+ and  \inlineisar+source+
      of type \inlineisar+Claim+\<close>   
doc_class AssertedArtifactContext = AssertedRelationship +
  isCounter::bool <= False
  source::"ArtifactElement set"
  target::"Assertion set"


section \<open>SACM Assurance Case Metamodel\<close>

subsection \<open>ACP types\<close>

subsection \<open>The class \emph{ArtifactPackage}\<close>

doc_class ArtifactPackage = SACMElement +
  ArP_artifactElement_assoc:: "ArtifactElement set"
  rejects "Claim"
  accepts "\<lbrace>ArtifactElement\<rbrace>\<^sup>*"

subsection \<open>The class \emph{ArtifactPackageInterface}\<close>

doc_class ArtifactPackageInterface = ArtifactPackage +
  ArPI_implements_assoc:: "ArtifactPackage"

subsection\<open>The class \emph{ArgumentPackageBinding}\<close>

doc_class ArtifactPackageBinding = ArtifactPackage +
  ArPB_participantPackage:: "ArtifactPackage set" (*The invariant is (card (participantPackage) \<ge> 2)*)

datatype ACP_interface_t = Arg_interface ArgumentPackageInterface| 
                           Art_interface ArtifactPackageInterface|
                           Ter_interface TerminologyPackageInterface|
                           Int_interface ACP_interface_t

datatype ACP_package_t = Arg_package ArgumentPackage| 
                         Art_package ArtifactPackage|
                         Ter_package TerminologyPackage|
                         Pac_package ACP_package_t

subsection \<open>The class AssuranceCasePackage\<close>

doc_class AssuranceCasePackage = SACMElement +
  assurancecasepackage_assoc::\<open>ACP_package_t set set\<close> 
  terminologypackage_assoc  ::\<open>TerminologyPackage set\<close>
  argumentpackage_assoc     ::\<open>ArgumentPackage set\<close>
  artifactpackage_assoc     ::\<open>ArtifactPackage set\<close>
  ACI_interface_assoc       ::\<open>ACP_interface_t set set\<close> 

subsection \<open>The class AssurancePackageInterface\<close>

doc_class AssurancePackageInterface = \<open>AssuranceCasePackage\<close> + 
  ACP_implements_assoc:: \<open>AssuranceCasePackage\<close>

subsection \<open>The class AssurancePackageBinding\<close>

doc_class AssurancePackageBinding = AssuranceCasePackage +
  ACP_participant_package:: \<open>AssuranceCasePackage set\<close> (*card ACP_participant_package \<ge> 2*)

(*
text \<open> Global warning or error \<close>

open_monitor*[ap1::ArtifactPackage]

text*[ar1::Artifact] \<open> An artifact \<close>

text*[ar2::Artifact] \<open> Another artifact \<close>

text*[ar3::Claim] \<open> Another artifact \<close>

text*[ar4::Claim] \<open> Another artifact \<close>

close_monitor*[ap1]
*)

end
