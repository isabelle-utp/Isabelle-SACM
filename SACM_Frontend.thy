theory SACM_Frontend
   imports SACM_Metamodel
   keywords (*Green Keywords*)
            "isAbstract" "isCitation" "content" "ISA_TERM" "isCounter" "src" "tgt" "reasoning" "REFERENCES" 
            "PROPERTIES" "occurence" "version" "date" "startTime" "endTime" "artifacts" "location" "metaClaims"
            "needsSupport" "axiomatic" "asserted" "assumed" "defeated" "ASSURANCE_CASE_PACKAGES" 
            "TERMINOLOGY_PACKAGES" "ARTIFACT_PACKAGES" "ARGUMENT_PACKAGES" "INTERFACE" "IMPLEMENTS"
            "Participant_PACKAGES" "ARGUMENTATION_ELEMENTS" "ARTIFACT_ELEMENTS" "TERMINOLOGY_ELEMENTS"
            and
            (*Blue keywords*)
            (* Keywords for terminology package leaf classes*)
            "Expression"
            (*Keywords for artifact package leaf classes*)
(*            "Property" *) "Participant" "Technique" "Event" "Activity" "Resource" "Artifact"
            (*Keywords for argument package leaf classes*)
            "Claim"
            "ArtifactReference" 
            "Inference"
            "Evidence" 
            "Context"
            "ArtifactContext"
            "ArtifactSupport"
            "ArtifactRelation"
(*
            "Context"
            "ArtifactSupport" 
 
            "ArtifactAssetRelation"
            "ASSURANCE_CASE_PACKAGE"
            "ASSURANCE_PACKAGE_INTERFACE"
            "ASSURANCE_PACKAGE_BINDING"
            "ARGUMENT_PACKAGE"
            "ARGUMENT_PACKAGE_INTERFACE"
            "ARGUMENT_PACKAGE_BINDING"
            "ARTIFACT_PACKAGE"
            "ARTIFACT_PACKAGE_INTERFACE"
            "ARTIFACT_PACKAGE_BINDING"
            "TERMINOLOGY_PACKAGE"
            "TERMINOLOGY_PACKAGE_INTERFACE"
            "TERMINOLOGY_PACKAGE_BINDING"
            "BLAH" *)::  thy_decl
            
begin

subsection \<open> SACM Entity Generators \<close>

ML \<open>

structure SACM_core = 
struct

\<comment> \<open> Generate an abbreviation from the given equation \<close>
fun gen_abbreviation spec = Named_Target.theory_map (Specification.abbreviation_cmd Syntax.mode_input NONE [] spec false);

\<comment> \<open> Generate an instance of the DOF command text* \<close>
fun gen_text_star name_generator n doc_class_name attrbt_names attrbt_pos attrbt_ctnts text =
      ((Onto_Macros.enriched_text_element_cmd NONE {markdown = true}
         ((((name_generator n, SOME (doc_class_name, Position.none)), 
            (attrbt_names ~~ attrbt_pos) ~~ (attrbt_ctnts)), 
            NONE),  
            text)));

\<comment> \<open> Parser for attribute definition (key-value pairs) \<close>
val attributes_add =  
    ((Parse.$$$ "["
      -- ODL_Command_Parser.improper 
     |-- (Parse.enum "," (ODL_Command_Parser.improper |-- ODL_Command_Parser.attribute)))
     --| Parse.$$$ "]"
     --| ODL_Command_Parser.improper);

\<comment> \<open> Generic interface for creating DOF instances \<close>
fun gen_dof_inst class prcr ((nm, pos), ((pout, attrs), txt)) =
        Toplevel.theory 
          (gen_abbreviation (nm ^ " \<equiv> ''"^nm^"''") #>
           (fn thy =>
           Onto_Macros.enriched_text_element_cmd NONE {markdown = true} (((((nm, pos), SOME (class, Position.none)), 
            prcr pout thy @ (case attrs of SOME a => a | NONE => [])), 
            NONE),  
            case txt of SOME t => t | NONE => Input.string "") thy));
                                                 
\<comment> \<open> Generic function for defining an Isabelle command that generates a SACM DOF instance. The 
  parameters include: (1) the command keyword; (2) the DOF class to be generated; (3) a comment
  that describes the command; (4) a pair consisting of a parser and generator for any optional
  subcommand keywords. \<close>
fun dof_instance cmd class cmt (prsr, prcr) =
  Outer_Syntax.command cmd cmt
  (Parse.position Parse.name -- (prsr -- Scan.option attributes_add -- Scan.option Parse.document_source) >>
   gen_dof_inst class prcr);

\<comment> \<open> Simpler version of above where there are no subcommands \<close>
fun dof_instance' cmd class cmt = dof_instance cmd class cmt (Scan.succeed "", fn _ => fn _ => []);

val assertDeclParser =
  (Scan.optional (@{keyword "needsSupport"} || @{keyword "asserted"} || @{keyword "axiomatic"} 
                  || @{keyword "assumed"} || @{keyword "defeated"}) "asserted");

val isCounterParser = Scan.option @{keyword "isCounter"} >> (fn x => case x of NONE => "False" | _ => "True");
val isAbstractParser = Scan.option @{keyword "isAbstract"} >> (fn x => case x of NONE => "False" | _ => "True");
val isCitationParser = Scan.option @{keyword "isCitation"} >> (fn x => case x of NONE => "False" | _ => "True");

end;

\<close>

subsection \<open> SACM Commands \<close>

ML \<open>

Outer_Syntax.command 
  @{command_keyword Expression}
  "Generate an SACM Expression"
  (Parse.position Parse.name -- Parse.term >>
  (fn (n, t) => Toplevel.theory
             (fn thy =>
             let open Syntax; open HOLogic;
                 val ctx = Proof_Context.init_global thy;
                 val ct = read_term ctx t;
                 val t' = YXML.content_of (string_of_term ctx ct) in
             (SACM_core.gen_abbreviation ((op ^) ((op ^) ((n |> fst), " \<equiv> "), "\<open>"^(n |> fst)^"\<close>")) #>
              SACM_core.gen_text_star (fn x => x) n "Expression" ["value_expr"] [Position.none] ["@{term ''" ^ t' ^ "''}"] (Input.string "")             
             ) thy end)));

SACM_core.dof_instance @{command_keyword Artifact} "Artifact" "Generate an SACM artifact"
  (Scan.optional (@{keyword version} |-- Parse.text) "" -- Scan.optional (@{keyword date} |-- Parse.text) ""
  , fn (v, d) => fn _ => [(("version", Position.none), "''" ^ v ^ "''"), (("date", Position.none), "''" ^ d ^ "''")]);

SACM_core.dof_instance @{command_keyword ArtifactReference} 
  "ArtifactReference" "Generate an SACM artifact reference"
  (@{keyword artifacts} |-- Parse.term, fn atfs => fn _ => [(("referencedArtifactElement_assoc", Position.none), atfs)]);

SACM_core.dof_instance @{command_keyword Resource} 
  "Resource" "Generate an SACM resource artifact"
  (@{keyword location} |-- Parse.path, fn loc => fn _ => [(("location_attr", Position.none), "''" ^ loc ^ "''")]);

SACM_core.dof_instance @{command_keyword Activity} 
  "Activity" "Generate an SACM activity artifact"
  (Scan.optional (@{keyword startTime} |-- Parse.text) "" -- Scan.optional (@{keyword endTime} |-- Parse.text) ""
   , fn (st, et) => fn _ => [(("startTime", Position.none), "''" ^ st ^ "''"), (("endTime", Position.none), "''" ^ et ^ "''")]);

SACM_core.dof_instance @{command_keyword Event} 
  "Event" "Generate an SACM event artifact"
  (Scan.optional (@{keyword occurence} |-- Parse.text) ""
   , fn st => fn _ => [(("occurence", Position.none), "''" ^ st ^ "''")]);

SACM_core.dof_instance' @{command_keyword Participant} 
  "Participant" "Generate an SACM participant artifact";

SACM_core.dof_instance' @{command_keyword Technique} 
  "Technique" "Generate an SACM technique artifact";

fun mk_dis ctx cs = Syntax.string_of_term ctx (Syntax.check_term ctx (HOLogic.mk_set dummyT (map (fn c => Const (@{const_name ISA_docitem}, dummyT) $ Const (c, dummyT)) cs)));

fun mkAssertRel cmd class cmt =
  SACM_core.dof_instance cmd class cmt                                                  
  (SACM_core.assertDeclParser -- (SACM_core.isCounterParser -- ((@{keyword src} |-- Parse.term) -- (@{keyword tgt} |-- Parse.term)))
   ,fn (s, (c, (src, tgt))) => fn _ => [(("isCounter", Position.none), c), (("assertionDeclaration", Position.none), s), (("source", Position.none), src), (("target", Position.none), tgt)]);

mkAssertRel @{command_keyword ArtifactContext} "AssertedArtifactContext" "Generate an SACM artifact context";
mkAssertRel @{command_keyword ArtifactSupport} "AssertedArtifactSupport" "Generate an SACM artifact support";
mkAssertRel @{command_keyword Context} "AssertedContext" "Generate an SACM context";
mkAssertRel @{command_keyword Inference} "AssertedInference" "Generate an SACM asserted inference";
mkAssertRel @{command_keyword Evidence} "AssertedEvidence" "Generate an SACM asserted evidence";

fun mkArtifactRel cmd class cmt =
  SACM_core.dof_instance cmd class cmt
  ((@{keyword src} |-- Parse.term) -- (@{keyword tgt} |-- Parse.term)
   ,fn (src, tgt) => fn _ => [(("source", Position.none), src), (("target", Position.none), tgt)]);

mkArtifactRel @{command_keyword ArtifactRelation} "ArtifactAssetRelationship" 
  "Generate an SACM asserted asset relationship";

SACM_core.dof_instance @{command_keyword Claim} "Claim" "Generate an SACM claim" 
  (SACM_core.isAbstractParser -- SACM_core.isCitationParser 
   -- SACM_core.assertDeclParser -- (Scan.optional (@{keyword metaClaims} |-- Parse.term) "{}")
  , fn (((a, c), s), m) => fn _ => [(("isAbstract", Position.none), a)
                                   ,(("isCitation", Position.none), c)
                                   ,(("assertionDeclaration", Position.none), s)
                                   ,(("metaClaim", Position.none), m)]);
\<close>

subsection \<open> Inner Syntax Antiquotations \<close>

syntax
  "_ArtifactReference" :: "logic \<Rightarrow> logic" ("@{ArtifactReference _}")
  "_Inference"         :: "logic \<Rightarrow> logic" ("@{Inference _}")
  "_Claim"             :: "logic \<Rightarrow> logic" ("@{Claim _}")
  "_Artifact"          :: "logic \<Rightarrow> logic" ("@{Artifact _}")
  "_Activity"          :: "logic \<Rightarrow> logic" ("@{Activity _}")

translations
  "_ArtifactReference a" => "@{docitem a} :: _ ArtifactElement_scheme"
  "_Inference i" => "@{docitem i}"
  "_Claim c" => "@{docitem c} :: _ Assertion_scheme"
  "_Artifact a" => "@{docitem a}"
  "_Activity a" => "@{docitem a}"

end
