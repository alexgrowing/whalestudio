import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompanionLatticeTrueColumnBaseLatticeEqStandard
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Formalism.LocalToGlobal.GroupLattices.Joint0
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.companionLattice_trueColumn_baseLattice_eq_standard : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (i : ℕ) (hi : i ≤ B.R.m) (Lb : Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)), (∀ x, x ∈ Lb ↔ x ∈ baseL B (B.R.N i) (X.piT u)) → GlobalTheory.TwU.latCo (I.rec7 l Z).sp (gramN (I.rec7 l Z) i hi) 1 (B.fields.conjO (X.piT u)) 1 Lb = StandardLatticesGL3.stdL (I.rec7 l Z) (B.R.N i) := by
  first | exact @GlobalTheory.TwU.latCo_base_eq_stdL | exact GlobalTheory.TwU.latCo_base_eq_stdL | (intros; apply GlobalTheory.TwU.latCo_base_eq_stdL <;> assumption)
