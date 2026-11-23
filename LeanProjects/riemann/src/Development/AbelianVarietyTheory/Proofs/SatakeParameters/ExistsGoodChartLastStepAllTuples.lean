import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLastStepTwistBasePointStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartsRebasedOneOffLevelPrimeKilledStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Formalism.LocalToGlobal.GroupLattices.Joint0
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwU.AtTrue

set_option maxHeartbeats 1000000 in

theorem chart_last_good : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))), (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.StdF l Z u F → ∃ (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a B.R.m).Cl → Ch) (Kc : Fam I l Z u a B.R.m le_rfl (badQ (I.rec7 l Z) Q) chOf), ReadsOne I l Z u a B.R.m le_rfl chOf Kc ∧ ∀ β, FunKilled (Kc β).lev (X.piT u) ∧ ∃ n : ℕ, 0 < n ∧ ∀ κ, (Kc β).lev.chi κ ^ n = 1 := by
  intro B X I hI hP l Z u Ch0 chOf0 F a Q hQ hF
  obtain ⟨K1, hR, -, -, hfin, -⟩ := GlobalTheory.T.chart_lastStep_twistBasePoint I hI hP l Z u a Q (F.cls B.R.m le_rfl (Or.inr rfl)) hQ
    (hF.ends B.R.m le_rfl (Or.inr rfl))
  obtain ⟨k, hk, -⟩ := hR
  obtain ⟨Kc, h1, h2⟩ := GlobalTheory.T.charts_rebased_one_off_levelPrime_killed I hI hP l Z u a B.R.m le_rfl (badQ (I.rec7 l Z) Q) Unit (fun _ => ()) K1 ⟨k, hk⟩
    (fun β => by cases β; exact hfin)
  exact ⟨Unit, inferInstance, fun _ => (), Kc, h1, h2⟩

end GlobalTheory.TwU.AtTrue

end
