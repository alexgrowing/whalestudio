import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartsRebasedOneOffLevelPrimeKilledStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleChainMiddleStageChartsJoinedMemberStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.AtTrue

set_option maxHeartbeats 4000000 in

theorem goodCharts_mid : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))), (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.StdF l Z u F → ∀ (i : ℕ) (hi : i ≤ B.R.m), 1 ≤ i → i < B.R.m → ∃ (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a i).Cl → Ch) (Kc : Fam I l Z u a i hi (badQ (I.rec7 l Z) Q) chOf), ReadsOne I l Z u a i hi chOf Kc ∧ ∀ β, FunKilled (Kc β).lev (X.piT u) ∧ ∃ n : ℕ, 0 < n ∧ ∀ κ, (Kc β).lev.chi κ ^ n = 1 := by
  intro B X I hI hP l Z u Ch0 chOf0 F a Q hQ hF i hi h1 h2
  have h2' : i + 1 ≤ B.R.m := h2
  obtain ⟨Ch, hCh, chOf, K, g, hK, hKb⟩ :=
    GlobalTheory.T.tupleChain_middleStage_charts_joined_member I hI hP l Z u a Q i hi (Ch0 i) (chOf0 i) (F.ch i h1 h2') h1 h2 hQ (hF.mid i h1 h2')
  obtain ⟨Kc, hR, hKc⟩ := GlobalTheory.T.charts_rebased_one_off_levelPrime_killed I hI hP l Z u a i hi (badQ (I.rec7 l Z) Q) Ch chOf K hK
    (fun β => (hKb β).2.1)
  exact ⟨Ch, hCh, chOf, Kc, hR, hKc⟩

end GlobalTheory.TwU.AtTrue
