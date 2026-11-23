import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.TiedTwJSym
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelLocalGroupEqOfAgreeOffPlacesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteOrderChartsMiddleStepsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberChartMatchingAwayFromTwistStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC.ChTw

set_option maxHeartbeats 1000000 in

theorem charts_tuple : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (i : ℕ) (hi : i ≤ B.R.m) (Ch0 : Type) (chOf0 : (I.stp u I.mu0 i).Cl → Ch0) (K0 : ∀ β : Ch0, LevelChart (I.rec7 l Z) (B.T u) (badG (I.rec7 l Z)) i hi (fun c : {c // chOf0 c = β} => (I.chain l u I.mu0).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u I.mu0 i c.1))), 1 ≤ i → i < B.R.m → (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.ReadsK l Z u I.mu0 i hi chOf0 K0 → ∃ (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (g : Ch → Ch0), I.ReadsK l Z u a i hi chOf K ∧ ∀ β, (∀ v, v ∉ Q → (K β).lev.Uloc v = (K0 (g β)).lev.Uloc v) ∧ (∃ n : ℕ, 0 < n ∧ ∀ κ, (K β).lev.chi κ ^ n = 1) ∧ ∀ (κ : (K β).lev.U) (κ' : (K0 (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = (K0 (g β)).lev.chi κ' := by
  intro B X I hok hpins l Z u a Q i hi Ch0 chOf0 K0 h1 h2 hQ hR
  obtain ⟨g, k, hk, hC⟩ := GlobalTheory.T.exists_memberChart_matching_awayFromTwist I hok hpins l Z u a Q i hi Ch0 chOf0 K0 h1 h2 hQ hR
  have hB := GlobalTheory.T.exists_finiteOrder_charts_middle_steps I hok hpins l Z u a Q i hi h1 h2 hQ k hk
  obtain ⟨K, hKB⟩ := hB
  have hK := hKB.1
  have hfin := hKB.2
  have hCK := hC K hK
  haveI := finite_chart I l u a i
  refine ⟨Chart I u a i, inferInstance, chartOf I u a i, K, g, ⟨k, hK⟩, fun β => ⟨?_, hfin β, ?_⟩⟩
  · intro v hv
    refine GlobalTheory.T.stepLevel_localGroup_eq_of_agree_off_places (K β).lev (K0 (g β)).lev (Q : Set _) (fun x hx => ⟨fun hxK => ?_, fun hx0 => ?_⟩) v hv
    · exact ((hCK β).1 ⟨x, hxK⟩ hx).1
    · exact (hCK β).2 ⟨x, hx0⟩ hx
  · intro κ κ' he hq
    obtain ⟨h', e⟩ := (hCK β).1 κ hq
    exact e.trans (congrArg (K0 (g β)).lev.chi (Subtype.ext he))

end GlobalTheory.Mem.Col2.TC.ChTw
