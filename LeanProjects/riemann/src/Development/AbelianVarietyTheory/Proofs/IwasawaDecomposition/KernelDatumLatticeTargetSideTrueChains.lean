import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalisationFormLatticeIffClassValuesWeylLatticeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientFieldFormValueMemPolynomialModelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefficientFieldFormOfPolynomialModelValueStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemLocalisedWeylLatticeIffTargetPairingIntegralStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

set_option maxHeartbeats 1000000 in

theorem kerEnt_latT : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ u μ w, LevFree Y u μ w → ∀ i, i < (I.rec7 l Z).R.m → ∀ φ : ((I.rec7 l Z).chTw u μ).cls (i + 1) → ((I.rec7 l Z).chTw u μ).Y (i + 1) → ℂ, (∃ y ∈ locW (I.rec7 l Z).what₂.places w (((I.tw l l0 Z).fm u μ).lat (i + 1)).L, ((I.tw l l0 Z).fm u μ).emb (i + 1) y = φ) ↔ (φ ∈ ((I.tw l l0 Z).fm u μ).Fi (i + 1) ∧ ∀ c', ∃ v' : ValQ O u μ (i + 1), evC O u μ (i + 1) v' = φ c' ∧ ∀ J, ‖prTC Pl O Bs u μ w i c' v' J‖ ≤ 1) := by
  intro B X I hok hpins l Z l0 Y O Pl Bs hQp hStd hBas hEnt hUnf hJets u μ w hw i hi φ
  have hL1 := fun x => GlobalTheory.T.localisation_formLattice_iff_classValues_weylLattice (I.stp u μ (i + 1)) B.fields.emb (lamT (B.hcW u) (i + 1)) ((l.fmL u μ).fam (i + 1))
    B.places w _ (Pl.iL w) (Pl.iL_int w) x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, fun c' => ?_⟩
    · rw [← (((I.tw l l0 Z).fm u μ).emb_basis (i + 1)).2, ← ((((I.tw l l0 Z).fm u μ).lat (i + 1)).b.sum_repr y), map_sum]
      exact Submodule.sum_mem _ fun a _ => by
        rw [LinearMap.map_smulₛₗ]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    · obtain ⟨v', hv'⟩ := GlobalTheory.T.coefficientField_form_value_mem_polynomialModel I hok hpins l Z l0 Y O Pl Bs hQp hStd hBas hEnt hUnf hJets u μ i hi y c'
      exact ⟨v', hv', (GlobalTheory.T.mem_localisedWeylLattice_iff_targetPairing_integral I hok hpins l Z l0 Y O Pl Bs hQp hStd hBas hEnt hUnf hJets u μ w hw i hi c' (y.1 c') v' hv').1
        ((hL1 y).1 hy c')⟩
  · rintro ⟨hF, hc⟩
    obtain ⟨x, rfl⟩ := GlobalTheory.T.exists_coefficientField_form_of_polynomialModel_values I hok hpins l Z l0 Y O Pl Bs hQp hStd hBas hEnt hUnf hJets u μ i hi φ hF
      (fun c' => (hc c').imp fun _ h => h.1)
    refine ⟨x, (hL1 x).2 fun c' => ?_, rfl⟩
    obtain ⟨v', hv', hn⟩ := hc c'
    exact (GlobalTheory.T.mem_localisedWeylLattice_iff_targetPairing_integral I hok hpins l Z l0 Y O Pl Bs hQp hStd hBas hEnt hUnf hJets u μ w hw i hi c' (x.1 c') v' hv').2 hn

end GlobalTheory.Mem.Col2.TC
