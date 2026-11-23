import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedDbarPartialCommutation
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEqZeroOfHolomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeContrSelfApply
open Matrix GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.FlatAcyc
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_dbar_partial_commutation : ∀ {g : ℕ} (G : Matrix (Fin g) (Fin g) ℂ) (ψ : (Fin g → ℂ) → ℂ)
    (f : (Fin g → ℂ) → Ext (0 + 0 + g)) (hf : Differentiable ℝ f) (hψ : Differentiable ℝ ψ)
    (hf01 : ∀ v, Differentiable ℝ (fun z => d01 f z v)) (hf10 : ∀ v, Differentiable ℝ (fun z => d10 f z v))
    (hψ10 : ∀ v, Differentiable ℝ (fun z => d10 ψ z v))
    (hmix : ∀ z v w, d01 (fun z' => d10 f z' v) z w = d10 (fun z' => d01 f z' w) z v)
    (z : Fin g → ℂ),
    dbarF (dbarAdjF G ψ f) z + dbarAdjF G ψ (dbarF f) z =
      -(∑ a, ∑ c, G a c • (d10 (fun z' => d01 f z' (ev c)) z (ev a) + d10 ψ z (ev a) • d01 f z (ev c))) -
      ∑ a, ∑ c, ∑ d, (G a c * d01 (fun z' => d10 ψ z' (ev a)) z (ev d)) •
        wedge (dzb 0 d) (contr (dzb 0 c) (f z)) := by
  first | exact @GlobalTheory.TorsionForm.FlatAcyc.Cross.dbarF_dbarAdjF_add | exact GlobalTheory.TorsionForm.FlatAcyc.Cross.dbarF_dbarAdjF_add | (intros; apply GlobalTheory.TorsionForm.FlatAcyc.Cross.dbarF_dbarAdjF_add <;> assumption)
