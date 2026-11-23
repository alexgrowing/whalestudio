import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedRepSigmaApplyQuotient
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRelParabColEq
open GlobalTheory.PRep GlobalTheory.SmGL Matrix GlobalTheory.CellDetFirst
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_rep_sigma_apply_quotient : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) (p : relParab k (colEq u v)) (w : ℂ ⊗[ℂ] ℂ),
    sigmaC χ₁ χ₂ u v p (Submodule.Quotient.mk w) =
    (((χ₂ * absPow k ((v : ℂ) / 2)) (GeneralLinearGroup.det (p.1 true)) *
      deltaHalf k (Two (Fin u) (Fin v))
        (leviProj k (two (stdSum (rfl : u + v = u + v))) ⟨p.1 false, (mem_relParab_colEq _).1 p.2⟩) *
      (χ₁ (GeneralLinearGroup.det (leviProj k (two (stdSum (rfl : u + v = u + v)))
          ⟨p.1 false, (mem_relParab_colEq _).1 p.2⟩ false)) *
        (χ₂ * absPow k (-(1 / 2))) (GeneralLinearGroup.det (leviProj k (two (stdSum (rfl : u + v = u + v)))
          ⟨p.1 false, (mem_relParab_colEq _).1 p.2⟩ true))) : ℂˣ) : ℂ) • Submodule.Quotient.mk w := by
  first | exact @GlobalTheory.CellDetFirst.sigmaC_mk_scalar | exact GlobalTheory.CellDetFirst.sigmaC_mk_scalar | (intros; apply GlobalTheory.CellDetFirst.sigmaC_mk_scalar <;> assumption)
