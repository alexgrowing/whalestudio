import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothColRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeJacquetRepEquivRowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicInductionColumnFalseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicInductionColumnTrueStatement

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SmGL.RowOneCell Matrix
open scoped TensorProduct

namespace GlobalTheory.SmGL.RowOneCell

theorem cell_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → ∀ (u v : ℕ)
    (B : SizeMatrix (Two (Fin u) (Fin (v + 1))) (Two (Fin 1) (Fin (u + v)))), B.1 true false = 1 →
    ∃ (f : ∀ i, (Σ j, Fin (B.1 i j)) ≃ Two (Fin u) (Fin (v + 1)) i)
      (g : ∀ j, (Σ i, Fin (B.1 i j)) ≃ Two (Fin 1) (Fin (u + v)) j),
      Nonempty (Representation.Equiv ((cellFunctor f g ((extTensor (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂)).comp
        (leviTwo k (Fin u) (Fin (v + 1))).symm.toMonoidHom)).comp
          (leviTwo k (Fin 1) (Fin (u + v))).toMonoidHom)
        (extTensor (detRep (Fin 1) (χ₂ * absPow k (-(v : ℂ) / 2)))
          (prod₂ (detRep (Fin u) χ₁) (detRep (Fin v) (χ₂ * absPow k (1 / 2)))))) := by
  intro k _ _ _ _ χ₁ χ₂ h₁ h₂ u v B hB
  obtain ⟨b, hb⟩ := B
  have hb' : b = sz u v := eq_sz b hb hB
  subst hb'
  refine Exists.intro (rowPart u v) ?_
  refine Exists.intro (colPart u v) ?_
  exact ⟨((GlobalTheory.LocGL.compEquiv ((CellSemis.relIndEquiv (colPart u v) (GlobalTheory.T.relative_jacquet_rep_equiv_row χ₁ χ₂ u v).some).trans
    (GlobalTheory.T.normalised_induction_product_parabolic_piTensor k Bool Bool (Two (Fin 1) (Fin (u + v))) (fun j i => Fin (sz u v i j)) (colPart u v)
      (fun _ => ℂ ⊗[ℂ] ℂ) (colRep χ₁ χ₂ u v) (isSmooth_colRep h₁ h₂ u v)).some)
    (leviTwo k (Fin 1) (Fin (u + v))).toMonoidHom).trans
      (GlobalTheory.JacFactor.piTensorBoolEquiv _)).trans
        (extTensorEquiv (GlobalTheory.T.parabolic_induction_column_false χ₁ χ₂ h₂ u v).some (GlobalTheory.T.parabolic_induction_column_true χ₁ χ₂ u v).some)⟩

end GlobalTheory.SmGL.RowOneCell
