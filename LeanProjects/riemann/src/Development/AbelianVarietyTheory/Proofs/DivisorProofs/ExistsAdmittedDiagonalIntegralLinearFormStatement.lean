import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedDiagonalIntegralLinearForm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_admitted_diagonal_integral_linearForm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (a a' : ℕ) (G : Geo σ a a') (ψ : AddChar (AF F) ℂ)
    (d' : Darboux (symp (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J)) (Fin a' × Fin (a + a')))
    (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) d' dd → ∀ v : Pl F,
    ∃ l ∈ (adeleClass F).adm ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a'))),
      (∀ z : Matrix (Fin (a + a')) (Fin a') (AE F E), ∀ φ ∈ (adeleClass F).sp ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a'))),
        l (dd.rho ψ (z * (diagCols (Fin a') : Matrix (Fin a' ⊕ Fin a') (Fin a') (AE F E))ᵀ) φ) = l φ) ∧
      ∃ r₀ : ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → AF F) → ℂ, (∀ φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v), Rest (evFin F v) φ r₀) ∧
      ∃ c₀ : ℂ, c₀ ≠ 0 ∧ ∃ μ : @MeasureTheory.Measure ((Fin a' × Fin (a + a')) → Fv F v) (borel _),
        @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧
        (∀ φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v), l (tens (evFin F v) φ r₀) = c₀ * ∫ x, φ (Sum.elim x x) ∂μ) ∧
        ∃ φ₀ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∫ x, φ₀ x * φ₀ x ∂μ ≠ 0 := by
  first | exact @GlobalTheory.DiagLocal.exists_diag_form | exact GlobalTheory.DiagLocal.exists_diag_form | (intros; apply GlobalTheory.DiagLocal.exists_diag_form <;> assumption)
