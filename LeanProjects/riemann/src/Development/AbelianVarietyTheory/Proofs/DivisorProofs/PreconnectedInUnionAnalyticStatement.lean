import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreconnectedInUnionAnalytic
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompReixMemAdm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot GlobalTheory.DblBox
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.darboux_doubled_transfer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (n d : ℕ) (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin d) (Fin d) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E)
      (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J) (incM F J')) (Fin n × Fin d))
      (cb : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J₂) (incM F J')) (Fin (n + n) × Fin d)), IsBoxCo co cb →
    ∀ [MeasurableSpace (Fin n × Fin d → AF F)] [BorelSpace (Fin n × Fin d → AF F)] (m : Measure (Fin n × Fin d → AF F)), m.IsAddHaarMeasure →
    ∀ l ∈ (adeleClass F).adm (Fin (n + n) × Fin d), (∃ φ ∈ schA F (Fin (n + n) × Fin d), l φ ≠ 0) →
    (∀ u : Matrix (Fin (n + n)) (Fin d) (AE F E), (∀ j, uᵀ j ∈ diagSub (AE F E) finSumFinEquiv) →
      ∀ φ ∈ schA F (Fin (n + n) × Fin d), l (cb.rho ψ u φ) = l φ) →
    ∃ c : ℂ, c ≠ 0 ∧ ∀ φ₁ ∈ schA F (Fin n × Fin d), ∀ φ₂ ∈ schA F (Fin n × Fin d), l (bx φ₁ φ₂) = c * ∫ x, φ₁ x * φ₂ x ∂m := by
  first | exact @GlobalTheory.DblBox.eq_smul_integral_bx | exact GlobalTheory.DblBox.eq_smul_integral_bx | (intros; apply GlobalTheory.DblBox.eq_smul_integral_bx <;> assumption)
