import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicComplementFormRestrict
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_complement_form_restrict : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n n₁ : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (J₁ : Matrix (Fin n₁) (Fin n₁) E) (x y : Fin n → E) (ι : Matrix (Fin n) (Fin n₁) E),
    (∀ z, σ (σ z) = z) → (∀ i j, σ (J j i) = J i j) → form σ J x x = 0 → form σ J y y = 0 →
    form σ J x y = 1 → (∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) → ιᵀ * J * ι.map σ = J₁ → J₁.det ≠ 0 →
    ∀ (a b : AE F E) (w : Fin n₁ → AE F E), a • incV F x + incM F ι *ᵥ w + b • incV F y = 0 → a = 0 ∧ w = 0 ∧ b = 0 := by
  first | exact @GlobalTheory.LeviIndep.indep | exact GlobalTheory.LeviIndep.indep | (intros; apply GlobalTheory.LeviIndep.indep <;> assumption)
