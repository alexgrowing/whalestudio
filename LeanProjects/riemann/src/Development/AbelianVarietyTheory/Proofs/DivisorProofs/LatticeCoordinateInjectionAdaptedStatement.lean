import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCoordinateInjectionAdapted
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_coordinate_injection_adapted : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W),
    H.IsAdapted σ B X X₁ j₀ j₁ →
    ∀ (j : Fin n₁ × Fin d → Fin n × Fin d) (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d)),
      Function.Injective j →
      (∀ z, co.e (incM F H.ι * z) = (Function.extend j (M₁.co.e z).1 0, Function.extend j (M₁.co.e z).2 0)) →
      (∀ z, (co.e (Matrix.vecMulVec (incV F H.x) z)).1 = 0 ∧ ∀ k, (co.e (Matrix.vecMulVec (incV F H.x) z)).2 (j k) = 0) →
      (∀ z, (co.e (Matrix.vecMulVec (incV F H.y) z)).2 = 0 ∧ ∀ k, (co.e (Matrix.vecMulVec (incV F H.y) z)).1 (j k) = 0) →
      ∀ (v : Pl F),
      (∀ γ ∈ latAtV X W v, ∃ (a b : Fin d → AE F E) (z : Matrix (Fin n₁) (Fin d) (AE F E)), z ∈ latAtV X₁ W v ∧
        Matrix.vecMulVec (incV F H.x) a ∈ latAtV X W v ∧ Matrix.vecMulVec (incV F H.y) b ∈ latAtV X W v ∧
        γ = Matrix.vecMulVec (incV F H.x) a + incM F H.ι * z + Matrix.vecMulVec (incV F H.y) b) →
      (∀ w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v),
        (∀ γ ∈ latAtV X W v, GlobalTheory.LatVac.psiAt B.ψ v ((GlobalTheory.LatVac.locCo co v γ).1 ⬝ᵥ w.2 - w.1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2) = 1) →
        w ∈ (latAtV X W v).map (GlobalTheory.LatVac.locCo co v)) →
      ∀ (φ : (Fin n × Fin d → Fv F v) → ℂ) (θ : 𝓞 E),
        (∀ γ ∈ latAtV X W v, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo co v γ) φ =
          B.ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ) • φ) →
        ∀ x, φ x ≠ 0 → φ (Function.extend j (x ∘ j) 0) ≠ 0 := by
  first | exact @GlobalTheory.VacResNonvan.nonvan | exact GlobalTheory.VacResNonvan.nonvan | (intros; apply GlobalTheory.VacResNonvan.nonvan <;> assumption)
