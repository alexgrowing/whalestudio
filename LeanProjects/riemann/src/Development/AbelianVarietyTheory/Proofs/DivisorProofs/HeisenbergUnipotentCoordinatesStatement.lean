import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergUnipotentCoordinates
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainClosure

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_unipotent_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁) (r s i₀ i₁ : ℕ), B.IsGood σ → Y.IsHerm σ B r s → H.IsAdapted σ B Y Y₁ i₀ i₁ →
  ∃ (Φ : unip σ Y H ≃ₜ (Fin n₁ → AE F E) × AF F) (β : (Fin n₁ → AE F E) → (Fin n₁ → AE F E) → AF F), Continuous (Function.uncurry β) ∧
    (∀ u v, Φ (u * v) = ((Φ u).1 + (Φ v).1, (Φ u).2 + (Φ v).2 + β (Φ u).1 (Φ v).1)) ∧
    ∀ (t : (AE F E)ˣ) (m : UA σ Y.J), IsLevi (W₁ := Y₁) H (Units.map (cA σ : AE F E →* AE F E) t) 1 m →
      ∀ u : unip σ Y H, ∃ h : m * u.1 * m⁻¹ ∈ unip σ Y H,
        Φ ⟨m * u.1 * m⁻¹, h⟩ = (cA σ (t : AE F E) • (Φ u).1, Algebra.norm (AF F) (t : AE F E) * (Φ u).2) := by
  first | exact @GlobalTheory.UnipCoord.exists_coord_unip | exact GlobalTheory.UnipCoord.exists_coord_unip | (intros; apply GlobalTheory.UnipCoord.exists_coord_unip <;> assumption)
