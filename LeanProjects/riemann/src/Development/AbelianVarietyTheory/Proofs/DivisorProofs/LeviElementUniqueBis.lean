import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAHaarUnfoldingMeasure
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.LeviUniqueGen

theorem levi_unique_gen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X Y : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) (r s i₀ i₁ : ℕ), B.IsGood σ → X.IsHerm σ B r s → (reS X Y).IsHerm σ B r s → H.IsAdapted σ B (reS X Y) X₁ i₀ i₁ → ∀ (t : (AE F E)ˣ) (h₁ : UA σ X₁.J) (h h' : UA σ X.J), IsLevi (W₁ := X₁) H t h₁ h → IsLevi (W₁ := X₁) H t h₁ h' → h = h' := by
  intro F E _ _ _ _ _ σ B n n₁ X Y X₁ H r s i₀ i₁ hB hX hXY hH t h₁ h h' hl hl'
  obtain rfl := hH.rank
  have hL : Submodule.span E ((reS X Y).L : Set (Fin (n₁ + 2) → E)) = ⊤ := by
    haveI := hXY.lat
    exact Submodule.IsLattice.span_eq_top
  have key : ∀ z : Fin (n₁ + 2) → E, mat h *ᵥ incV F z = mat h' *ᵥ incV F z := fun z => by
    obtain ⟨a, b, u, rfl⟩ := GlobalTheory.IterBochner.exists_decomp B H (reS X Y) X₁ hH hL z
    rw [GlobalTheory.IterBochner.incV_decomp]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hl.1, hl.2.1, hl.2.2, hl'.1, hl'.2.1, hl'.2.2]
  have hmat : mat h = mat h' := by
    ext i j
    have := congrFun (key (Pi.single j 1)) i
    rw [GlobalTheory.IterBochner.incV_single] at this
    simpa [Matrix.mulVec_single_one] using this
  exact Subtype.ext (Units.ext hmat)

end GlobalTheory.LeviUniqueGen
