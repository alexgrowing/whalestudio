import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeComapMulVecLinOfLeftInverseMatrix

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory

theorem isLattice_complement_of_adapted_plane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁) (i₀ i₁ r s : ℕ),
    W.IsSkew σ B r s → H.IsAdapted σ B W W₁ i₀ i₁ → ∀ P : Matrix (Fin n₁) (Fin n) E, P * H.ι = 1 → W₁.L.IsLattice E := by
  intro F E _ _ _ _ _ σ B _ n n₁ W W₁ H i₀ i₁ r s hW hH P hP
  have hL : W₁.L = W.L.comap ((Matrix.mulVecLin H.ι).restrictScalars (𝓞 E)) := by
    ext u
    rw [hH.low u]
    rfl
  rw [hL]
  exact isLattice_comap_mulVecLin_of_leftInverse E n n₁ W.L H.ι P hP hW.lat

end GlobalTheory
