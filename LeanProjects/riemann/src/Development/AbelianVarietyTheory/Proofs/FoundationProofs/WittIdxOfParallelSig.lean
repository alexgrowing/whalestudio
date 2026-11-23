import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.WittIndexParallel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfIsotropicSignature
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LandherrAndLandherrSt

noncomputable section

open NumberField Matrix Formalism.BasicNotions Formalism.BasicNotions.TH

namespace GlobalTheory.ParallelWitt

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

theorem embedding_star (τ : E →+* ℂ) (a : E) : τ (star a) = star (τ a) :=
  IsCMField.complexEmbedding_complexConj E τ a

theorem form_eq {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (x y : Fin S.rank → E) :
    S.hT (S.frame.equivFun.symm x) (S.frame.equivFun.symm y) = star x ⬝ᵥ (S.gram *ᵥ y) := by
  simp only [Module.Basis.equivFun_symm_apply, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, RingHom.id_apply, starRingEnd_apply, dotProduct, mulVec, HSpace.gram, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem finrank_le (S : HSpace E) {p q : ℕ} (τ : E →+* ℂ) (hs : Formalism.UG.HasSignature (S.gram.map τ) p q)
    (U : Submodule E S.V) (hU : ∀ x ∈ U, ∀ y ∈ U, S.hT x y = 0) : Module.finrank E U ≤ q := by
  let b := Module.finBasis E U
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective U.subtype U.ker_subtype
  let M := LinearMap.toMatrix b S.frame U.subtype
  let L := LinearMap.toMatrix S.frame b g
  have hL : L * M = 1 := by
    rw [← LinearMap.toMatrix_comp, hg, LinearMap.toMatrix_id]
  have hb : ∀ i, (b i : S.V) = ∑ a, M a i • S.frame a := by
    intro i
    simp only [M, LinearMap.toMatrix_apply, Submodule.subtype_apply]
    exact (S.frame.sum_repr _).symm
  have h : Mᴴ * S.gram * M = 0 := by
    ext i j
    have h0 := hU _ (b i).2 _ (b j).2
    rw [hb i, hb j] at h0
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply,
      starRingEnd_apply] at h0
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, HSpace.gram, Matrix.zero_apply]
    rw [← h0]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  refine (GlobalTheory.WittSignature.le_of_isotropic_signature _ hs (M.map τ) (L.map τ) ?_ ?_).2
  · rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero τ) (map_one τ)]
  · have : (M.map τ)ᴴ = (Mᴴ).map τ := by
      ext i j
      simp [Matrix.conjTranspose_apply, embedding_star]
    rw [this, ← Matrix.map_mul, ← Matrix.map_mul, h, Matrix.map_zero _ (map_zero τ)]

end CM

open GlobalTheory.IndefiniteRowSideFullHecke.WittIndexParallel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.ParallelWitt

end
