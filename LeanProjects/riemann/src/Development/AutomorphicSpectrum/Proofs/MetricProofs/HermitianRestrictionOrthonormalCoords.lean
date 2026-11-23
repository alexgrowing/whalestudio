import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsFundSet
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.HermCoords

open scoped MatrixOrder ComplexOrder

theorem posDef_of_re_pos {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm *ᵥ star z).re) : Hm.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH ?_
  intro x hx
  have h := hpos (star x) (star_ne_zero.2 hx)
  rw [star_star] at h
  have him : (star x ⬝ᵥ Hm *ᵥ x).im = 0 := by
    have := hH.im_star_dotProduct_mulVec_self x
    rwa [RCLike.im_to_complex] at this
  exact Complex.pos_iff.2 ⟨h, him.symm⟩

theorem exists_factor {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hP : Hm.PosDef) :
    ∃ T : Matrix (Fin g) (Fin g) ℂ, ∀ z z' : Fin g → ℂ,
      z' ⬝ᵥ Hm *ᵥ star z = (T *ᵥ z') ⬝ᵥ star (T *ᵥ z) := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hP.posSemidef.nonneg
  rw [Matrix.star_eq_conjTranspose] at hB
  refine ⟨(Bᴴ)ᵀ, fun z z' => ?_⟩
  have hT : ((((Bᴴ)ᵀ)ᴴ)ᵀ : Matrix (Fin g) (Fin g) ℂ) = B := by
    ext i j
    simp [Matrix.transpose_apply, Matrix.conjTranspose_apply]
  rw [Matrix.star_mulVec, ← Matrix.mulVec_transpose, ← Matrix.vecMul_transpose ((Bᴴ)ᵀ) z',
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.transpose_transpose, hT, hB]

theorem exists_coords_of_injective {V E : Type*} [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (L : V →ₗ[ℂ] E) (hinj : Function.Injective L) (m : ℕ) (W : Submodule ℂ V)
    (hW : Module.finrank ℂ W = m) :
    ∃ c : V →ₗ[ℂ] (Fin m → ℂ), ∀ z ∈ W, ∀ z' ∈ W,
      innerₛₗ ℂ (L z) (L z') = ∑ i, starRingEnd ℂ (c z i) * c z' i := by
  let W' : Submodule ℂ E := W.map L
  have hm : Module.finrank ℂ W' = m := by
    rw [← hW]
    exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective L hinj W)).symm
  let b : OrthonormalBasis (Fin m) ℂ W' := (stdOrthonormalBasis ℂ W').reindex (finCongr hm)
  refine ⟨LinearMap.pi fun i => innerₛₗ ℂ (b i : E) ∘ₗ L, fun z hz z' hz' => ?_⟩
  have key := b.sum_inner_mul_inner (⟨L z, Submodule.mem_map_of_mem hz⟩ : W')
    ⟨L z', Submodule.mem_map_of_mem hz'⟩
  simp only [Submodule.coe_inner] at key
  rw [innerₛₗ_apply_apply, ← key]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [LinearMap.pi_apply, LinearMap.comp_apply, innerₛₗ_apply_apply, inner_conj_symm]

theorem exists_coords (g m : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm *ᵥ star z).re)
    (W : Submodule ℂ (Fin g → ℂ)) (hW : Module.finrank ℂ W = m) :
    ∃ c : (Fin g → ℂ) →ₗ[ℂ] (Fin m → ℂ), ∀ z ∈ W, ∀ z' ∈ W,
      z' ⬝ᵥ Hm *ᵥ star z = ∑ i, starRingEnd ℂ (c z i) * c z' i := by
  obtain ⟨T, hT⟩ := GlobalTheory.CompanionTheory.Ar.HermCoords.exists_factor
    (GlobalTheory.CompanionTheory.Ar.HermCoords.posDef_of_re_pos hH hpos)
  let L : (Fin g → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin g) :=
    (WithLp.linearEquiv 2 ℂ (Fin g → ℂ)).symm.toLinearMap ∘ₗ Matrix.mulVecLin T
  have hL : ∀ z z', innerₛₗ ℂ (L z) (L z') = z' ⬝ᵥ Hm *ᵥ star z := by
    intro z z'
    rw [hT, innerₛₗ_apply_apply, EuclideanSpace.inner_eq_star_dotProduct]
    first
    | rfl
    | simp [L]
  have hinj : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).2 fun z hz => ?_
    by_contra hne
    have h1 := hpos z hne
    rw [← hL z z, hz] at h1
    simp at h1
  obtain ⟨c, hc⟩ := GlobalTheory.CompanionTheory.Ar.HermCoords.exists_coords_of_injective L hinj m W hW
  exact ⟨c, fun z hz z' hz' => by rw [← hL, hc z hz z' hz']⟩

end GlobalTheory.CompanionTheory.Ar.HermCoords
