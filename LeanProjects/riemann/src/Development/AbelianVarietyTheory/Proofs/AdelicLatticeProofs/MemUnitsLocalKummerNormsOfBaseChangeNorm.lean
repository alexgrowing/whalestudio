import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.KummerGalois
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem isUnit_of_norm_ne_zero {L A : Type} [Field L] [CommRing A] [Algebra L A]
    [Module.Finite L A] (y : A) (h : Algebra.norm L y ≠ 0) : IsUnit y := by
  have h1 : IsUnit (Algebra.lmul L A y) := by
    rw [LinearMap.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr (by rwa [Algebra.norm_apply] at h)
  obtain ⟨z, hz⟩ := ((Module.End.isUnit_iff _).mp h1).surjective 1
  exact IsUnit.of_mul_eq_one z (by simpa using hz)

theorem IsKum.nonempty_tensor_equiv {p : ℕ} {F E : Type} [Field F] [Field E] [Algebra F E]
    {ζ δ : F} {θ : E} {σ : E ≃ₐ[F] E} (h : IsKum p ζ δ θ σ) (L : Type) [Field L] [Algebra F L] :
    Nonempty ((L ⊗[F] E) ≃ₐ[L] AdjoinRoot (X ^ p - C (algebraMap F L δ) : L[X])) := by
  have hp := h.prime
  have hmin := h.minpoly_eq
  have hint : IsIntegral F θ :=
    ⟨X ^ p - C δ, monic_X_pow_sub_C δ hp.ne_zero, by simp [h.pow]⟩
  let pb : PowerBasis F E := PowerBasis.ofAdjoinEqTop hint h.gen
  have hgen : pb.gen = θ := PowerBasis.ofAdjoinEqTop_gen hint h.gen
  set g : L[X] := X ^ p - C (algebraMap F L δ) with hg
  have hroot : AdjoinRoot.root g ^ p = algebraMap F (AdjoinRoot g) δ := by
    have := AdjoinRoot.eval₂_root g
    rw [hg, eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at this
    rw [IsScalarTower.algebraMap_apply F L (AdjoinRoot g)]
    exact this
  let ψ : E →ₐ[F] AdjoinRoot g := pb.lift (AdjoinRoot.root g) (by
    rw [hgen, hmin]; simp [hroot])
  have hψ : ψ θ = AdjoinRoot.root g := (congrArg _ hgen.symm).trans (pb.lift_gen _ _)
  let a : (L ⊗[F] E) →ₐ[L] AdjoinRoot g :=
    Algebra.TensorProduct.lift (Algebra.ofId L _) ψ (fun _ _ => Commute.all _ _)
  let b : AdjoinRoot g →ₐ[L] (L ⊗[F] E) :=
    AdjoinRoot.liftAlgHom g (Algebra.ofId L _) ((1 : L) ⊗ₜ[F] θ) (by
      rw [hg, eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero, Algebra.TensorProduct.tmul_pow,
        one_pow, h.pow]
      change _ = algebraMap L (L ⊗[F] E) (algebraMap F L δ)
      rw [← IsScalarTower.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply',])
  have hb : b (AdjoinRoot.root g) = (1 : L) ⊗ₜ[F] θ := AdjoinRoot.liftAlgHom_root ..
  have ha : a ((1 : L) ⊗ₜ[F] θ) = AdjoinRoot.root g := by
    simp [a, hψ]
  refine ⟨AlgEquiv.ofAlgHom a b ?_ ?_⟩
  · apply AdjoinRoot.algHom_ext
    simp [ha, hb]
  · apply Algebra.TensorProduct.ext
    · exact Subsingleton.elim _ _
    · apply pb.algHom_ext
      rw [hgen]
      simp [ha, hb]

theorem mem_kNorm_of_tNorm : ∀ (p : ℕ) (F E L : Type) [Field F] [CharZero F] [Field E] [Algebra F E] [Field L] [Algebra F L] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → ∀ x : Fˣ, TNorm F E L (x : F) → x ∈ kNorm p (algebraMap F L) δ := by
  intro p F E L _ _ _ _ _ _ ζ δ θ σ h x ⟨y, hy⟩
  obtain ⟨e⟩ := h.nonempty_tensor_equiv L
  have : Module.Finite L (AdjoinRoot (X ^ p - C (algebraMap F L δ) : L[X])) :=
    (AdjoinRoot.powerBasis' (monic_X_pow_sub_C _ h.prime.ne_zero)).finite
  have hn : Algebra.norm L (e y) = algebraMap F L x := by
    rw [Algebra.norm_eq_of_algEquiv, hy]
  have hu : IsUnit (e y) := isUnit_of_norm_ne_zero _ (by
    rw [hn]; exact (_root_.map_ne_zero _).mpr x.ne_zero)
  rw [mem_kNorm]
  exact ⟨hu.unit, hn⟩

end GlobalTheory.CNorm
