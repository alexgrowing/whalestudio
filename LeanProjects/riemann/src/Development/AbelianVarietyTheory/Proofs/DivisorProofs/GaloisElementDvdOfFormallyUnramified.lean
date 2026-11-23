import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFreeOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalMapGalElt
open scoped TensorProduct

namespace GlobalTheory.GoodEtale

theorem galElt_dvd_of_unramified : ∀ (R C O : Type) [CommRing R] [CommRing C] [Algebra R C] [CommRing O] [Algebra R O]
    [Algebra.FormallyUnramified O (O ⊗[R] C)] [Algebra.EssFiniteType O (O ⊗[R] C)]
    (G : Type) [Group G] [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (b : R) (n : ℕ) (x y : Fin n → C),
      (∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C b else 0) →
    ∀ σ : C →ₐ[R] O, Function.Injective (GlobalTheory.GoodEtale.galMap act σ) →
    ∀ h : G, ∃ m' : O ⊗[R] C, GlobalTheory.GoodEtale.galElt act σ x y h = algebraMap R O b • m' := by
  intro R C O _ _ _ _ _ _ _ G _ _ act b n x y hxy σ hinj h
  obtain ⟨t, ht1, ht2⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := O) (S := O ⊗[R] C)).mp inferInstance
  let τ : O ⊗[R] C →ₐ[O] O := (Pi.evalAlgHom O (fun _ : G => O) h).comp (galMap act σ)
  let ψ : (O ⊗[R] C) ⊗[O] (O ⊗[R] C) →ₐ[O] O ⊗[R] C :=
    Algebra.TensorProduct.lift (AlgHom.id O _) ((Algebra.ofId O (O ⊗[R] C)).comp τ) (fun _ _ => Commute.all _ _)
  have hψ : ∀ a c, ψ (a ⊗ₜ c) = a * algebraMap O (O ⊗[R] C) (τ c) := by
    intro a c; simp [ψ]
  set e := ψ t with he

  have hi : ∀ s, s * e = algebraMap O (O ⊗[R] C) (τ s) * e := by
    intro s
    have := congrArg ψ (ht1 s)
    rw [map_mul, map_sub, hψ, hψ, map_zero] at this
    simp only [map_one, one_mul, mul_one] at this
    rw [← he] at this
    rw [sub_mul, sub_eq_zero] at this
    exact this.symm

  have hii : τ e = 1 := by
    have hcomp : τ.comp ψ = τ.comp (Algebra.TensorProduct.lmul' O) := by
      apply Algebra.TensorProduct.ext'
      intro a c
      simp only [AlgHom.comp_apply, hψ, map_mul, AlgHom.commutes, Algebra.TensorProduct.lmul'_apply_tmul]
      simp only [Algebra.algebraMap_self, RingHom.id_apply]
    have := congrArg (fun f => f t) hcomp
    simp only [AlgHom.comp_apply] at this
    rw [he, this, ht2, map_one]

  have hfix : galElt act σ x y h * e = galElt act σ x y h := by
    apply hinj
    rw [map_mul, galMap_galElt act σ x y b hxy h]
    funext g
    by_cases hg : g = h
    · subst hg
      have : galMap act σ e g = τ e := rfl
      simp [this, hii]
    · simp [Pi.single_apply, hg]
  refine ⟨e, ?_⟩
  rw [← hfix]
  simp only [galElt, Finset.sum_mul]
  have hterm : ∀ i, σ (x i) ⊗ₜ[R] act h⁻¹ (y i) * e = algebraMap O (O ⊗[R] C) (σ (x i) * σ (y i)) * e := by
    intro i
    have hsplit : σ (x i) ⊗ₜ[R] act h⁻¹ (y i) = algebraMap O (O ⊗[R] C) (σ (x i)) * ((1 : O) ⊗ₜ[R] act h⁻¹ (y i)) := by
      simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
    rw [hsplit, mul_assoc, hi, ← mul_assoc, ← map_mul]
    congr 3
    have : τ ((1 : O) ⊗ₜ[R] act h⁻¹ (y i)) = σ (act h (act h⁻¹ (y i))) := by
      simp [τ, galMap_tmul]
    rw [this]
    congr 2
    rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgEquiv.one_apply]
  simp_rw [hterm, ← Finset.sum_mul, ← map_sum, ← map_mul, ← map_sum]
  have h1 := hxy 1
  simp only [map_one, AlgEquiv.one_apply, if_true] at h1
  rw [h1, AlgHom.commutes, Algebra.smul_def]

end GlobalTheory.GoodEtale
