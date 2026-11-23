import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnitFormC
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.MapLk

open Finset UpperTheory.V.Sd

namespace UpperTheory.V.Z.Sym.Unl

private theorem gauss_mul_gauss_inv {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar * χ (-1) = N := by
  have hi : (χ⁻¹).IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]; exact hχ
  have h1 : ZMod.dft (χ : ZMod N → ℂ) = fun k => χ⁻¹ (-k) * gaussSum χ ZMod.stdAddChar :=
    funext fun k => hχ.fourierTransform_eq_inv_mul_gaussSum k
  have h2 := congrFun (ZMod.dft_dft (χ : ZMod N → ℂ)) (-1)
  rw [h1, ZMod.dft_mul_const (fun k => χ⁻¹ (-k)), ZMod.dft_comp_neg (fun k => χ⁻¹ k)] at h2
  simp only [neg_neg, map_one, smul_eq_mul, mul_one] at h2
  have h3 := hi.fourierTransform_eq_inv_mul_gaussSum 1
  rw [inv_inv] at h3
  have h4 : ZMod.dft (fun k => χ⁻¹ k) 1 = χ (-1) * gaussSum χ⁻¹ ZMod.stdAddChar := h3
  rw [h4] at h2
  rw [← h2]; ring

private theorem gauss_inv_ne {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    gaussSum χ⁻¹ ZMod.stdAddChar ≠ 0 := by
  intro h
  have := gauss_mul_gauss_inv χ hχ
  rw [h, mul_zero, zero_mul] at this
  exact (NeZero.ne N) (by exact_mod_cast this.symm)

private theorem map_Lk (σ : ℂ ≃+* ℂ) (k : ℕ) (x : ℂ) : σ (Lk k x) = Lk k (σ x) := by
  unfold Lk
  rw [map_div₀, map_pow, map_sub, map_one]
  congr 1
  exact (Polynomial.aeval_algHom_apply (σ.toRingHom.toIntAlgHom) x (numL k)).symm

private theorem cj_inv_apply {N : ℕ} (σ : ℂ ≃+* ℂ) (χ : DirichletCharacter ℂ N) (a : ZMod N) :
    σ (χ⁻¹ a) = (cj σ χ)⁻¹ a := by
  rw [MulChar.inv_apply, MulChar.inv_apply]
  rfl

private theorem sum_conj {N : ℕ} [NeZero N] (σ : ℂ ≃+* ℂ) (χ : DirichletCharacter ℂ N) (s : (ZMod N)ˣ)
    (hs : ∀ b : ZMod N, σ (ZMod.stdAddChar b : ℂ) = (ZMod.stdAddChar ((s : ZMod N) * b) : ℂ))
    (F : ℂ → ℂ) (hF : ∀ x, σ (F x) = F (σ x)) :
    σ (∑ a : ZMod N, χ⁻¹ a * F (ZMod.stdAddChar a : ℂ)) =
      (cj σ χ)⁻¹ ((s⁻¹ : (ZMod N)ˣ) : ZMod N) * ∑ a : ZMod N, (cj σ χ)⁻¹ a * F (ZMod.stdAddChar a : ℂ) := by
  rw [map_sum, Finset.mul_sum]
  refine Fintype.sum_equiv (Units.mulLeft s) _ _ fun a => ?_
  have hu : (Units.mulLeft s a : ZMod N) = (s : ZMod N) * a := rfl
  rw [map_mul, hF, hs, cj_inv_apply, hu, ← mul_assoc, ← map_mul, ← mul_assoc, Units.inv_mul, one_mul]

theorem constCj : ConstCj := by
  intro N k _ hN χ hχ σ c c' h1 h2
  obtain ⟨s, hs, -⟩ := eisCj N hN σ
  have hG := sum_conj σ χ s hs id (fun _ => rfl)
  have hS := sum_conj σ χ s hs (Lk k) (map_Lk σ k)
  simp only [id] at hG
  have hG' : σ (gaussSum χ⁻¹ ZMod.stdAddChar) =
      (cj σ χ)⁻¹ ((s⁻¹ : (ZMod N)ˣ) : ZMod N) * gaussSum (cj σ χ)⁻¹ ZMod.stdAddChar := hG
  have hne : (cj σ χ)⁻¹ ((s⁻¹ : (ZMod N)ˣ) : ZMod N) * gaussSum (cj σ χ)⁻¹ ZMod.stdAddChar ≠ 0 := by
    rw [← hG']
    exact (map_ne_zero σ).2 (gauss_inv_ne χ hχ)
  have h3 := congrArg σ h1
  rw [hS, ← h2, map_mul, map_mul, hG', map_ofNat] at h3
  have h4 : ((cj σ χ)⁻¹ ((s⁻¹ : (ZMod N)ˣ) : ZMod N) * gaussSum (cj σ χ)⁻¹ ZMod.stdAddChar) * (2 * σ c) =
      ((cj σ χ)⁻¹ ((s⁻¹ : (ZMod N)ˣ) : ZMod N) * gaussSum (cj σ χ)⁻¹ ZMod.stdAddChar) * (2 * c') := by
    linear_combination h3
  have h5 := mul_left_cancel₀ hne h4
  have h6 : (2 : ℂ) ≠ 0 := two_ne_zero
  exact (mul_left_cancel₀ h6 h5).symm

end UpperTheory.V.Z.Sym.Unl
