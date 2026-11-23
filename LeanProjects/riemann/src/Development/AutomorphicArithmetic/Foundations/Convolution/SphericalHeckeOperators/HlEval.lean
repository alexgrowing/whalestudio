import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

private theorem he_single {n : ℕ} (i : Fin n) (m : ℤ) (w : Fin n → ℂˣ) : monomialChar (Pi.single i m : Fin n → ℤ) w = (w i : ℂ) ^ m := by
  rw [monomialChar_apply, Finset.prod_eq_single i] <;> simp +contextual [Pi.single_apply]

private theorem he_d {n : ℕ} (w : Fin n → ℂˣ) : evalAt w (dPol n 1) = ∏ p ∈ pairs n, ((w p.1 : ℂ) - w p.2) := by
  rw [dPol, map_prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [map_sub, one_smul, evalAt_single, evalAt_single, he_single, he_single]
  simp

private theorem he_det {n : ℕ} (w : Fin n → ℂˣ) :
    evalAt w (dPol n 1) = (Matrix.projVandermonde (fun _ => (1 : ℂ)) fun i => (w i : ℂ)).det := by
  rw [he_d, Matrix.det_projVandermonde, Finset.prod_sigma', pairs]
  refine Finset.prod_nbij' (fun p => ⟨p.1, p.2⟩) (fun p => (p.1, p.2)) ?_ ?_ ?_ ?_ ?_ <;> simp

private theorem he_alt {n : ℕ} (w : Fin n → ℂˣ) : evalAt w (alternant (staircase n)) = evalAt w (dPol n 1) := by
  rw [he_det, alternant_eq_det, AlgHom.map_det]
  congr 1
  ext a b
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, monomial, evalAt_single, he_single, one_mul,
    Matrix.projVandermonde_apply, one_pow]
  rw [← zpow_natCast]
  congr 1
  have := b.2
  simp only [staircase, Fin.val_rev]
  omega

private theorem he_sgn {n : ℕ} (w : Fin n → ℂˣ) (σ : Equiv.Perm (Fin n)) :
    evalAt (w ∘ σ) (dPol n 1) = ((Equiv.Perm.sign σ : ℤ) : ℂ) * evalAt w (dPol n 1) := by
  rw [he_det, he_det, ← Matrix.det_permute]
  rfl

theorem UpperTheory.ConvolutionTheory.H.hlEval :
    ∀ (n : ℕ) (t : ℂ) (z : Fin n → ℂˣ), Function.Injective z → ∀ a : Fin n → ℤ,
      (∀ σ : Equiv.Perm (Fin n), evalAt (z ∘ σ) (dPol n 1) ≠ 0) ∧
      evalAt z (hlR t a) = ∑ σ : Equiv.Perm (Fin n), evalAt (z ∘ σ) (dPol n t) / evalAt (z ∘ σ) (dPol n 1) * monomialChar a (z ∘ σ) := by
  intro n t z hz a
  have hne : ∀ σ : Equiv.Perm (Fin n), evalAt (z ∘ σ) (dPol n 1) ≠ 0 := fun σ => by
    rw [he_d]
    refine Finset.prod_ne_zero_iff.2 fun p hp => sub_ne_zero.2 fun h => ?_
    have h1 : p.1 < p.2 := by simpa [pairs] using hp
    exact h1.ne (σ.injective (hz (Units.ext h)))
  refine ⟨hne, ?_⟩
  have h1 := congrArg (evalAt z) (alternant_mul_altQuot (monomial a * hlFactor n t))
  rw [map_mul, he_alt, antisymm_apply, map_sum] at h1
  have h0 : evalAt z (dPol n 1) ≠ 0 := hne 1
  refine mul_left_cancel₀ h0 (h1.trans ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h2 := he_sgn z σ
  have h3 := hne σ
  rw [Units.smul_def, map_zsmul, evalAt_permAct, map_mul, monomial, evalAt_single, one_mul, zsmul_eq_mul]
  have h4 : ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign σ : ℤ) : ℂ) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have h5 : evalAt z (dPol n 1) = ((Equiv.Perm.sign σ : ℤ) : ℂ) * evalAt (z ∘ σ) (dPol n 1) := by
    rw [h2, ← mul_assoc, h4, one_mul]
  rw [h5]
  change _ * (_ * evalAt (z ∘ σ) (dPol n t)) = _
  field_simp
