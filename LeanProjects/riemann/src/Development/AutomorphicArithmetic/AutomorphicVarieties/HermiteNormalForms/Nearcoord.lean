import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.DetPull
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Cramer
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Scinv
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Rypos

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.nearcoord :
    ∀ (L : Type) [Field L] [NumberField L] [IsTotallyComplex L] (N : ℕ) (A B : Matrix (Fin N) (Fin N) (𝓞 L)), A.det ≠ 0 →
    A * B = ((nrmDet A : ℕ) : 𝓞 L) • (1 : Matrix (Fin N) (Fin N) (𝓞 L)) → ∀ y ∈ nearVec A, ∀ w a, ‖embO w ((B *ᵥ y) a)‖ ≤ RR L N := by
  intro L _ _ _ N A B hA hAB y hy w a
  obtain ⟨h, hRy, hcol, hq⟩ := hy
  obtain ⟨hI, hpl⟩ := nrmle L N h A hRy hcol hA
  obtain ⟨hpsd, hdiag, hdet⟩ := hpl w
  have hdpos : 0 < nrmDet A := (scinv L N A hA).1
  have hAx : A *ᵥ (B *ᵥ y) = fun i => ((nrmDet A : ℕ) : 𝓞 L) * y i := by
    rw [Matrix.mulVec_mulVec, hAB]
    ext i
    simp [Matrix.smul_mulVec]
  have hq2 : q (pull A h) (B *ᵥ y) = ((nrmDet A : ℕ) : ℝ) ^ 2 := by
    rw [q_pull, hAx]
    unfold q qR toR at hq ⊢
    rw [← mul_one (((nrmDet A : ℕ) : ℝ) ^ 2), ← hq, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    have e : (fun i => embO v (((nrmDet A : ℕ) : 𝓞 L) * y i)) = (((nrmDet A : ℕ) : ℝ) : ℂ) • (fun i => embO v (y i)) := by
      ext i; simp
    rw [e, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
    simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
    ring
  set d : ℝ := ((nrmDet A : ℕ) : ℝ) with hd
  have hd0 : 0 < d := by rw [hd]; exact_mod_cast hdpos
  set xw : Fin N → ℂ := fun i => embO w ((B *ᵥ y) i) with hxw
  set G := mat (pull A h) w with hG
  have hterm : (star xw ⬝ᵥ G *ᵥ xw).re ≤ d ^ 2 := by
    rw [← hq2]
    unfold q qR toR
    exact Finset.single_le_sum (f := fun v => (star (fun i => embO v ((B *ᵥ y) i)) ⬝ᵥ mat (pull A h) v *ᵥ fun i => embO v ((B *ᵥ y) i)).re)
      (fun v _ => (Complex.le_def.mp ((hpl v).1.dotProduct_mulVec_nonneg _)).1) (Finset.mem_univ w)
  set c : Fin N → ℂ := ((d⁻¹ : ℝ) : ℂ) • xw with hc
  have hcq : (star c ⬝ᵥ G *ᵥ c).re ≤ 1 := by
    rw [hc, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
    simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
    have : d⁻¹ * d⁻¹ * (star xw ⬝ᵥ G *ᵥ xw).re ≤ d⁻¹ * d⁻¹ * d ^ 2 := by
      apply mul_le_mul_of_nonneg_left hterm; positivity
    calc _ ≤ d⁻¹ * d⁻¹ * d ^ 2 := this
      _ = 1 := by field_simp
  have hcr := cramer N G c hpsd hdiag hcq a
  have hca : ‖xw a‖ = d * ‖c a‖ := by
    rw [hc, Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hd0, ← mul_assoc, mul_inv_cancel₀ hd0.ne', one_mul]
  have hdI : d ≤ (I0 L N : ℝ) := by rw [hd]; exact_mod_cast hI
  have hn : 0 ≤ ‖c a‖ := norm_nonneg _
  have hdn : 0 ≤ ‖G.det‖ := norm_nonneg _
  have hcb : ‖c a‖ ≤ (I0 L N : ℝ) * (N : ℝ) ^ N := by
    calc ‖c a‖ ≤ ‖c a‖ * ((I0 L N : ℝ) * ‖G.det‖) := le_mul_of_one_le_right hn hdet
      _ = (I0 L N : ℝ) * (‖G.det‖ * ‖c a‖) := by ring
      _ ≤ (I0 L N : ℝ) * (N : ℝ) ^ N := mul_le_mul_of_nonneg_left hcr (by positivity)
  show ‖xw a‖ ≤ (RR L N : ℝ)
  rw [hca]
  unfold RR
  push_cast
  calc d * ‖c a‖ ≤ (I0 L N : ℝ) * ((I0 L N : ℝ) * (N : ℝ) ^ N) := mul_le_mul hdI hcb hn (by positivity)
    _ = (N : ℝ) ^ N * (I0 L N : ℝ) ^ 2 := by ring
