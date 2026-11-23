import Formalism.HermitianCurvature.HermitianCurvatureProofs.MinorCellOfParts

open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.GaugeNormPower

open Formalism.QuantumDeterminants

theorem hasDerivAt_normPow (z v : ℂ) (hz : z ≠ 0) (n : ℕ) :
    HasDerivAt (fun t : ℝ => ‖z + t • v‖ ^ n)
      ((n : ℝ) * ‖z‖ ^ n * ((v * conj z).re / ‖z‖ ^ 2)) 0 := by
  have hz' : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hline : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have hsq : HasDerivAt (fun t : ℝ => ‖z + t • v‖ ^ 2) (2 * (v * conj z).re) 0 := by
    have := hline.norm_sq
    simpa [Complex.inner] using this
  have h0 : (fun t : ℝ => ‖z + t • v‖ ^ 2) 0 ≠ 0 := by simpa using pow_ne_zero 2 hz'
  have hsqrt := hsq.sqrt h0
  have hn : (fun t : ℝ => √(‖z + t • v‖ ^ 2)) = fun t => ‖z + t • v‖ := by
    funext t; rw [Real.sqrt_sq (norm_nonneg _)]
  rw [hn] at hsqrt
  have hv : (n : ℝ) * ‖z + (0 : ℝ) • v‖ ^ (n - 1) * (2 * (v * conj z).re / (2 * √(‖z + (0 : ℝ) • v‖ ^ 2))) =
      (n : ℝ) * ‖z‖ ^ n * ((v * conj z).re / ‖z‖ ^ 2) := by
    simp only [zero_smul, add_zero, Real.sqrt_sq (norm_nonneg _)]
    rcases n with _ | m
    · simp
    · simp only [Nat.add_sub_cancel]
      push_cast
      field_simp
      ring
  have hp := (hsqrt.pow n).congr_deriv hv
  exact hp

theorem hasDerivAt_prodPow (r : ℕ) (n : Fin r → ℕ) (c : Fin r → ℂ) (hc : c ∈ OmX r) (l : Fin r) (v : ℂ) :
    HasDerivAt (fun t : ℝ => ∏ a, ‖(c + t • (Pi.single l v : Fin r → ℂ)) a‖ ^ n a)
      ((n l : ℝ) * (∏ a, ‖c a‖ ^ n a) * ((v * conj (c l)).re / ‖c l‖ ^ 2)) 0 := by
  classical
  have h := HasDerivAt.fun_finsetProd (u := Finset.univ)
    (f := fun a (t : ℝ) => ‖c a + t • (Pi.single l v : Fin r → ℂ) a‖ ^ n a)
    (fun a _ => hasDerivAt_normPow (c a) ((Pi.single l v : Fin r → ℂ) a) (hc a) (n a))
  have hv : (∑ i, (∏ j ∈ Finset.univ.erase i, ‖c j + (0 : ℝ) • (Pi.single l v : Fin r → ℂ) j‖ ^ n j) •
        ((n i : ℝ) * ‖c i‖ ^ n i * (((Pi.single l v : Fin r → ℂ) i * conj (c i)).re / ‖c i‖ ^ 2))) =
      (n l : ℝ) * (∏ a, ‖c a‖ ^ n a) * ((v * conj (c l)).re / ‖c l‖ ^ 2) := by
    rw [Finset.sum_eq_single l]
    · simp only [Pi.single_eq_same, zero_smul, add_zero, smul_eq_mul]
      rw [← Finset.mul_prod_erase Finset.univ (fun a => ‖c a‖ ^ n a) (Finset.mem_univ l)]
      ring
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · intro h; exact absurd (Finset.mem_univ l) h
  exact h.congr_deriv hv

theorem fderiv_prodPow (r : ℕ) (n : Fin r → ℕ) (c : Fin r → ℂ) (hc : c ∈ OmX r) (l : Fin r) (v : ℂ) :
    DifferentiableAt ℝ (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) c ∧
    fderiv ℝ (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) c (Pi.single l v) =
      (n l : ℝ) * (∏ a, ‖c a‖ ^ n a) * ((v * conj (c l)).re / ‖c l‖ ^ 2) := by
  classical
  have hd : DifferentiableAt ℝ (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) c := by
    have := HasFDerivAt.finsetProd (u := Finset.univ) (x := c)
      (g := fun a (x : Fin r → ℂ) => ‖x a‖ ^ n a)
      (fun a _ => (((differentiableAt_apply (𝕜 := ℝ) a c).norm ℂ (hc a)).pow (n a)).hasFDerivAt)
    exact this.differentiableAt
  refine ⟨hd, ?_⟩
  have hline : HasDerivAt (fun t : ℝ => c + t • (Pi.single l v : Fin r → ℂ)) (Pi.single l v) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single l v : Fin r → ℂ)).const_add c
  have hc0 : c + (0 : ℝ) • (Pi.single l v : Fin r → ℂ) = c := by simp
  have h1 : HasDerivAt ((fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) ∘ fun t : ℝ => c + t • (Pi.single l v : Fin r → ℂ))
      (fderiv ℝ (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) c (Pi.single l v)) 0 := by
    have hd' := hd.hasFDerivAt
    rw [← hc0] at hd'
    have := hd'.comp_hasDerivAt (0 : ℝ) hline
    rwa [hc0] at this
  exact h1.unique (hasDerivAt_prodPow r n c hc l v)

theorem gauge_scalar (z : ℂ) (hz : z ≠ 0) (m : ℕ) (P : ℝ) :
    z * ((1 / 2 : ℂ) * ((((m : ℝ) * P * ((1 * conj z).re / ‖z‖ ^ 2) : ℝ) : ℂ) -
      Complex.I * (((m : ℝ) * P * ((Complex.I * conj z).re / ‖z‖ ^ 2) : ℝ) : ℂ))) = (P : ℂ) * ((m : ℂ) / 2) := by
  have h1 : (1 * conj z).re = z.re := by simp
  have h2 : (Complex.I * conj z).re = z.im := by simp
  have hc : ((z.re : ℂ)) - Complex.I * (z.im : ℂ) = conj z := by apply Complex.ext <;> simp
  have hzz : z * conj z = (‖z‖ : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hN0 : (‖z‖ : ℂ) ^ 2 ≠ 0 := by exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  rw [h1, h2]
  push_cast
  calc _ = ((m : ℂ) * P / 2) * (z * ((z.re : ℂ) - Complex.I * (z.im : ℂ))) / (‖z‖ : ℂ) ^ 2 := by ring
    _ = (P : ℂ) * ((m : ℂ) / 2) := by
      have hN1 : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
      rw [hc, hzz]; field_simp

end Formalism.FourierDecayAlt.P.GaugeNormPower

namespace Formalism.FourierDecayAlt.P

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.GaugeNormPower

theorem gauge_positivity : PBN.GaugeP := by
  intro E _ _ r n H c hc hH l
  obtain ⟨hψ, hψ'⟩ := fderiv_prodPow r n c hc l 1
  obtain ⟨-, hψI⟩ := fderiv_prodPow r n c hc l Complex.I
  have hfun : (fun c' : Fin r → ℂ => ((∏ a, ‖c' a‖ ^ n a : ℝ) : ℂ) • H c') =
      (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) • H := by
    funext c'; exact Complex.coe_smul _ _
  rw [hfun]
  have hD : ∀ w, fderiv ℝ ((fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) • H) c w =
      (∏ a, ‖c a‖ ^ n a) • fderiv ℝ H c w + fderiv ℝ (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) c w • H c := by
    intro w
    rw [(hψ.hasFDerivAt.smul hH.hasFDerivAt).fderiv]
    simp
  have hs : c l * ((1 / 2 : ℂ) * (((fderiv ℝ (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) c (Pi.single l 1) : ℝ) : ℂ) -
      Complex.I * ((fderiv ℝ (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) c (Pi.single l Complex.I) : ℝ) : ℂ))) =
      ((∏ a, ‖c a‖ ^ n a : ℝ) : ℂ) * ((n l : ℂ) / 2) := by
    rw [hψ', hψI]
    exact gauge_scalar (c l) (hc l) (n l) _
  simp only [pOp, if_pos hc, wirt]
  rw [hD, hD]
  simp only [← Complex.coe_smul]
  linear_combination (norm := module) hs • H c

end Formalism.FourierDecayAlt.P
