import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSlashRationalMatrixProperties
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsRealMatrixForLatticeAndDualWithDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPosGramFormIntegralLatticeProperties
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.PoissonSummationGaussianConstantOnEvenBlocks
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.WCos
open UpperHalfPlane hiding I

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

noncomputable def sg (v : InfinitePlace F) : F →+* ℝ := (Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) v).comp rhom

theorem reAt_eq (v : InfinitePlace F) (x : F) : reAt v x = sg v x :=
  ((GlobalTheory.T.hilbert_slash_rational_matrix_properties F 0 (fun _ => 0)).1 v x).symm

theorem cmp_wm (c : Fˣ) (v : InfinitePlace F) (i j : Fin 2) :
    ((HilbertThetaSeries.cmp v (toInf (wm c)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j
      = sg v (((wm c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j) := rfl

theorem sg_ne (c : Fˣ) (v : InfinitePlace F) : sg v (c : F) ≠ 0 := (map_ne_zero _).2 c.ne_zero

theorem denom_wm (c : Fˣ) (v : InfinitePlace F) (z : ℂ) :
    denom (HilbertThetaSeries.cmp v (toInf (wm c))) z = (sg v (c : F) : ℂ) * z := by
  unfold denom
  rw [cmp_wm, cmp_wm]
  simp [wm]

theorem act_wm (c : Fˣ) (z : Hn F) (v : InfinitePlace F) :
    ((act (toInf (wm c)) z v : ℍ) : ℂ) = -((sg v (c : F) : ℂ) ^ 2 * (z v : ℂ))⁻¹ := by
  have hc : (sg v (c : F) : ℂ) ≠ 0 := by exact_mod_cast sg_ne c v
  have hz : ((z v : ℍ) : ℂ) ≠ 0 := (z v).ne_zero
  unfold HilbertThetaSeries.act
  rw [coe_smul_of_det_pos, denom_wm]
  · unfold num
    rw [cmp_wm, cmp_wm]
    simp [wm]
    field_simp
  · rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, cmp_wm, cmp_wm, cmp_wm, cmp_wm]
    simp [wm]

theorem ez_QF {κ : Type} [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ) (e : (κ → F) →+ (InfinitePlace F × κ → ℝ))
    (he : ∀ x y v, ∑ i, e x (v, i) * e y (v, i) = reAt v (BF G x y)) (b : F) (x : κ → F) (w : Hn F) :
    ez (b * QF G x) w = Complex.exp (Real.pi * Complex.I * ∑ j : InfinitePlace F × κ,
      ((sg j.1 b : ℂ) * (w j.1 : ℂ)) * ((e x j : ℝ) : ℂ) ^ 2) := by
  unfold ez QF
  congr 1
  rw [Fintype.sum_prod_type, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [reAt_eq, map_mul, map_div₀, map_ofNat, ← reAt_eq v (BF G x x), ← he]
  dsimp only
  rw [← Finset.mul_sum]
  push_cast
  simp only [sq]
  ring

theorem et_BF {κ : Type} [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ) (e : (κ → F) →+ (InfinitePlace F × κ → ℝ))
    (he : ∀ x y v, ∑ i, e x (v, i) * e y (v, i) = reAt v (BF G x y)) (x y : κ → F) :
    et (BF G x y) = Complex.exp (2 * Real.pi * Complex.I * ∑ j : InfinitePlace F × κ, ((e x j * e y j : ℝ) : ℂ)) := by
  unfold et
  congr 2
  rw [← Complex.ofReal_ratCast, ← ((GlobalTheory.T.hilbert_slash_rational_matrix_properties F 0 (fun _ => 0)).2.2.2.2 (BF G x y)).2, ← Complex.ofReal_sum,
    Fintype.sum_prod_type]
  simp only [he]

theorem const_eq (k t : ℕ) (a : F) (c : Fˣ) (z : Hn F) (d : ℝ)
    (hd : d = ((Algebra.norm ℚ a : ℚ) : ℝ) ^ (2 * k) * ((discr F).natAbs : ℝ) ^ k * (t : ℝ) ^ Module.finrank ℚ F) :
    (∏ v, (sg v (c : F) : ℂ) * (z v : ℂ))⁻¹ ^ k * ((d : ℂ)⁻¹ * (∏ v, -Complex.I * ((sg v (c : F) : ℂ) ^ 2 * (z v : ℂ))) ^ k)
      = wC k t a (c : F) := by
  have hP : (∏ v, (sg v (c : F) : ℂ) * (z v : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ => mul_ne_zero (by exact_mod_cast sg_ne c v) (z v).ne_zero
  have hcard : Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, ← InfinitePlace.card_add_two_mul_card_eq_rank,
      IsTotallyReal.nrComplexPlaces_eq_zero]
  have hN : (∏ v, (sg v (c : F) : ℂ)) = ((Algebra.norm ℚ (c : F) : ℚ) : ℂ) := by
    rw [← Complex.ofReal_ratCast, ← ((GlobalTheory.T.hilbert_slash_rational_matrix_properties F 0 (fun _ => 0)).2.2.2.2 (c : F)).1, Complex.ofReal_prod]
    simp only [reAt_eq]
  have h : (∏ v, -Complex.I * ((sg v (c : F) : ℂ) ^ 2 * (z v : ℂ)))
      = (-Complex.I) ^ Module.finrank ℚ F * ((Algebra.norm ℚ (c : F) : ℚ) : ℂ) * ∏ v, (sg v (c : F) : ℂ) * (z v : ℂ) := by
    rw [← hN, ← hcard, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v _ => by ring
  rw [h, hd, wC]
  generalize (∏ v, (sg v (c : F) : ℂ) * (z v : ℂ)) = P at hP
  push_cast
  rw [mul_pow _ P, mul_pow, ← pow_mul, mul_comm (Module.finrank ℚ F) k, div_eq_mul_inv, inv_pow]
  have : (P ^ k)⁻¹ * P ^ k = 1 := inv_mul_cancel₀ (pow_ne_zero _ hP)
  generalize (P ^ k)⁻¹ = Q at this
  generalize (_ * _ * _ : ℂ)⁻¹ = R
  linear_combination (R * ((-Complex.I) ^ (k * Module.finrank ℚ F) * ((Algebra.norm ℚ (c : F) : ℚ) : ℂ) ^ k)) * this

theorem wcos : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ t : ℕ, G.det = (t : ℤ) ^ 2 → ∀ k : ℕ, Fintype.card κ = 2 * k → ∀ (a : F) (c : Fˣ) (x₀ : κ → F), a ≠ 0 → sl0 k (toInf (wm c)) (th G fun x => open Classical in if x - x₀ ∈ aL κ a then 1 else 0) = th G (wT G k t a c {x₀} fun _ => 1) := by
  intro F _ _ _ κ _ _ G hG t ht k hk a c x₀ ha
  letI : DecidableEq (InfinitePlace F) := Classical.decEq _
  obtain ⟨e, B, α, β, he, hα, hβ, hB, hdet⟩ := GlobalTheory.T.exists_realMatrix_for_lattice_and_dual_with_det F κ G hG t ht k hk a ha
  have hsm := (GlobalTheory.HilbertThetaSeries.formLatticeProps F κ G hG).2.1
  have hc : (c : F) ≠ 0 := c.ne_zero
  funext z
  have hz : ∀ v, 0 < ((sg v (c : F) : ℂ) ^ 2 * (z v : ℂ)).im := fun v => by
    rw [← Complex.ofReal_pow, Complex.im_ofReal_mul]
    exact mul_pos (sq_pos_of_ne_zero (sg_ne c v)) (z v).im_pos
  have hP := GlobalTheory.T.poisson_summation_gaussian_constant_on_even_blocks (InfinitePlace F) κ k hk B hB (e x₀) (fun v => (sg v (c : F) : ℂ) ^ 2 * (z v : ℂ)) hz
  have hL : ∀ Φ : (κ → F) → ℂ, (∀ x, x - x₀ ∈ aL κ a → Φ x = 1) → (∀ x, x - x₀ ∉ aL κ a → Φ x = 0) →
      th G Φ (HilbertThetaSeries.act (toInf (wm c)) z)
      = ∑' m : InfinitePlace F × κ → ℤ, Complex.exp (Real.pi * Complex.I * ∑ j, (-((sg j.1 (c : F) : ℂ) ^ 2 * (z j.1 : ℂ))⁻¹)
        * (((B *ᵥ fun i => (m i : ℝ)) j + e x₀ j : ℝ) : ℂ) ^ 2) := by
    intro Φ h1 h0
    unfold th
    have hinj : Function.Injective fun m : InfinitePlace F × κ → ℤ => (α m : κ → F) + x₀ := fun m n h =>
      α.injective (Subtype.ext (add_right_cancel h))
    rw [← hinj.tsum_eq]
    · refine tsum_congr fun m => ?_
      rw [h1 _ (by rw [add_sub_cancel_right]; exact (α m).2), one_mul, ← one_mul (QF G _), ez_QF G e he, map_add, hα]
      simp only [act_wm, map_one, Complex.ofReal_one, one_mul, Pi.add_apply]
    · intro x hx
      have hx' : x - x₀ ∈ aL κ a := by
        by_contra h
        exact hx (by simp [h0 x h])
      exact ⟨α.symm ⟨_, hx'⟩, by simp⟩
  have hR : th G (wT G k t a c {x₀} fun _ => 1) z = wC k t a (c : F) *
      ∑' m : InfinitePlace F × κ → ℤ, Complex.exp (Real.pi * Complex.I * ∑ j, ((sg j.1 (c : F) : ℂ) ^ 2 * (z j.1 : ℂ))
        * (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) j : ℝ) : ℂ) ^ 2) *
        Complex.exp (2 * Real.pi * Complex.I * ∑ j, (((B⁻¹ᵀ *ᵥ fun i => (m i : ℝ)) j * e x₀ j : ℝ) : ℂ)) := by
    unfold th
    have hinj : Function.Injective fun m : InfinitePlace F × κ → ℤ => (c : F) • (β m : κ → F) := fun m n h =>
      β.injective (Subtype.ext (smul_right_injective _ hc h))
    rw [← hinj.tsum_eq, ← tsum_mul_left]
    · refine tsum_congr fun m => ?_
      have h1 : (a / (c : F)) • (c : F) • (β m : κ → F) ∈ dualL F G := by
        rw [smul_smul, div_mul_cancel₀ _ hc]
        exact (β m).2
      rw [wT, if_pos h1, Finset.sum_singleton, one_mul, (hsm _ _ x₀).1, (hsm _ _ x₀).2.1, mul_div_cancel_left₀ _ hc,
        ez_QF G e he, et_BF G e he, hβ, mul_assoc, mul_comm (Complex.exp _)]
      simp only [map_pow, Complex.ofReal_pow]
    · intro y hy
      have hy' : (a / (c : F)) • y ∈ dualL F G := by
        by_contra h
        exact hy (by simp [wT, h])
      refine ⟨β.symm ⟨(c : F)⁻¹ • y, by rwa [smul_smul, ← div_eq_mul_inv]⟩, ?_⟩
      simp [smul_smul, hc]
  unfold sl0
  simp only [denom_wm]
  rw [hL _ (fun x h => if_pos h) (fun x h => if_neg h), hP, hR, ← mul_assoc, const_eq k t a c z _ hdet]

end GlobalTheory.WCos

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertThetaSeries_coset_inversion_formula : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ t : ℕ, G.det = (t : ℤ) ^ 2 → ∀ k : ℕ, Fintype.card κ = 2 * k → ∀ (a : F) (c : Fˣ) (x₀ : κ → F), a ≠ 0 → sl0 k (toInf (wm c)) (th G fun x => open Classical in if x - x₀ ∈ aL κ a then 1 else 0) = th G (wT G k t a c {x₀} fun _ => 1) := by
  first | exact @GlobalTheory.WCos.wcos | exact GlobalTheory.WCos.wcos | (intros; apply GlobalTheory.WCos.wcos <;> assumption)
