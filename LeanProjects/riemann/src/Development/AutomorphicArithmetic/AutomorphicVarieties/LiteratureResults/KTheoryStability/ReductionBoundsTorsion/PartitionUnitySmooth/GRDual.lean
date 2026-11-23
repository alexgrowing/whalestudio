import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.Smoothing

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL
open scoped ComplexOrder

namespace PositivityTheory.KB.SmoothPartitionUnityBasic

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

private theorem re_nonneg {h : HS L N} (hh : h ∈ Pos L N) (w : InfinitePlace L) (x : Fin N → ℂ) :
    0 ≤ (star x ⬝ᵥ (mat h w *ᵥ x)).re :=
  (Complex.le_def.1 ((hh w).posSemidef.dotProduct_mulVec_nonneg x)).1

private theorem qR_nonneg {h : HS L N} (hh : h ∈ Pos L N) (z : VR L N) : 0 ≤ qR h z :=
  Finset.sum_nonneg fun w _ => re_nonneg hh w _

private theorem le_qR {h : HS L N} (hh : h ∈ Pos L N) (z : VR L N) (w : InfinitePlace L) :
    (star (z w) ⬝ᵥ (mat h w *ᵥ z w)).re ≤ qR h z :=
  Finset.single_le_sum (f := fun w => (star (z w) ⬝ᵥ (mat h w *ᵥ z w)).re) (fun w _ => re_nonneg hh w _)
    (Finset.mem_univ w)

private theorem qR_para (h : HS L N) (a b : VR L N) : qR h (a - b) + qR h (a + b) = 2 * qR h a + 2 * qR h b := by
  simp only [qR, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [Pi.sub_apply, Pi.add_apply, star_sub, star_add, mulVec_sub, mulVec_add, sub_dotProduct, add_dotProduct,
    dotProduct_sub, dotProduct_add, Complex.sub_re, Complex.add_re]
  ring

open Classical in
private theorem qR_single (h : HS L N) (w : InfinitePlace L) (y : Fin N → ℂ) :
    qR h (Pi.single w y) = (star y ⬝ᵥ (mat h w *ᵥ y)).re := by
  unfold qR
  rw [Finset.sum_eq_single w]
  · simp
  · intro w' _ hw
    simp [Pi.single_eq_of_ne hw]
  · simp

private theorem ex_single (w : InfinitePlace L) (y : Fin N → ℂ) :
    ∃ z : VR L N, z w = y ∧ ∀ k : HS L N, qR k z = (star y ⬝ᵥ (mat k w *ᵥ y)).re := by
  classical
  exact ⟨_, Pi.single_eq_same _ _, fun k => qR_single k w y⟩

private theorem cs (hB : Basic) (hN : 1 ≤ N) {h : HS L N} (hh : h ∈ Pos L N) (w : InfinitePlace L) (u v : Fin N → ℂ) :
    ‖star u ⬝ᵥ (mat h w *ᵥ v)‖ ^ 2 ≤ 4 * (star u ⬝ᵥ (mat h w *ᵥ u)).re * (star v ⬝ᵥ (mat h w *ᵥ v)).re := by
  have hc : Cl 1 h (h + h) := fun z => by
    have : qR (h + h) z = qR h z + qR h z := map_add (evR z) h h
    rw [this, add_sub_cancel_right, abs_of_nonneg (qR_nonneg hh z), one_mul]
  have := (hB L N hN).2.2.2.2.1 1 zero_le_one h hh _ hc w u v
  simpa only [mat_add, add_mulVec, dotProduct_add, add_sub_cancel_right, one_pow, mul_one] using this

private theorem pair {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.PosDef) (g v : Fin N → ℂ) :
    star (A⁻¹ *ᵥ star g) ⬝ᵥ (A *ᵥ v) = g ⬝ᵥ v := by
  have hd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hA.isUnit
  rw [star_mulVec, star_star, hA.isHermitian.inv.eq, ← dotProduct_mulVec, mulVec_mulVec, nonsing_inv_mul _ hd, one_mulVec]

private theorem dual_eq (A : Matrix (Fin N) (Fin N) ℂ) (g : Fin N → ℂ) :
    star g ⬝ᵥ ((A⁻¹)ᵀ *ᵥ g) = g ⬝ᵥ (A⁻¹ *ᵥ star g) := by
  rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]

private theorem place (a : 𝓞 L) (ha : a ≠ 0) : ∃ w : InfinitePlace L, 1 ≤ ‖embO w a‖ := by
  by_contra hn
  push Not at hn
  have h1 : ∀ w : InfinitePlace L, w (a : L) < 1 := fun w => by
    have := hn w
    rwa [← w.norm_embedding_eq]
  have h2 := InfinitePlace.prod_eq_abs_norm (a : L)
  have h3 : ∏ w : InfinitePlace L, w (a : L) ^ w.mult < ∏ _w : InfinitePlace L, (1 : ℝ) :=
    Finset.prod_lt_prod_of_nonempty
      (fun w _ => pow_pos (InfinitePlace.pos_iff.2 (RingOfIntegers.coe_ne_zero_iff.2 ha)) _)
      (fun w _ => pow_lt_one₀ (apply_nonneg w _) (h1 w) InfinitePlace.mult_ne_zero) Finset.univ_nonempty
  rw [h2, Finset.prod_const_one, ← Algebra.coe_norm_int] at h3
  have h4 : Algebra.norm ℤ a ≠ 0 := Algebra.norm_ne_zero_iff.2 ha
  have h5 : (1 : ℤ) ≤ |Algebra.norm ℤ a| := Int.one_le_abs h4
  have h6 : ((1 : ℤ) : ℝ) ≤ ((|Algebra.norm ℤ a| : ℤ) : ℝ) := Int.cast_le.2 h5
  push_cast at h3 h6
  linarith

private theorem geo (T : Finset ℤ) (k0 : ℤ) :
    ∑ k ∈ T, (if k0 ≤ k then ((4 : ℝ) ^ k)⁻¹ else 0) ≤ 2 * ((4 : ℝ) ^ k0)⁻¹ := by
  rw [← Finset.sum_filter]
  have e : ∑ k ∈ T.filter (k0 ≤ ·), ((4 : ℝ) ^ k)⁻¹ =
      ∑ j ∈ (T.filter (k0 ≤ ·)).image (fun k => (k - k0).toNat), ((4 : ℝ) ^ k0)⁻¹ * (1 / 4) ^ j := by
    rw [Finset.sum_image]
    · refine Finset.sum_congr rfl fun k hk => ?_
      have h1 := (Finset.mem_filter.1 hk).2
      obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = k0 + j := ⟨(k - k0).toNat, by omega⟩
      rw [show (k0 + j - k0).toNat = j by omega, zpow_add₀ (by norm_num), zpow_natCast, mul_inv, one_div, inv_pow]
    · intro a ha b hb hab
      have h1 := (Finset.mem_filter.1 (Finset.mem_coe.1 ha)).2
      have h2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hb)).2
      simp only at hab
      omega
  rw [e, ← Finset.mul_sum, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have hs := hasSum_geometric_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
  exact (sum_le_hasSum _ (fun i _ => by positivity) hs).trans (by norm_num)

private theorem fin_num {A s m G P X Q : ℝ} (hA0 : 0 < A) (hsp : 0 < s) (hmp : 0 < m) (h1 : 1 ≤ 4 * s * m) (hgy : s ≤ G)
    (k1 : G ^ 2 ≤ 4 * P * X) (k2 : P ≤ Q) (k0 : 0 ≤ Q) (hX : 0 ≤ X) (hR : X ≤ A * s / m) : 1 / (16 * A) ≤ Q := by
  have k3 : s ^ 2 ≤ 4 * Q * (A * s / m) := by
    calc s ^ 2 ≤ G ^ 2 := by gcongr
      _ ≤ _ := k1
      _ ≤ 4 * Q * X := by gcongr
      _ ≤ _ := by gcongr
  have k4 : s * m ≤ 4 * Q * A := by
    have : s * (s * m) ≤ s * (4 * Q * A) := by
      calc s * (s * m) = s ^ 2 * m := by ring
        _ ≤ 4 * Q * (A * s / m) * m := by gcongr
        _ = _ := by field_simp
    exact le_of_mul_le_mul_left this hsp
  rw [div_le_iff₀ (by positivity)]
  nlinarith

attribute [local irreducible] lam ret term

set_option maxHeartbeats 600000 in
theorem pf_GRDual : GRDual := by
  classical
  intro hB hTr hE hTL L _ _ hC N hN μ hμ
  obtain ⟨C1, hC1, htr⟩ := hTr L hC N hN
  obtain ⟨_, hT⟩ := hTL L N hN
  obtain ⟨c, C2, hc, hcmp⟩ := hμ.cmp
  refine ⟨1 / (16 * (12 * C1 * |C2| + 32)), by positivity, fun h hh => ?_⟩
  have hRP := (hE L N hN μ hμ h hh).2.1
  obtain ⟨f, hf, e⟩ := ((hB L N hN).1 _ ((hB L N hN).1 _ hRP).2.2.2.1).2.2.1
  have hD : 0 < lamD h := ((hB L N hN).1 _ ((hB L N hN).1 _ hh).2.2.2.1).1
  change _ ≤ lam _
  rw [← e]
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hf
  have hne : f ⬝ᵥ (Pi.single a 1 : Lat L N) ≠ 0 := by simpa using ha
  obtain ⟨v0, hv0, hmin⟩ := Set.exists_min_image {v : Lat L N | q h v ≤ q h (Pi.single a 1) ∧ f ⬝ᵥ v ≠ 0} (q h)
    ((((hB L N hN).1 _ hh).2.2.2.2 _).subset fun v hv => hv.1) ⟨_, le_rfl, hne⟩
  have hmin' : ∀ v : Lat L N, f ⬝ᵥ v ≠ 0 → q h v0 ≤ q h v := fun v hv => by
    by_cases h1 : q h v ≤ q h (Pi.single a 1)
    · exact hmin v ⟨h1, hv⟩
    · exact hv0.1.trans (not_le.1 h1).le
  obtain ⟨w, hw⟩ := place _ hv0.2
  have hdot : ∀ v : Lat L N, toR f w ⬝ᵥ toR v w = embO w (f ⬝ᵥ v) := fun v => by
    simp [toR, dotProduct]
  set g := toR f w with hg
  set y := (mat h w)⁻¹ *ᵥ star g with hy
  have hp : ∀ v, star y ⬝ᵥ (mat h w *ᵥ v) = g ⬝ᵥ v := pair (hh w) g
  set s := (star y ⬝ᵥ (mat h w *ᵥ y)).re with hs
  set m := q h v0 with hm
  have hs0 : 0 ≤ s := re_nonneg hh w y
  have hm0 : 0 ≤ m := qR_nonneg hh _
  have h1 : 1 ≤ 4 * s * m := by
    have := cs hB hN hh w y (toR v0 w)
    rw [hp, hdot] at this
    have h2 := le_qR hh (toR v0) w
    calc (1 : ℝ) ≤ ‖embO w (f ⬝ᵥ v0)‖ ^ 2 := one_le_pow₀ hw
      _ ≤ _ := this
      _ ≤ 4 * s * m := mul_le_mul_of_nonneg_left h2 (mul_nonneg (by norm_num) hs0)
  have hsp : 0 < s := by
    rcases hs0.eq_or_lt with h0 | h0
    · rw [← h0] at h1; norm_num at h1
    · exact h0
  have hmp : 0 < m := by
    rcases hm0.eq_or_lt with h0 | h0
    · rw [← h0] at h1; norm_num at h1
    · exact h0
  have hgy : s ≤ ‖g ⬝ᵥ y‖ := by rw [← hp]; exact Complex.re_le_norm _
  clear_value m s y g
  have hmC : m ≤ 12 * (C1 / lamD h) := by
    have htr' := htr h hh
    have hρ0 : 0 < C1 / lamD h := div_pos hC1 hD
    generalize C1 / lamD h = ρ at htr' hρ0 ⊢
    obtain ⟨t, ht0, ht2⟩ : ∃ t : ℝ, 0 ≤ t ∧ t ^ 2 * s = 5 * ρ :=
      ⟨√(5 * ρ / s), Real.sqrt_nonneg _, by
        rw [Real.sq_sqrt (div_pos (mul_pos (by norm_num) hρ0) hsp).le, div_mul_cancel₀ _ hsp.ne']⟩
    obtain ⟨Z, hZw, hZ⟩ := ex_single w ((t : ℂ) • y)
    obtain ⟨v, hv⟩ := htr' Z
    have hz : qR h Z = 5 * ρ := by
      rw [hZ, star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_smul, ← ht2]
      simp [hs, sq]
    have hfv : f ⬝ᵥ v ≠ 0 := by
      intro h0
      have k1 := cs hB hN hh w y ((Z - toR v : VR L N) w)
      have k2 := (le_qR hh (Z - toR v) w).trans hv
      rw [hp] at k1
      have k3 : g ⬝ᵥ (Z - toR v : VR L N) w = (t : ℂ) * (g ⬝ᵥ y) := by
        rw [Pi.sub_apply, hZw, dotProduct_sub, hdot, h0, map_zero, sub_zero, dotProduct_smul, smul_eq_mul]
      rw [k3, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0] at k1
      have k4 : (t * s) ^ 2 ≤ (t * ‖g ⬝ᵥ y‖) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg ht0 hs0) (mul_le_mul_of_nonneg_left hgy ht0) 2
      have k5 : (t * s) ^ 2 ≤ 4 * s * ρ := k4.trans (k1.trans (by
        rw [← hs]; exact mul_le_mul_of_nonneg_left k2 (mul_nonneg (by norm_num) hs0)))
      have k6 : (t * s) ^ 2 = 5 * ρ * s := by rw [← ht2]; ring
      have k10 := mul_pos hρ0 hsp
      rw [k6] at k5
      clear * - k5 k10
      nlinarith
    have k7 := qR_para h Z (Z - toR v)
    rw [sub_sub_cancel, hz] at k7
    have k8 := qR_nonneg hh (Z + (Z - toR v))
    have k9 := hmin' v hfv
    change m ≤ qR h (toR v) at k9
    clear * - k7 k8 k9 hv
    linarith
  obtain ⟨z, -, hzz⟩ := ex_single w y
  have hzs : qR h z = s := (hzz h).trans hs.symm
  obtain ⟨k0, hk0, hk1⟩ := exists_mem_Ico_zpow hmp (show (1 : ℝ) < 4 by norm_num)
  have hrho : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1 := fun x => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hterm : ∀ k : ℤ, evR z (rho ((4 : ℝ) ^ k * μ h) • term ((4 : ℝ) ^ k) h) ≤
      4 * s * if k0 ≤ k then ((4 : ℝ) ^ k)⁻¹ else 0 := by
    intro k
    have hk : (0 : ℝ) < 4 ^ k := zpow_pos (by norm_num) _
    rw [map_smul, smul_eq_mul, evR_apply]
    split_ifs with hkk
    · obtain ⟨⟨b1, b2⟩, -⟩ := hT _ hk h hh z
      rw [hzs] at b2
      calc _ ≤ 1 * (4 / 4 ^ k * s) := mul_le_mul (hrho _).2 b2 b1 zero_le_one
        _ = _ := by rw [div_eq_mul_inv]; ring
    · have h4 : 4 * (4 : ℝ) ^ k ≤ m := by
        refine le_trans ?_ hk0
        rw [mul_comm, ← zpow_add_one₀ (by norm_num)]
        exact zpow_le_zpow_right₀ (by norm_num) (by omega)
      have h0 : evR z (∑ᶠ v : Lat L N, rho (q h v / 4 ^ k) • rk h v) = 0 := by
        refine finsum_induction (fun x => evR z x = 0) (map_zero _)
          (fun x y hx hy => by rw [map_add, hx, hy, add_zero]) fun v => ?_
        rw [map_smul, smul_eq_mul]
        by_cases hv : f ⬝ᵥ v = 0
        · refine mul_eq_zero_of_right _ ?_
          have e1 : mat (rk h v) w = vecMulVec (mat h w *ᵥ toR v w) (star (mat h w *ᵥ toR v w)) := rfl
          have e2 : star y ⬝ᵥ (mat h w *ᵥ toR v w) = 0 := by rw [hp, hdot, hv, map_zero]
          rw [evR_apply, hzz, e1, dotProduct_mulVec, vecMul_vecMulVec, e2, zero_smul, zero_dotProduct, Complex.zero_re]
        · refine mul_eq_zero_of_left (Real.smoothTransition.zero_of_nonpos ?_) _
          have : 4 ≤ q h v / 4 ^ k := by rw [le_div_iff₀ hk]; exact h4.trans (hmin' v hv)
          clear * - this
          linarith
      have : qR (term ((4 : ℝ) ^ k) h) z = 0 := by
        rw [← evR_apply, term, map_smul, h0, smul_zero]
      rw [this]; simp
  have hinv : ((4 : ℝ) ^ k0)⁻¹ ≤ 4 / m := by
    rw [zpow_add_one₀ (by norm_num)] at hk1
    rw [le_div_iff₀ hmp, inv_mul_le_iff₀ (zpow_pos (by norm_num) _)]
    exact hk1.le
  have hsum : evR z (∑ᶠ k : ℤ, rho ((4 : ℝ) ^ k * μ h) • term ((4 : ℝ) ^ k) h) ≤ 32 * s / m := by
    by_cases hfin : (Function.support fun k : ℤ => rho ((4 : ℝ) ^ k * μ h) • term ((4 : ℝ) ^ k) h).Finite
    · rw [finsum_eq_sum _ hfin, map_sum]
      refine (Finset.sum_le_sum fun k _ => hterm k).trans ?_
      rw [← Finset.mul_sum]
      calc _ ≤ 4 * s * (2 * (4 / m)) :=
            mul_le_mul_of_nonneg_left ((geo _ k0).trans (mul_le_mul_of_nonneg_left hinv (by norm_num)))
              (mul_nonneg (by norm_num) hs0)
        _ = _ := by ring
    · rw [finsum_of_infinite_support hfin, map_zero]; exact div_nonneg (mul_nonneg (by norm_num) hs0) hm0
  have hμm : μ h * m ≤ 12 * C1 * |C2| := by
    have b1 : μ h ≤ |C2| * lamD h := (hcmp h hh).2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hD.le)
    calc μ h * m ≤ |C2| * lamD h * (12 * (C1 / lamD h)) :=
          mul_le_mul b1 hmC hm0 (mul_nonneg (abs_nonneg _) hD.le)
      _ = _ := by have := hD.ne'; clear * - this; generalize lamD h = x at *; field_simp
  have hR : (star y ⬝ᵥ (mat (ret μ h) w *ᵥ y)).re ≤ (12 * C1 * |C2| + 32) * s / m := by
    rw [← hzz, ← evR_apply, ret, map_add, map_smul, smul_eq_mul, evR_apply z h, hzs]
    have : μ h * s ≤ 12 * C1 * |C2| * s / m := by
      rw [le_div_iff₀ hmp]
      exact (mul_right_comm _ _ _).trans_le (mul_le_mul_of_nonneg_right hμm hs0)
    calc _ ≤ 12 * C1 * |C2| * s / m + 32 * s / m := add_le_add this hsum
      _ = _ := by ring
  have k1 := cs hB hN hRP w ((mat (ret μ h) w)⁻¹ *ᵥ star g) y
  rw [pair (hRP w), pair (hRP w), ← dual_eq] at k1
  have k2 : (star g ⬝ᵥ (((mat (ret μ h) w)⁻¹)ᵀ *ᵥ g)).re ≤ q (dualH (ret μ h)) f := by
    rw [hg]
    exact le_qR ((hB L N hN).1 _ hRP).2.2.2.1 (toR f) w
  have k0' : 0 ≤ q (dualH (ret μ h)) f := qR_nonneg ((hB L N hN).1 _ hRP).2.2.2.1 _
  have hA0 : 0 < 12 * C1 * |C2| + 32 := by clear * - hC1; positivity
  exact fin_num hA0 hsp hmp h1 hgy k1 k2 k0' (re_nonneg hRP w y) hR

end PositivityTheory.KB.SmoothPartitionUnityBasic

end
