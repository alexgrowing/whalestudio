import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEisInt
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDeltaInt
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.CoeffRescaleExpandOfNotDvd
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalSer
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalMF

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem zetaRoot_mem_cyclotomicSubring_self (m : ℕ) : zetaC m ∈ Rm m := by
  exact Subring.subset_closure (Set.mem_singleton _)

theorem zetaRoot_ne_zero (e : ℕ) : zetaC e ≠ 0 := by
  exact Complex.exp_ne_zero _

private theorem dvd_and_eq_div_of_mem_Tm {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) :
    t.1 ∣ m ∧ 0 < t.1 ∧ t.2.2 = m / t.1 ∧ t.1 * t.2.2 = m := by
  simp only [Tm, Finset.mem_image, Finset.mem_sigma, Nat.mem_divisors, Finset.mem_range] at ht
  obtain ⟨⟨a, b⟩, ⟨⟨hdvd, _⟩, _⟩, rfl⟩ := ht
  exact ⟨hdvd, Nat.pos_of_dvd_of_pos hdvd hm, rfl, Nat.mul_div_cancel' hdvd⟩

private theorem zetaC_div_eq_pow_of_dvd {m a : ℕ} (hm : 0 < m) (ha : a ∣ m) : zetaC (m / a) = zetaC m ^ a := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at ha
    omega
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha0
  unfold zetaC
  rw [← Complex.exp_nat_mul, Nat.cast_div ha ha']
  congr 1
  field_simp

theorem zetaRoot_pow_mem_of_mem_hermiteTriples {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) :
    zetaC t.2.2 ^ t.2.1 ∈ Rm m ∧ (zetaC t.2.2 ^ t.2.1)⁻¹ ∈ Rm m := by
  obtain ⟨hdvd, _, he, _⟩ := dvd_and_eq_div_of_mem_Tm hm ht
  have hz : zetaC t.2.2 ^ t.2.1 = zetaC m ^ (t.1 * t.2.1) := by
    rw [he, zetaC_div_eq_pow_of_dvd hm hdvd, pow_mul]
  have hzm : zetaC m ^ m = 1 := by
    unfold zetaC
    rw [← Complex.exp_nat_mul]
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [show (m : ℂ) * (2 * Real.pi * Complex.I / m) = 2 * Real.pi * Complex.I by field_simp]
    exact Complex.exp_two_pi_mul_I
  have hinv : (zetaC m)⁻¹ = zetaC m ^ (m - 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', Nat.sub_add_cancel hm, hzm]
  rw [hz]
  constructor
  · exact pow_mem (zetaRoot_mem_cyclotomicSubring_self m) _
  · rw [← inv_pow, hinv, ← pow_mul]
    exact pow_mem (zetaRoot_mem_cyclotomicSubring_self m) _

theorem norm_zetaRoot_pow_of_mem_hermiteTriples {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) :
    ‖zetaC t.2.2 ^ t.2.1‖ = 1 := by
  rw [norm_pow, zetaC, Complex.norm_exp]
  simp

theorem convergesOnDisk_eisensteinFourCubeSeries : Conv aC := by
  rw [aC_eq]
  exact isMF_AA.conv

theorem convergesOnDisk_discriminantSeries : Conv dC := by
  rw [dC_eq]
  exact isMF_DD.conv

theorem evalSeries_eisensteinFourCubeSeries (τ : ℍ) : ev aC (qm 1 τ) = AA τ := by
  rw [aC_eq]
  exact isMF_AA.ev_eq τ

theorem evalSeries_discriminantSeries (τ : ℍ) : ev dC (qm 1 τ) = DD τ := by
  rw [dC_eq]
  exact isMF_DD.ev_eq τ

theorem eisensteinFourCubeSeries_coeff_zero : PowerSeries.coeff 0 aC = 1 := by
  rw [aC, PowerSeries.coeff_map, aZ, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, e4Z]
  simp

theorem discriminantSeries_coeff_zero : PowerSeries.coeff 0 dC = 0 := by
  rw [dC, PowerSeries.coeff_map, dZ_coeff_zero]
  simp

theorem discriminantSeries_coeff_one : PowerSeries.coeff 1 dC = 1 := by
  rw [dC, PowerSeries.coeff_map, dZ_coeff_one]
  simp

theorem facSer_coeffIn {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) :
    CoeffIn (Rm m) (facSer m t) := by
  obtain ⟨hc, _⟩ := zetaRoot_pow_mem_of_mem_hermiteTriples hm ht
  have hA : CoeffIn (Rm m) aC := CoeffIn.map_int _ _
  have hD : CoeffIn (Rm m) dC := CoeffIn.map_int _ _
  unfold facSer
  exact ((hA.xp m).mul (hD.sub1 hc _)).sub ((hA.sub1 hc _).mul (hD.xp m))

theorem facSer_conv {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) : Conv (facSer m t) := by
  have hc : ‖zetaC t.2.2 ^ t.2.1‖ ≤ 1 := (norm_zetaRoot_pow_of_mem_hermiteTriples hm ht).le
  have hk : t.1 ^ 2 ≠ 0 := pow_ne_zero _ (dvd_and_eq_div_of_mem_Tm hm ht).2.1.ne'
  unfold facSer
  exact ((convergesOnDisk_eisensteinFourCubeSeries.xp hm.ne').mul (convergesOnDisk_discriminantSeries.sub1 hc hk)).sub
    ((convergesOnDisk_eisensteinFourCubeSeries.sub1 hc hk).mul (convergesOnDisk_discriminantSeries.xp hm.ne'))

theorem facSer_ev {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) (τ : ℍ) :
    ev (facSer m t) (qm m τ) = fac t τ := by
  obtain ⟨hdvd, ha0, he, hae⟩ := dvd_and_eq_div_of_mem_Tm hm ht
  have he0 : 0 < t.2.2 := by
    rw [he]
    exact Nat.div_pos (Nat.le_of_dvd hm hdvd) ha0
  have hq := qm_norm_lt_one hm τ
  have hc := (norm_zetaRoot_pow_of_mem_hermiteTriples hm ht).le
  have hk : t.1 ^ 2 ≠ 0 := pow_ne_zero _ ha0.ne'
  have hA := convergesOnDisk_eisensteinFourCubeSeries
  have hD := convergesOnDisk_discriminantSeries
  have hpt : zetaC t.2.2 ^ t.2.1 * qm m τ ^ (t.1 ^ 2) = qm 1 (pt t.1 t.2.1 t.2.2 τ) := by
    rw [qm_pt ha0 he0, hae]
  unfold facSer fac
  rw [ev_sub ((hA.xp hm.ne').mul (hD.sub1 hc hk)) ((hA.sub1 hc hk).mul (hD.xp hm.ne')) hq,
    ev_mul (hA.xp hm.ne') (hD.sub1 hc hk) hq, ev_mul (hA.sub1 hc hk) (hD.xp hm.ne') hq,
    ev_xp _ hm.ne', ev_xp _ hm.ne', evalSeries_rescaleExpand _ _ hk, evalSeries_rescaleExpand _ _ hk, qm_pow hm, hpt]
  simp only [evalSeries_eisensteinFourCubeSeries, evalSeries_discriminantSeries]

theorem LowUnit.facSub_left {R : Subring ℂ} {f g : PowerSeries ℂ} {n n' : ℕ} {u u' : ℂ}
    (hf : LowUnit R f n u) (hg : LowUnit R g n' u') (h : n < n') : LowUnit R (f - g) n u := by
  obtain ⟨hu, hui, hu0, hlow, hval⟩ := hf
  obtain ⟨_, _, _, hglow, _⟩ := hg
  refine ⟨hu, hui, hu0, fun k hk => ?_, ?_⟩
  · rw [map_sub, hlow k hk, hglow k (hk.trans h), sub_zero]
  · rw [map_sub, hval, hglow n h, sub_zero]

theorem LowUnit.facSub_right {R : Subring ℂ} {f g : PowerSeries ℂ} {n n' : ℕ} {u u' : ℂ}
    (hf : LowUnit R f n u) (hg : LowUnit R g n' u') (h : n' < n) : LowUnit R (f - g) n' (-u') := by
  obtain ⟨_, _, _, hflow, _⟩ := hf
  obtain ⟨hu, hui, hu0, hglow, hval⟩ := hg
  refine ⟨neg_mem hu, by rw [inv_neg]; exact neg_mem hui, neg_ne_zero.2 hu0, fun k hk => ?_, ?_⟩
  · rw [map_sub, hflow k (hk.trans h), hglow k hk, sub_zero]
  · rw [map_sub, hflow n' h, hval, zero_sub]

theorem hasUnitLeadingCoeff_rescaleExpand_eisensteinFourCubeSeries (R : Subring ℂ) (c : ℂ) {k : ℕ} (hk : k ≠ 0) :
    LowUnit R (sub1 c k aC) 0 1 := by
  refine ⟨one_mem R, by rw [inv_one]; exact one_mem R, one_ne_zero,
    fun n hn => absurd hn (Nat.not_lt_zero n), ?_⟩
  rw [sub1, coeff_xp, if_pos (dvd_zero k), Nat.zero_div, PowerSeries.coeff_rescale, pow_zero, one_mul,
    eisensteinFourCubeSeries_coeff_zero]

theorem hasUnitLeadingCoeff_rescaleExpand_discriminantSeries {R : Subring ℂ} {c : ℂ} (hc : c ∈ R) (hc' : c⁻¹ ∈ R) (hc0 : c ≠ 0) {k : ℕ}
    (hk : k ≠ 0) : LowUnit R (sub1 c k dC) k c := by
  refine ⟨hc, hc', hc0, fun n hn => ?_, ?_⟩
  · rw [sub1, coeff_xp]
    split_ifs with hd
    · have h0 : n = 0 := Nat.eq_zero_of_dvd_of_lt hd hn
      subst h0
      rw [Nat.zero_div, PowerSeries.coeff_rescale, discriminantSeries_coeff_zero, mul_zero]
    · rfl
  · rw [sub1, coeff_xp, if_pos dvd_rfl, Nat.div_self (Nat.pos_of_ne_zero hk), PowerSeries.coeff_rescale,
      pow_one, discriminantSeries_coeff_one, mul_one]

theorem rescaleExpand_one (k : ℕ) (f : PowerSeries ℂ) : sub1 1 k f = xp k f := by
  simp [sub1, PowerSeries.rescale_one]

theorem facSer_low {m : ℕ} (hm : 0 < m) {t : ℕ × ℕ × ℕ} (ht : t ∈ Tm m) (hne : t.1 ≠ t.2.2) :
    ∃ n0 u, LowUnit (Rm m) (facSer m t) n0 u := by
  obtain ⟨hdvd, ha0, he, hae⟩ := dvd_and_eq_div_of_mem_Tm hm ht
  obtain ⟨hc, hci⟩ := zetaRoot_pow_mem_of_mem_hermiteTriples hm ht
  have hc0 : zetaC t.2.2 ^ t.2.1 ≠ 0 := pow_ne_zero _ (zetaRoot_ne_zero _)
  have hk : t.1 ^ 2 ≠ 0 := pow_ne_zero _ ha0.ne'
  have hxa : LowUnit (Rm m) (xp m aC) 0 1 := by
    rw [← rescaleExpand_one]
    exact hasUnitLeadingCoeff_rescaleExpand_eisensteinFourCubeSeries _ 1 hm.ne'
  have hxd : LowUnit (Rm m) (xp m dC) m 1 := by
    rw [← rescaleExpand_one]
    exact hasUnitLeadingCoeff_rescaleExpand_discriminantSeries (one_mem _) (by rw [inv_one]; exact one_mem _) one_ne_zero hm.ne'
  have h1 := hxa.mul (hasUnitLeadingCoeff_rescaleExpand_discriminantSeries hc hci hc0 hk)
  have h2 := (hasUnitLeadingCoeff_rescaleExpand_eisensteinFourCubeSeries (Rm m) (zetaC t.2.2 ^ t.2.1) hk).mul hxd
  simp only [zero_add, one_mul] at h1 h2
  unfold facSer
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨_, _, h1.facSub_left h2 (by rw [← hae]; nlinarith)⟩
  · exact ⟨_, _, h1.facSub_right h2 (by rw [← hae]; nlinarith)⟩

end ReciprocityTheory.ChartRestriction.L1
