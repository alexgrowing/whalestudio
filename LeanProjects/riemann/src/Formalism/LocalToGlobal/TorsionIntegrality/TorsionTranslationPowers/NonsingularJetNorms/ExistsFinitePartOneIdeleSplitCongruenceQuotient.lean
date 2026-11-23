import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementA
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral

noncomputable section

namespace Formalism.L2.Th1.E

namespace AddThm

open Formalism.L2.Th1

section Analytic

variable (L : PeriodPair)

theorem hasDerivAt_P (z : ℂ) (hz : z ∉ L.lattice) :
    HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
  haveI : DiscreteTopology L.lattice.toAddSubgroup := inferInstanceAs (DiscreteTopology L.lattice)
  have ho := (AddSubgroup.isClosed_of_discrete (H := L.lattice.toAddSubgroup)).isOpen_compl.mem_nhds hz
  have hd := (L.differentiableOn_weierstrassP z hz).differentiableAt ho
  rw [← L.deriv_weierstrassP]
  exact hd.hasDerivAt

theorem notMem_nhds (z : ℂ) (hz : z ∉ L.lattice) : ∀ᶠ w in nhds z, w ∉ L.lattice := by
  haveI : DiscreteTopology L.lattice.toAddSubgroup := inferInstanceAs (DiscreteTopology L.lattice)
  exact (AddSubgroup.isClosed_of_discrete (H := L.lattice.toAddSubgroup)).isOpen_compl.mem_nhds hz

theorem P_sub_ne (z w : ℂ) (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) (hp : z + w ∉ L.lattice)
    (hm : z - w ∉ L.lattice) : L.weierstrassP z - L.weierstrassP w ≠ 0 := by
  intro h
  rcases (Formalism.L2.Th1.F.pInjective L z w hz hw).mp (sub_eq_zero.mp h) with h1 | h1
  · exact hm h1
  · exact hp h1

private theorem weierstrassP_addition_identity (a b : ℂ) (ha : a ∉ L.lattice) (hb : b ∉ L.lattice)
    (hab : a + b ∉ L.lattice) (hmab : a - b ∉ L.lattice) :
    -L.weierstrassP (a + b) * (2 * (L.weierstrassP a - L.weierstrassP b)) ^ 2 =
      -L.weierstrassP a * (2 * (L.weierstrassP a - L.weierstrassP b)) ^ 2 +
        ((6 * L.weierstrassP a ^ 2 - L.g₂ / 2) * (2 * (L.weierstrassP a - L.weierstrassP b))
          - (L.derivWeierstrassP a - L.derivWeierstrassP b) * (2 * L.derivWeierstrassP a)) := by
  have hne : L.weierstrassP a - L.weierstrassP b ≠ 0 := P_sub_ne L a b ha hb hab hmab
  have hD : 2 * (L.weierstrassP a - L.weierstrassP b) ≠ 0 := mul_ne_zero two_ne_zero hne
  have h2 : ∀ᶠ u in nhds a, u + b ∉ L.lattice :=
    ((continuous_add_right b).tendsto a).eventually (notMem_nhds L (a + b) hab)
  have h3 : ∀ᶠ u in nhds a, u - b ∉ L.lattice :=
    ((continuous_sub_right b).tendsto a).eventually (notMem_nhds L (a - b) hmab)
  have hev : (fun u => Formalism.L2.Th1.F.wZeta L (u + b)) =ᶠ[nhds a]
      (fun u => Formalism.L2.Th1.F.wZeta L u + Formalism.L2.Th1.F.wZeta L b
        + (L.derivWeierstrassP u - L.derivWeierstrassP b) / (2 * (L.weierstrassP u - L.weierstrassP b))) := by
    filter_upwards [notMem_nhds L a ha, h2, h3] with u hu1 hu2 hu3
    exact Formalism.L2.Th1.F.zetaAdd L u b hu1 hb hu2 hu3
  have hL := (Formalism.L2.Th1.F.zetaHasDeriv L (a + b) hab).comp_add_const a b
  have hR := ((Formalism.L2.Th1.F.zetaHasDeriv L a ha).add_const (Formalism.L2.Th1.F.wZeta L b)).add
    (((Formalism.L2.Th1.F.pSecond L a ha).sub_const (L.derivWeierstrassP b)).div
      (((hasDerivAt_P L a ha).sub_const (L.weierstrassP b)).const_mul 2) hD)
  have hu := hL.unique (hR.congr_of_eventuallyEq hev)
  have hD2 : (2 * (L.weierstrassP a - L.weierstrassP b)) ^ 2 ≠ 0 := pow_ne_zero 2 hD
  have hm2 := congrArg (· * (2 * (L.weierstrassP a - L.weierstrassP b)) ^ 2) hu
  simp only [add_mul, div_mul_cancel₀ _ hD2] at hm2
  linear_combination hm2

theorem P_add (z w : ℂ) (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) (hp : z + w ∉ L.lattice)
    (hm : z - w ∉ L.lattice) :
    L.weierstrassP (z + w) =
      ((L.derivWeierstrassP z - L.derivWeierstrassP w) / (L.weierstrassP z - L.weierstrassP w)) ^ 2 / 4
        - L.weierstrassP z - L.weierstrassP w := by
  have hne : L.weierstrassP z - L.weierstrassP w ≠ 0 := P_sub_ne L z w hz hw hp hm
  have E1 := weierstrassP_addition_identity L z w hz hw hp hm
  have E2 := weierstrassP_addition_identity L w z hw hz (by rwa [add_comm]) (fun h => hm (by simpa using L.lattice.neg_mem h))
  rw [add_comm w z] at E2
  rw [div_pow, div_div, eq_sub_iff_add_eq, eq_sub_iff_add_eq,
    eq_div_iff (mul_ne_zero (pow_ne_zero 2 hne) (by norm_num : (4 : ℂ) ≠ 0))]
  linear_combination (-1 / 2 : ℂ) * E1 + (-1 / 2 : ℂ) * E2

theorem collinear (z w : ℂ) (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) (hp : z + w ∉ L.lattice) :
    (L.weierstrassP z - L.weierstrassP w) * L.derivWeierstrassP (z + w) =
      -((L.derivWeierstrassP z - L.derivWeierstrassP w) * (L.weierstrassP (z + w) - L.weierstrassP z)
        + L.derivWeierstrassP z * (L.weierstrassP z - L.weierstrassP w)) := by
  by_cases hm : z - w ∈ L.lattice
  · have hwz : w = z + -(z - w) := by ring
    have hx : L.weierstrassP w = L.weierstrassP z := by
      rw [hwz]; exact L.weierstrassP_add_coe z ⟨-(z - w), L.lattice.neg_mem hm⟩
    have hy : L.derivWeierstrassP w = L.derivWeierstrassP z := by
      rw [hwz]; exact L.derivWeierstrassP_add_coe z ⟨-(z - w), L.lattice.neg_mem hm⟩
    rw [hx, hy]; ring
  have hne := P_sub_ne L z w hz hw hp hm
  have hf := ((Formalism.L2.Th1.F.pSecond L z hz).sub_const (L.derivWeierstrassP w)).div
    ((hasDerivAt_P L z hz).sub_const (L.weierstrassP w)) hne
  have hg := (((hf.mul hf).div_const 4).sub (hasDerivAt_P L z hz)).sub_const (L.weierstrassP w)
  have h2 : ∀ᶠ u in nhds z, u + w ∉ L.lattice :=
    ((continuous_add_right w).tendsto z).eventually (notMem_nhds L (z + w) hp)
  have h3 : ∀ᶠ u in nhds z, u - w ∉ L.lattice :=
    ((continuous_sub_right w).tendsto z).eventually (notMem_nhds L (z - w) hm)
  have hev : (fun u => L.weierstrassP (u + w)) =ᶠ[nhds z]
      (fun u => (L.derivWeierstrassP u - L.derivWeierstrassP w) / (L.weierstrassP u - L.weierstrassP w) *
        ((L.derivWeierstrassP u - L.derivWeierstrassP w) / (L.weierstrassP u - L.weierstrassP w)) / 4 - L.weierstrassP u - L.weierstrassP w) := by
    filter_upwards [notMem_nhds L z hz, h2, h3] with u hu1 hu2 hu3
    rw [P_add L u w hu1 hw hu2 hu3]
    ring
  have hu := ((hasDerivAt_P L (z + w) hp).comp_add_const z w).unique (hg.congr_of_eventuallyEq hev)
  beta_reduce at hu
  simp only [Pi.div_apply, Pi.mul_apply, Pi.sub_apply] at hu
  have hF : (L.derivWeierstrassP z - L.derivWeierstrassP w) / (L.weierstrassP z - L.weierstrassP w) * (L.weierstrassP z - L.weierstrassP w) = L.derivWeierstrassP z - L.derivWeierstrassP w := div_mul_cancel₀ _ hne
  have hFz : ((6 * L.weierstrassP z ^ 2 - L.g₂ / 2) * (L.weierstrassP z - L.weierstrassP w) - (L.derivWeierstrassP z - L.derivWeierstrassP w) * L.derivWeierstrassP z) / (L.weierstrassP z - L.weierstrassP w) ^ 2 * (L.weierstrassP z - L.weierstrassP w) ^ 2 = (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) * (L.weierstrassP z - L.weierstrassP w) - (L.derivWeierstrassP z - L.derivWeierstrassP w) * L.derivWeierstrassP z :=
    div_mul_cancel₀ _ (pow_ne_zero 2 hne)
  have E1 := weierstrassP_addition_identity L z w hz hw hp hm
  have hFz2 : ((6 * L.weierstrassP z ^ 2 - L.g₂ / 2) * (L.weierstrassP z - L.weierstrassP w) - (L.derivWeierstrassP z - L.derivWeierstrassP w) * L.derivWeierstrassP z) / (L.weierstrassP z - L.weierstrassP w) ^ 2 = 2 * (L.weierstrassP z - L.weierstrassP (z + w)) :=
    mul_right_cancel₀ (pow_ne_zero 2 hne) (by linear_combination hFz - (1 / 2 : ℂ) * E1)
  linear_combination (L.weierstrassP z - L.weierstrassP w) * hu + (((6 * L.weierstrassP z ^ 2 - L.g₂ / 2) * (L.weierstrassP z - L.weierstrassP w) - (L.derivWeierstrassP z - L.derivWeierstrassP w) * L.derivWeierstrassP z) / (L.weierstrassP z - L.weierstrassP w) ^ 2 / 2) * hF + ((L.derivWeierstrassP z - L.derivWeierstrassP w) / 2) * hFz2

theorem rat_notMem (q : ℚ) (hq : q.den ≠ 1) (x : ℂ) (hx : x = (q : ℂ) * L.ω₁) : x ∉ L.lattice := by
  intro h
  have h' := (PeriodPair.mul_ω₁_add_mul_ω₂_mem_lattice (L := L) (α := q) (β := 0)).1
    (by rw [hx] at h; simpa using h)
  exact hq h'.1

theorem exists_finite_part_one_idele_split_congruence_quotient (s : ℂ) : ∃ u : ℂ, 2 * u ∉ L.lattice ∧ s + u ∉ L.lattice ∧ s - u ∉ L.lattice := by
  by_cases h : s + L.ω₁ / 3 ∈ L.lattice ∨ s - L.ω₁ / 3 ∈ L.lattice
  · refine ⟨L.ω₁ / 5, rat_notMem L (2 / 5) (by norm_num) _ (by push_cast; ring), ?_, ?_⟩
    · intro h5
      rcases h with h | h
      · exact rat_notMem L (2 / 15) (by norm_num) _ (by push_cast; ring) (L.lattice.sub_mem h h5)
      · exact rat_notMem L (8 / 15) (by norm_num) _ (by push_cast; ring) (L.lattice.sub_mem h5 h)
    · intro h5
      rcases h with h | h
      · exact rat_notMem L (8 / 15) (by norm_num) _ (by push_cast; ring) (L.lattice.sub_mem h h5)
      · exact rat_notMem L (2 / 15) (by norm_num) _ (by push_cast; ring) (L.lattice.sub_mem h5 h)
  · push Not at h
    exact ⟨L.ω₁ / 3, rat_notMem L (2 / 3) (by norm_num) _ (by push_cast; ring), h.1, h.2⟩

end Analytic

variable (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])

theorem disc_ne : (curveL l L ι).Δ ≠ 0 := by
  have h := Formalism.L2.Th1.F.discNeZero L
  have e : (curveL l L ι).Δ = ι (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
    simp only [curveL, Formalism.L2.Th1.A.shortW, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈, map_sub, map_mul, map_pow,
      map_ofNat]
    ring
  rw [e]
  exact (map_ne_zero ι).mpr h

theorem nonsing (t : ℂ) (ht : t ∉ L.lattice) :
    (curveL l L ι).toAffine.Nonsingular (ι (L.weierstrassP t)) (ι (L.derivWeierstrassP t) / 2) := by
  haveI : (curveL l L ι).IsElliptic := ⟨(disc_ne l L ι).isUnit⟩
  rw [← WeierstrassCurve.Affine.equation_iff_nonsingular, WeierstrassCurve.Affine.equation_iff]
  have h := congrArg ι (L.derivWeierstrassP_sq t ht)
  simp only [map_sub, map_mul, map_pow, map_ofNat, map_add] at h
  simp only [curveL, Formalism.L2.Th1.A.shortW]
  linear_combination (1 / 4 : ℂ_[l]) * h

end AddThm

variable (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])

theorem ptOf_some (t : ℂ) (ht : t ∉ L.lattice) :
    ptOf l L ι t = .some _ _ (AddThm.nonsing l L ι t ht) := by
  unfold ptOf
  rw [dif_pos ⟨ht, AddThm.nonsing l L ι t ht⟩]

theorem ptOf_lattice (t : ℂ) (ht : t ∈ L.lattice) : ptOf l L ι t = 0 := by
  unfold ptOf
  exact dif_neg (fun h => h.1 ht)

theorem ptOf_add_lattice (t ω : ℂ) (hω : ω ∈ L.lattice) : ptOf l L ι (t + ω) = ptOf l L ι t := by
  have h1 : L.weierstrassP (t + ω) = L.weierstrassP t := L.weierstrassP_add_coe t ⟨ω, hω⟩
  have h2 : L.derivWeierstrassP (t + ω) = L.derivWeierstrassP t := L.derivWeierstrassP_add_coe t ⟨ω, hω⟩
  have h3 : t + ω ∈ L.lattice ↔ t ∈ L.lattice := L.lattice.add_mem_iff_left hω
  by_cases ht : t ∈ L.lattice
  · rw [ptOf_lattice l L ι t ht, ptOf_lattice l L ι (t + ω) (h3.mpr ht)]
  · rw [ptOf_some l L ι t ht, ptOf_some l L ι (t + ω) (fun h => ht (h3.mp h))]
    simp only [WeierstrassCurve.Affine.Point.some.injEq, h1, h2, and_self]

theorem ptOf_neg (t : ℂ) : ptOf l L ι (-t) = -ptOf l L ι t := by
  by_cases ht : t ∈ L.lattice
  · rw [ptOf_lattice l L ι t ht, ptOf_lattice l L ι (-t) (L.lattice.neg_mem ht)]
    rfl
  · have ht' : -t ∉ L.lattice := fun h => ht (by simpa using L.lattice.neg_mem h)
    rw [ptOf_some l L ι t ht, ptOf_some l L ι (-t) ht', WeierstrassCurve.Affine.Point.neg_some]
    simp [L.weierstrassP_neg, L.derivWeierstrassP_neg, curveL, Formalism.L2.Th1.A.shortW,
      WeierstrassCurve.Affine.negY, neg_div]

section Law

variable [DecidableEq ℂ_[l]]

theorem ptOf_add_generic (s t : ℂ) (hs : s ∉ L.lattice) (ht : t ∉ L.lattice) (hp : s + t ∉ L.lattice)
    (hm : s - t ∉ L.lattice) : ptOf l L ι (s + t) = ptOf l L ι s + ptOf l L ι t := by
  have hne := AddThm.P_sub_ne L s t hs ht hp hm
  have hne' : ι (L.weierstrassP s) - ι (L.weierstrassP t) ≠ 0 := by
    rw [← map_sub]
    exact fun h => hne (ι.injective (h.trans (map_zero ι).symm))
  have hx : ι (L.weierstrassP s) ≠ ι (L.weierstrassP t) := sub_ne_zero.1 hne'
  have hX := congrArg ι (AddThm.P_add L s t hs ht hp hm)
  have hY := congrArg ι (AddThm.collinear L s t hs ht hp)
  simp only [map_pow, map_sub, map_mul, map_add, map_neg, map_div₀, map_ofNat] at hX hY
  rw [ptOf_some l L ι s hs, ptOf_some l L ι t ht, ptOf_some l L ι _ hp,
    WeierstrassCurve.Affine.Point.add_of_X_ne hx]
  have e1 : ι (L.weierstrassP (s + t)) =
      (curveL l L ι).toAffine.addX (ι (L.weierstrassP s)) (ι (L.weierstrassP t))
        ((curveL l L ι).toAffine.slope (ι (L.weierstrassP s)) (ι (L.weierstrassP t))
          (ι (L.derivWeierstrassP s) / 2) (ι (L.derivWeierstrassP t) / 2)) := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hx, hX]
    simp only [WeierstrassCurve.Affine.addX, curveL, A.shortW]
    field_simp
    ring
  have e2 : ι (L.derivWeierstrassP (s + t)) / 2 =
      (curveL l L ι).toAffine.addY (ι (L.weierstrassP s)) (ι (L.weierstrassP t))
        (ι (L.derivWeierstrassP s) / 2)
        ((curveL l L ι).toAffine.slope (ι (L.weierstrassP s)) (ι (L.weierstrassP t))
          (ι (L.derivWeierstrassP s) / 2) (ι (L.derivWeierstrassP t) / 2)) := by
    rw [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, ← e1,
      WeierstrassCurve.Affine.slope_of_X_ne hx]
    simp only [WeierstrassCurve.Affine.negY, curveL, A.shortW]
    field_simp
    linear_combination hY
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨e1, e2⟩

theorem ptOf_add (s t : ℂ) : ptOf l L ι (s + t) = ptOf l L ι s + ptOf l L ι t := by
  by_cases hs : s ∈ L.lattice
  · rw [add_comm s t, ptOf_add_lattice l L ι t s hs, ptOf_lattice l L ι s hs, zero_add]
  by_cases ht : t ∈ L.lattice
  · rw [ptOf_add_lattice l L ι s t ht, ptOf_lattice l L ι t ht, add_zero]
  by_cases hp : s + t ∈ L.lattice
  · have h : ptOf l L ι t = -ptOf l L ι s := by
      rw [← ptOf_neg, ← ptOf_add_lattice l L ι (-s) (s + t) hp]
      congr 1
      ring
    rw [ptOf_lattice l L ι _ hp, h, add_neg_cancel]
  by_cases hm : s - t ∈ L.lattice
  · have h1 : ptOf l L ι s = ptOf l L ι t := by
      rw [← ptOf_add_lattice l L ι t (s - t) hm]
      congr 1
      ring
    have h2 : ptOf l L ι (s + t) = ptOf l L ι (t + t) := by
      rw [← ptOf_add_lattice l L ι (t + t) (s - t) hm]
      congr 1
      ring
    have htt : t + t ∉ L.lattice := fun h => hp (by
      have := L.lattice.add_mem h hm
      convert this using 1
      ring)
    obtain ⟨u, hu2, hup, hum⟩ := AddThm.exists_finite_part_one_idele_split_congruence_quotient L t
    have hu : u ∉ L.lattice := fun h => hu2 (by
      rw [two_mul]
      exact L.lattice.add_mem h h)
    have hu' : -u ∉ L.lattice := fun h => hu (by simpa using L.lattice.neg_mem h)
    have a1 : ptOf l L ι ((t + u) + (t - u)) = ptOf l L ι (t + u) + ptOf l L ι (t - u) :=
      ptOf_add_generic l L ι _ _ hup hum (by convert htt using 2; ring) (by convert hu2 using 2; ring)
    have a2 : ptOf l L ι (t + u) = ptOf l L ι t + ptOf l L ι u :=
      ptOf_add_generic l L ι _ _ ht hu hup hum
    have a3 : ptOf l L ι (t + -u) = ptOf l L ι t + ptOf l L ι (-u) :=
      ptOf_add_generic l L ι _ _ ht hu' (by rwa [← sub_eq_add_neg]) (by rwa [sub_neg_eq_add])
    rw [h2, h1]
    have e : t + t = (t + u) + (t - u) := by ring
    rw [e, a1, a2, sub_eq_add_neg, a3, ptOf_neg]
    abel
  exact ptOf_add_generic l L ι s t hs ht hp hm

end Law

open Classical in

theorem PtOfAdd_of : PtOfAdd := by
  intro l _ L ι s t
  exact ptOf_add l L ι s t

end Formalism.L2.Th1.E
