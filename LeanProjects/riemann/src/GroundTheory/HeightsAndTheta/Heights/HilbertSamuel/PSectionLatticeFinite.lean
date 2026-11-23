import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionLatticeFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SectionLatticeFinite

section Groups

variable {G G' : Type*} [AddCommGroup G] [AddCommGroup G']

theorem fg_of_le_fg {H H' : AddSubgroup G} (h : H ≤ H') (hH' : H'.FG) : H.FG := by
  rw [← AddSubgroup.toIntSubmodule_toAddSubgroup H, ← Submodule.fg_iff_addSubgroup_fg]
  rw [← AddSubgroup.toIntSubmodule_toAddSubgroup H', ← Submodule.fg_iff_addSubgroup_fg] at hH'
  have := isNoetherian_of_fg_of_noetherian _ hH'
  have := isNoetherian_of_le (AddSubgroup.toIntSubmodule.monotone h)
  exact Module.Finite.iff_fg.mp inferInstance

theorem fg_map (f : G →+ G') {H : AddSubgroup G} (hH : H.FG) : (H.map f).FG := by
  classical
  obtain ⟨S, hS⟩ := hH
  exact ⟨S.image f, by rw [Finset.coe_image, ← AddMonoidHom.map_closure, hS]⟩

end Groups

section Homog

variable {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]

theorem homog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

theorem homog_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem homog_neg {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (-f) a := by
  intro m hm k
  rw [MvPolynomial.support_neg] at hm
  exact hf m hm k

theorem homog_one : IsMultiHomog (1 : MRing ι) 0 := by
  classical
  intro m hm k
  rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
  subst hm
  simp

theorem homog_zero (a : K → ℕ) : IsMultiHomog (0 : MRing ι) a := by
  intro m hm
  simp at hm

open Classical in
theorem homog_X (p : Σ k, ι k) : IsMultiHomog (X p : MRing ι) (Pi.single p.1 1) := by
  intro m hm k
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  obtain ⟨k0, i0⟩ := p
  by_cases h : k = k0
  · subst h
    simp [Finsupp.single_apply]
  · have : ∀ j : ι k, (⟨k0, i0⟩ : Σ k, ι k) ≠ ⟨k, j⟩ := fun j e => h (congrArg Sigma.fst e).symm
    simp [h]

end Homog

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem aeval_scale {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) (μ : K → Ω)
    (y : (Σ k, ι k) → Ω) :
    aeval (fun p => μ p.1 * y p) g = (∏ k, μ k ^ d k) * aeval y g := by
  classical
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial, Finsupp.prod, Finsupp.prod]
  simp only [mul_pow, Finset.prod_mul_distrib]
  have hμ : ∏ p ∈ m.support, μ p.1 ^ m p = ∏ k, μ k ^ d k := by
    rw [Finset.prod_subset (Finset.subset_univ m.support)
      (fun p _ hp => by rw [Finsupp.notMem_support_iff.mp hp, pow_zero]), Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, μ k ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hg m hm k]
  rw [hμ]
  ring

theorem secM_fg (y : (Σ k, ι k) → Ω) (d : K → ℕ) : (secM y d).FG := by
  classical
  set M : (Σ k, ι k) →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun p => d p.1) with hM
  set S : Set Ω := (fun m : (Σ k, ι k) →₀ ℕ => aeval y (monomial m (1 : ℤ))) '' Set.Iic M
  have hS : S.Finite := (Set.finite_Iic M).image _
  have hle : Submodule.span ℤ {s | ∃ g : MRing ι, IsMultiHomog g d ∧ aeval y g = s} ≤
      Submodule.span ℤ S := by
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, g.as_sum, map_sum]
    refine Submodule.sum_mem _ fun m hm => ?_
    have hmon : aeval y (monomial m (coeff m g)) = (coeff m g) • aeval y (monomial m (1 : ℤ)) := by
      rw [aeval_monomial, aeval_monomial, zsmul_eq_mul]
      simp
    rw [hmon]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, ?_, rfl⟩)
    rw [Set.mem_Iic, Finsupp.le_iff]
    intro p _
    rw [hM, Finsupp.coe_equivFunOnFinite_symm]
    show m p ≤ d p.1
    rw [← hg m hm p.1]
    exact Finset.single_le_sum (f := fun i => m ⟨p.1, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ p.2)
  have hfg : (Submodule.span ℤ S).FG := ⟨hS.toFinset, by simp⟩
  unfold secM
  rw [← Submodule.fg_iff_addSubgroup_fg]
  have := isNoetherian_of_fg_of_noetherian _ hfg
  have := isNoetherian_of_le hle
  exact Module.Finite.iff_fg.mp inferInstance

omit [∀ k, Fintype (ι k)] in

theorem chartLat_le_nm (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) : chartLat y a τ ≤ chartLatNm y a τ :=
  fun _ hs c hc => isIntegral_algebraMap (x := (⟨_, hs c hc⟩ : chartRingZ y c))

def fnField (y : (Σ k, ι k) → Ω) : Subfield Ω where
  carrier := {s | ∃ (d : K → ℕ) (g h : MRing ι), IsMultiHomog g d ∧ IsMultiHomog h d ∧
    aeval y h ≠ 0 ∧ aeval y g = s * aeval y h}
  mul_mem' := by
    rintro s t ⟨d, g, h, hg, hh, hh0, hgs⟩ ⟨e, g', h', hg', hh', hh0', hgt⟩
    exact ⟨d + e, g * g', h * h', homog_mul hg hg', homog_mul hh hh',
      by rw [map_mul]; exact mul_ne_zero hh0 hh0', by rw [map_mul, map_mul, hgs, hgt]; ring⟩
  one_mem' := ⟨0, 1, 1, homog_one, homog_one, by simp, by simp⟩
  add_mem' := by
    rintro s t ⟨d, g, h, hg, hh, hh0, hgs⟩ ⟨e, g', h', hg', hh', hh0', hgt⟩
    refine ⟨d + e, g * h' + h * g', h * h', homog_add (homog_mul hg hh') (homog_mul hh hg'),
      homog_mul hh hh', by rw [map_mul]; exact mul_ne_zero hh0 hh0', ?_⟩
    rw [map_add, map_mul, map_mul, map_mul, hgs, hgt]
    ring
  zero_mem' := ⟨0, 0, 1, homog_zero 0, homog_one, by simp, by simp⟩
  neg_mem' := by
    rintro s ⟨d, g, h, hg, hh, hh0, hgs⟩
    exact ⟨d, -g, h, homog_neg hg, hh, hh0, by rw [map_neg, hgs]; ring⟩
  inv_mem' := by
    rintro s ⟨d, g, h, hg, hh, hh0, hgs⟩
    by_cases hs : s = 0
    · subst hs
      rw [inv_zero]
      exact ⟨0, 0, 1, homog_zero 0, homog_one, by simp, by simp⟩
    · refine ⟨d, h, g, hh, hg, ?_, ?_⟩
      · rw [hgs]
        exact mul_ne_zero hs hh0
      · rw [hgs, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]

omit [Fintype K] in
theorem mem_fnField (y : (Σ k, ι k) → Ω) {s : Ω} : s ∈ fnField y ↔ ∃ (d : K → ℕ) (g h : MRing ι),
    IsMultiHomog g d ∧ IsMultiHomog h d ∧ aeval y h ≠ 0 ∧ aeval y g = s * aeval y h := Iff.rfl

omit [Fintype K] in
open Classical in

theorem ratio_mem (y : (Σ k, ι k) → Ω) (p : Σ k, ι k) (q : ι p.1) (hq : y ⟨p.1, q⟩ ≠ 0) :
    y p / y ⟨p.1, q⟩ ∈ fnField y :=
  ⟨Pi.single p.1 1, X p, X ⟨p.1, q⟩, homog_X p, homog_X ⟨p.1, q⟩, by rw [aeval_X]; exact hq,
    by rw [aeval_X, aeval_X, div_mul_cancel₀ _ hq]⟩

omit [Fintype K] in

theorem chartRingZ_le (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {x : Ω}
    (hx : x ∈ chartRingZ y c) : x ∈ fnField y := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact ratio_mem y p (c p.1) (hc p.1)
  | algebraMap r =>
    rw [algebraMap_int_eq, eq_intCast]
    exact intCast_mem _ r
  | add x z _ _ hx hz => exact add_mem hx hz
  | mul x z _ _ hx hz => exact mul_mem hx hz

def yr (y : (Σ k, ι k) → Ω) (c0 : ∀ k, ι k) (hc0 : ∀ k, y ⟨k, c0 k⟩ ≠ 0) : (Σ k, ι k) → fnField y :=
  fun p => ⟨y p / y ⟨p.1, c0 p.1⟩, ratio_mem y p (c0 p.1) (hc0 p.1)⟩

section Rescaled

variable (y : (Σ k, ι k) → Ω) (c0 : ∀ k, ι k) (hc0 : ∀ k, y ⟨k, c0 k⟩ ≠ 0)

omit [Fintype K] in
theorem coe_yr (p : Σ k, ι k) : (yr y c0 hc0 p : Ω) = y p / y ⟨p.1, c0 p.1⟩ := rfl

omit [Fintype K] in
theorem yr_self (k : K) : yr y c0 hc0 ⟨k, c0 k⟩ = 1 :=
  Subtype.ext (div_self (hc0 k))

omit [Fintype K] in
theorem coe_aeval_yr (g : MRing ι) :
    ((aeval (yr y c0 hc0) g : fnField y) : Ω) = aeval (fun p => y p / y ⟨p.1, c0 p.1⟩) g := by
  induction g using MvPolynomial.induction_on with
  | C n => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p q hp => simp [hp, coe_yr]

theorem coe_aeval_yr_homog {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) :
    ((aeval (yr y c0 hc0) g : fnField y) : Ω) = (∏ k, (y ⟨k, c0 k⟩)⁻¹ ^ d k) * aeval y g := by
  have h := aeval_scale hg (fun k => (y ⟨k, c0 k⟩)⁻¹) y
  have hf : (fun p : Σ k, ι k => (fun k => (y ⟨k, c0 k⟩)⁻¹) p.1 * y p) =
      fun p => y p / y ⟨p.1, c0 p.1⟩ := funext fun p => (div_eq_inv_mul _ _).symm
  rw [hf] at h
  rw [coe_aeval_yr, h]

omit [∀ k, Fintype (ι k)] in
include hc0 in
theorem prod_inv_ne_zero (d : K → ℕ) : (∏ k, (y ⟨k, c0 k⟩)⁻¹ ^ d k) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (inv_ne_zero (hc0 k))

theorem birational_yr : Birational (yr y c0 hc0) := by
  rintro ⟨s, hs⟩
  obtain ⟨d, g, h, hg, hh, hh0, hgs⟩ := (mem_fnField y).mp hs
  refine ⟨d, g, h, hg, hh, ?_, ?_⟩
  · intro h0
    have h1 : ((aeval (yr y c0 hc0) h : fnField y) : Ω) = 0 := by rw [h0]; rfl
    rw [coe_aeval_yr_homog y c0 hc0 hh] at h1
    exact hh0 ((mul_eq_zero.mp h1).resolve_left (prod_inv_ne_zero y c0 hc0 d))
  · apply Subtype.ext
    rw [Subfield.coe_mul, coe_aeval_yr_homog y c0 hc0 hg, coe_aeval_yr_homog y c0 hc0 hh, hgs]
    show _ = s * _
    ring

omit [Fintype K] in

theorem map_chartRingZ_yr (c : ∀ k, ι k) :
    (chartRingZ (yr y c0 hc0) c).map (fnField y).subtype.toIntAlgHom = chartRingZ y c := by
  rw [chartRingZ, chartRingZ, AlgHom.map_adjoin, ← Set.range_comp]
  congr 2
  funext p
  show (y p / y ⟨p.1, c0 p.1⟩) / (y ⟨p.1, c p.1⟩ / y ⟨p.1, c0 p.1⟩) = y p / y ⟨p.1, c p.1⟩
  rw [div_div_div_cancel_right₀ (hc0 p.1)]

omit [Fintype K] in
theorem mem_chartRingZ_yr (c : ∀ k, ι k) {x : fnField y} (hx : (x : Ω) ∈ chartRingZ y c) :
    x ∈ chartRingZ (yr y c0 hc0) c := by
  rw [← map_chartRingZ_yr y c0 hc0 c] at hx
  obtain ⟨x', hx', he⟩ := Subalgebra.mem_map.mp hx
  have : x' = x := Subtype.ext he
  rwa [← this]

end Rescaled

theorem proof (hC : KH.CondStatement) : SectionLatticeFinite.Statement := by
  intro K _ ι _ Ω _ y a n hy
  classical
  choose c0 hc0 using hy
  obtain ⟨b, hb⟩ : ∃ b : K → ℕ, ∀ k, 1 ≤ b k ∧ (n : ℤ) * a k ≤ b k :=
    ⟨fun k => ((n : ℤ) * a k).toNat + 1, fun k => ⟨Nat.le_add_left 1 _, by
      have := Int.self_le_toNat ((n : ℤ) * a k); push_cast; omega⟩⟩
  set y' := yr y c0 hc0 with hy'
  have hy'1 : ∀ k, y' ⟨k, c0 k⟩ = 1 := yr_self y c0 hc0
  obtain ⟨k0, cf, -, hcf0, hcf⟩ := hC K ι (fnField y) y' b (fun k => (hb k).1)
    (fun k => ⟨c0 k, by rw [hy'1]; exact one_ne_zero⟩) (birational_yr y c0 hc0)

  have hA : ∀ s ∈ chartLat y' a n, s ∈ chartLat y' (fun k => (b k : ℤ)) 1 := by
    intro s hs c hc
    have hgen : ∀ k, (y' ⟨k, c k⟩)⁻¹ ∈ chartRingZ y' c := by
      intro k
      have h1 : (y' ⟨k, c k⟩)⁻¹ = y' ⟨k, c0 k⟩ / y' ⟨k, c k⟩ := by rw [hy'1, one_div]
      rw [h1]
      exact Algebra.subset_adjoin ⟨⟨k, c0 k⟩, rfl⟩
    have hsplit : ∏ k, y' ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (b k : ℤ))) =
        (∏ k, y' ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) *
          ∏ k, (y' ⟨k, c k⟩)⁻¹ ^ ((b k : ℤ) - n * a k).toNat := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [inv_pow, ← zpow_natCast,
        Int.toNat_of_nonneg (show (0 : ℤ) ≤ (b k : ℤ) - n * a k by linarith [(hb k).2]), ← zpow_neg,
        ← zpow_add₀ (hc k)]
      congr 1
      push_cast
      ring
    show s * ∏ k, y' ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (b k : ℤ))) ∈ chartRingZ y' c
    rw [hsplit, ← mul_assoc]
    exact Subalgebra.mul_mem _ (hs c hc)
      (Subalgebra.prod_mem _ fun k _ => Subalgebra.pow_mem _ (hgen k) _)

  have hB : (chartLat y' a n).FG := by
    refine fg_of_le_fg (H' := (secM y' (fun κ => (1 + k0) * b κ)).map
      (AddMonoidHom.mulLeft (aeval y' cf)⁻¹)) ?_ (fg_map _ (secM_fg y' _))
    intro s hs
    refine AddSubgroup.mem_map.mpr ⟨aeval y' cf * s, hcf 1 s (chartLat_le_nm y' _ 1 (hA s hs)), ?_⟩
    show (aeval y' cf)⁻¹ * (aeval y' cf * s) = s
    rw [← mul_assoc, inv_mul_cancel₀ hcf0, one_mul]

  set m : Ω := ∏ k, y ⟨k, c0 k⟩ ^ ((n : ℤ) * a k) with hm
  refine fg_of_le_fg (H' := (chartLat y' a n).map
    ((AddMonoidHom.mulRight m).comp (fnField y).subtype.toAddMonoidHom)) ?_ (fg_map _ hB)
  intro s hs
  set t : Ω := s * ∏ k, y ⟨k, c0 k⟩ ^ (-((n : ℤ) * a k)) with ht
  have htF : t ∈ fnField y := chartRingZ_le y c0 hc0 (hs c0 hc0)
  refine AddSubgroup.mem_map.mpr ⟨⟨t, htF⟩, ?_, ?_⟩
  · intro c hc
    have hcy : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
      intro k h0
      apply hc k
      apply Subtype.ext
      show y ⟨k, c k⟩ / y ⟨k, c0 k⟩ = 0
      rw [h0, zero_div]
    apply mem_chartRingZ_yr y c0 hc0 c
    have e1 : ∀ p, (fnField y).subtype (y' p) = y p / y ⟨p.1, c0 p.1⟩ := fun p => rfl
    have hco : (fnField y).subtype (⟨t, htF⟩ * ∏ k, y' ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) =
        s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k)) := by
      rw [map_mul, map_prod]
      simp only [map_zpow₀, e1]
      show t * _ = _
      rw [ht, mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl fun k _ => ?_
      show y ⟨k, c0 k⟩ ^ (-((n : ℤ) * a k)) * (y ⟨k, c k⟩ / y ⟨k, c0 k⟩) ^ (-((n : ℤ) * a k)) =
        y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))
      rw [div_zpow, mul_div_assoc', mul_div_right_comm, div_self (zpow_ne_zero _ (hc0 k)), one_mul]
    show (fnField y).subtype (⟨t, htF⟩ * ∏ k, y' ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) ∈ chartRingZ y c
    rw [hco]
    exact hs c hcy
  · show t * m = s
    rw [ht, hm, mul_assoc, ← Finset.prod_mul_distrib,
      Finset.prod_eq_one (fun k _ => by rw [← zpow_add₀ (hc0 k), neg_add_cancel, zpow_zero]), mul_one]

end SectionLatticeFinite

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
