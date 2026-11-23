import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationGenericRatioEqRestriction
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GeneratorNeZeroOfHeight

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField ReciprocityTheory.MultiplicativeHeights

theorem isMultiHomogeneous_mul' {R : Type*} [CommSemiring R] {B n : ℕ} {a a' : Fin B → ℕ}
    {f g : MvPolynomial (Fin B × Fin n) R} (hf : IsMultiHomogeneous a f)
    (hg : IsMultiHomogeneous a' g) : IsMultiHomogeneous (a + a') (f * g) := by
  classical
  unfold IsMultiHomogeneous at *
  intro s hs b
  obtain ⟨s1, hs1, s2, hs2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hs)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf s1 hs1 b, hg s2 hs2 b]

theorem isMultiHomogeneous_one {R : Type*} [CommSemiring R] {B n : ℕ} :
    IsMultiHomogeneous (0 : Fin B → ℕ) (1 : MvPolynomial (Fin B × Fin n) R) := by
  classical
  unfold IsMultiHomogeneous
  intro s hs b
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hs
  split_ifs at hs with h
  · subst h
    simp
  · exact absurd rfl hs

theorem height_one_eq_zero {K : Type} [Field K] [NumberField K] {B n : ℕ} (hn : 0 < n) :
    h0 (1 : MvPolynomial (Fin B × Fin n) K) = 0 := by
  classical
  first
    | simp [h0, gaussAbs, blockSphereMean]
    | simp [h0, gaussAbs, blockSphereMean, MvPolynomial.support_one]

theorem height_pow_multiHomogeneous {K : Type} [Field K] [NumberField K] {B n : ℕ} (hn : 0 < n)
    {g : MvPolynomial (Fin B × Fin n) K} {a : Fin B → ℕ} (hg0 : g ≠ 0)
    (hg : IsMultiHomogeneous a g) (e : ℕ) :
    g ^ e ≠ 0 ∧ IsMultiHomogeneous (e • a) (g ^ e) ∧ h0 (g ^ e) = e * h0 g := by
  induction e with
  | zero => simp [height_one_eq_zero hn, isMultiHomogeneous_one]
  | succ e ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨pow_ne_zero _ hg0, ?_, ?_⟩
    · rw [pow_succ, succ_nsmul]; exact isMultiHomogeneous_mul' h2 hg
    · rw [pow_succ, (ReciprocityTheory.MultiplicativeHeights.Closed.gauss_height_additivity K B n _ _ _ _ hn h1 hg0 h2 hg).1, h3]
      push_cast; ring

theorem height_prod_pow_multiHomogeneous {K : Type} [Field K] [NumberField K] {B n : ℕ} (hn : 0 < n) {ι' : Type*}
    (T : Finset ι') (g : ι' → MvPolynomial (Fin B × Fin n) K) (e : ι' → ℕ)
    (hg : ∀ i ∈ T, g i ≠ 0 ∧ ∃ a, IsMultiHomogeneous a (g i)) :
    (∏ i ∈ T, g i ^ e i) ≠ 0 ∧ (∃ a, IsMultiHomogeneous a (∏ i ∈ T, g i ^ e i)) ∧
      h0 (∏ i ∈ T, g i ^ e i) = ∑ i ∈ T, (e i : ℝ) * h0 (g i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [height_one_eq_zero hn]; exact ⟨0, isMultiHomogeneous_one⟩
  | insert q T hq ih =>
    obtain ⟨h1, ⟨a1, h2⟩, h3⟩ := ih fun i hi => hg i (Finset.mem_insert_of_mem hi)
    obtain ⟨hq0, aq, hqa⟩ := hg q (Finset.mem_insert_self q T)
    obtain ⟨p1, p2, p3⟩ := height_pow_multiHomogeneous hn hq0 hqa (e q)
    rw [Finset.prod_insert hq, Finset.sum_insert hq]
    refine ⟨mul_ne_zero p1 h1, ⟨_, isMultiHomogeneous_mul' p2 h2⟩, ?_⟩
    rw [(ReciprocityTheory.MultiplicativeHeights.Closed.gauss_height_additivity K B n _ _ _ _ hn p1 h1 p2 h2).1, p3, h3]

namespace Data

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

variable (d : Data K ι Ω WT A)

private lemma ratio_eq_of_eq_smul' {Ω' V : Type*} [Field Ω'] [AddCommGroup V] [Module Ω' V] {f g : V} {a : Ω'}
    (hg : g ≠ 0) (h : f = a • g) : ratio f g = a := by
  have hex : ∃ b : Ω', f = b • g := ⟨a, h⟩
  unfold ratio
  rw [dif_pos hex]
  have hc := hex.choose_spec
  exact smul_left_injective Ω' hg (hc.symm.trans h)

theorem ratio_linearCombination_expand (hd : d.AxH 𝒜) (x : Fin (d.N + 1) → K) (c : ι) :
    ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c) =
      ∑ j, algebraMap K (Ω c) (x j) * ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) := by
  haveI := hd.tower c
  have hg : d.w (d.jc c) c ≠ 0 := hd.w_base c
  have hspan : ∀ f ∈ 𝒜 c d.wL, ∃ a : Ω c, f = a • d.w (d.jc c) c := by
    intro f hf
    have hne : (⟨d.w (d.jc c) c, hd.w_mem _ c⟩ : 𝒜 c d.wL) ≠ 0 := by
      intro h0
      exact hg (congrArg Subtype.val h0)
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp (hd.finrank_one c d.wL) ⟨f, hf⟩
    exact ⟨a, (congrArg Subtype.val ha).symm⟩
  choose r hr using fun j => hspan (d.w j c) (hd.w_mem j c)
  have hrat : ∀ j, ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) = r j := fun j => ratio_eq_of_eq_smul' hg (hr j)
  simp only [hrat]
  apply ratio_eq_of_eq_smul' hg
  rw [Finset.sum_smul]
  unfold Data.wx
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [Pi.smul_apply, mul_smul, algebraMap_smul]
  conv_lhs => rw [hr j]

theorem untopD_le_untopD {u v : WithTop ℤ} (hu : u ≠ ⊤) (hv : v ≠ ⊤) (h : u ≤ v) :
    u.untopD 0 ≤ v.untopD 0 := by
  lift u to ℤ using hu
  lift v to ℤ using hv
  simpa using h

theorem ordMinMax_nonneg (hd : d.AxH 𝒜) (h : d.S1) (x : Fin (d.N + 1) → K) (c : ι)
    (hx : d.wx x c ≠ 0) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne)
    {w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)} (hw : w ∈ d.GoodP c p) :
    0 ≤ d.ordMM c (d.Wres c w) (d.wx x c) := by
  rcases d.PlaceTrivialOrPositive hd h c p hp w hw.1 with htr | ⟨hA, htriv, j0, hj0, hint, _⟩
  · obtain ⟨a, ha, hne⟩ := hw.2
    exact absurd (htr a ha) hne
  have hmem := d.linearCombination_mem_section hd x c
  rw [d.ordMinMax_eq_ratio_untop_sub hd c _ hA j0 hj0 hint hmem hx, sub_nonneg]
  set v := d.Wres c w
  have hb := hd.w_base c
  have hm := hd.w_mem (d.jc c) c
  apply untopD_le_untopD (hA.1.1 _ (d.ratio_base_ne_zero hd c (hd.w_mem j0 c) hj0))
    (hA.1.1 _ (d.ratio_base_ne_zero hd c hmem hx))
  rw [d.ratio_linearCombination_expand hd x c]
  apply AddValuation.map_le_sum
  intro j _
  by_cases hxj : x j = 0
  · rw [hxj, map_zero, zero_mul, v.map_zero]; exact le_top
  rw [v.map_mul, htriv _ hxj, zero_add,
    d.ratio_mul_ratio_height hd c (hd.w_mem j c) (hd.w_mem j0 c) hm hj0 hb, v.map_mul]
  exact le_add_of_nonneg_left (hint j)

theorem multiplicity_nonneg (hd : d.AxH 𝒜) (h : d.S1) (x : Fin (d.N + 1) → K) (c : ι)
    (hx : d.wx x c ≠ 0) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) :
    0 ≤ d.nPMM h c (d.wx x c) p := by
  unfold Data.nPMM
  apply finsum_nonneg
  intro w
  apply finsum_nonneg
  intro hw
  refine mul_nonneg ?_ (d.ordMinMax_nonneg hd h x c hx hp hw)
  first
    | positivity
    | exact Nat.cast_nonneg _

theorem height_substituted_eq_finsum (hd : d.AxH 𝒜) (h : d.S1) (x : Fin (d.N + 1) → K)
    (hx : ∀ c, d.wx x c ≠ 0) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) :
    d.translatedForm x F ≠ 0 ∧
    ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        (d.nPMM h c (d.wx x c) p : ℝ) * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p) =
      ReciprocityTheory.MultiplicativeHeights.h0 (d.translatedForm x F) := by
  classical
  have hmem := d.linearCombination_mem_section hd x c
  obtain ⟨κ1, hκ1, e1⟩ := d.SpecialFibreFactorization hd h c F hF x (hx c)
  have hS := (d.good_primes_properties hd h c).2.2.2 _ hmem (hx c)
  set T := hS.toFinset
  set n : Ideal (KTp K d.D d.N) → ℤ := fun p => d.nPMM h c (d.wx x c) p with hn
  have hT : ∀ p, p ∈ T ↔ p ∈ d.HtOne ∧ n p ≠ 0 := fun p => by rw [Set.Finite.mem_toFinset]; rfl
  have hgood : ∀ p ∈ T, d.gen p ≠ 0 ∧ ∃ a, IsMultiHomogeneous a (d.gen p) := by
    intro p hpT
    obtain ⟨hp, hnp⟩ := (hT p).mp hpT
    refine ⟨d.gen_ne_zero_of_htOne hp, _, (d.good_primes_properties hd h c).2.1 p hp ?_⟩
    obtain ⟨w, hw, _⟩ := exists_ne_zero_of_finsum_mem_ne_zero' hnp
    exact ⟨w, hw⟩
  set e : Ideal (KTp K d.D d.N) → ℕ := fun p => (n p).toNat with he
  have hne : ∀ p ∈ d.HtOne, n p = (e p : ℤ) := fun p hp =>
    (Int.toNat_of_nonneg (d.multiplicity_nonneg hd h x c (hx c) hp)).symm
  obtain ⟨P0, ⟨aP, hPm⟩, hPh⟩ := height_prod_pow_multiHomogeneous (K := K) (Nat.succ_pos d.N) T (fun p => d.gen p) e hgood
  have hprod : (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ n p) =
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (∏ p ∈ T, d.gen p ^ e p) := by
    rw [finprod_mem_eq_prod_of_inter_mulSupport_eq _ (t := T), map_prod]
    · refine Finset.prod_congr rfl fun p hpT => ?_
      rw [hne p ((hT p).mp hpT).1, zpow_natCast, map_pow]
    · ext p
      simp only [Set.mem_inter_iff, Function.mem_mulSupport, Finset.mem_coe, hT]
      constructor
      · rintro ⟨hp, h1⟩
        refine ⟨⟨hp, fun h0 => h1 ?_⟩, h1⟩
        rw [h0, zpow_zero]
      · rintro ⟨⟨hp, _⟩, h1⟩; exact ⟨hp, h1⟩
  have hFx : d.translatedForm x F = MvPolynomial.C κ1 * ∏ p ∈ T, d.gen p ^ e p := by
    apply IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
    unfold translatedForm
    rw [e1, hprod, map_mul, ← MvPolynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply K (KTp K d.D d.N) (KTf K d.D d.N)]
  refine ⟨by rw [hFx]; exact mul_ne_zero (MvPolynomial.C_ne_zero.mpr hκ1) P0, ?_⟩
  rw [hFx, (ReciprocityTheory.MultiplicativeHeights.Closed.gauss_height_additivity K (d.D + 1) (d.N + 1) aP aP _ _ (Nat.succ_pos _) P0 P0 hPm hPm).2
    κ1 hκ1, hPh]
  rw [finsum_mem_eq_sum_of_inter_support_eq _ (t := T)]
  · refine Finset.sum_congr rfl fun p hpT => ?_
    rw [show ((d.nPMM h c (d.wx x c) p : ℤ) : ℝ) = ((e p : ℤ) : ℝ) from
      congrArg _ (hne p ((hT p).mp hpT).1)]
    simp
  · ext p
    simp only [Set.mem_inter_iff, Function.mem_support, Finset.mem_coe, hT]
    constructor
    · rintro ⟨hp, h1⟩
      refine ⟨⟨hp, fun h0 => h1 ?_⟩, h1⟩
      simp only [hn] at h0; rw [h0]; simp
    · rintro ⟨⟨hp, _⟩, h1⟩; exact ⟨hp, h1⟩

theorem fZ_and_substituted_ne_zero (hd : d.AxH 𝒜) (h : d.S1) (x : Fin (d.N + 1) → K)
    (hx : ∀ c, d.wx x c ≠ 0) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) :
    F ≠ 0 ∧ d.translatedForm x F ≠ 0 := by
  have hne := (d.height_substituted_eq_finsum hd h x hx c F hF).1
  refine ⟨fun h0 => hne ?_, hne⟩
  rw [h0]
  first
    | simp [Data.translatedForm]
    | exact map_zero _

end Data

end ReciprocityTheory.ChartRestriction.G.T0
