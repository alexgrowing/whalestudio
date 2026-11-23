import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.UniformizerOfResidueIndep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormByPlaces

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

theorem ratio_eq_of_eq_smul {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V] {f g : V} {a : Ω}
    (hg : g ≠ 0) (h : f = a • g) : ratio f g = a := by
  unfold ratio
  have hex : ∃ a' : Ω, f = a' • g := ⟨a, h⟩
  rw [dif_pos hex]
  have hs : a • g = hex.choose • g := by
    rw [← h]
    exact hex.choose_spec
  exact (smul_left_injective Ω hg hs).symm

theorem ratio_self_height {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V] {f : V}
    (hf : f ≠ 0) : ratio (Ω := Ω) f f = 1 := ratio_eq_of_eq_smul hf (one_smul Ω f).symm

theorem untopD_nonneg {x : WithTop ℤ} (hx : 0 ≤ x) : 0 ≤ WithTop.untopD 0 x := by
  induction x with
  | top => simp
  | coe a => simpa using hx

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem eq_ratio_smul_on_line {hd : d.AxH 𝒜} {c : ι} {G : WT} {f g : A c} (hf : f ∈ 𝒜 c G) (hg : g ∈ 𝒜 c G)
    (hg0 : g ≠ 0) : f = ratio (Ω := Ω c) f g • g := by
  have h1 := hd.finrank_one c G
  have hg' : (⟨g, hg⟩ : 𝒜 c G) ≠ 0 := fun h => hg0 (by simpa using congrArg Subtype.val h)
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hg').1 h1 ⟨f, hf⟩
  have hfa : f = a • g := by
    have := congrArg Subtype.val ha
    simpa using this.symm
  rw [ratio_eq_of_eq_smul hg0 hfa]
  exact hfa

theorem ratio_line_expansion (hd : d.AxH 𝒜) (c : ι) (j0 : Fin (d.N + 1)) (hj0 : d.w j0 c ≠ 0) :
    d.rationalBaseRow c = algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c)) *
      ∑ j, d.sH c (MvPolynomial.X (0, j)) *
        algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w j0 c)) := by
  have hjc := hd.w_base c
  have hmul : ∀ j, ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) =
      ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) * ratio (Ω := Ω c) (d.w j c) (d.w j0 c) := by
    intro j
    have h1 := eq_ratio_smul_on_line d (hd := hd) (hd.w_mem j c) (hd.w_mem j0 c) hj0
    have h2 := eq_ratio_smul_on_line d (hd := hd) (hd.w_mem j0 c) (hd.w_mem (d.jc c) c) hjc
    apply ratio_eq_of_eq_smul hjc
    calc d.w j c = ratio (Ω := Ω c) (d.w j c) (d.w j0 c) • d.w j0 c := h1
      _ = ratio (Ω := Ω c) (d.w j c) (d.w j0 c) • (ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) • d.w (d.jc c) c) := by
          rw [← h2]
      _ = _ := by rw [smul_smul, mul_comm]
  unfold rationalBaseRow
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hmul j, map_mul]
  ring

theorem lineRatio_ne_zero (hd : d.AxH 𝒜) (c : ι) : d.rationalBaseRow c ≠ 0 := by
  have hr1 : ratio (Ω := Ω c) (d.w (d.jc c) c) (d.w (d.jc c) c) = 1 := ratio_self_height (hd.w_base c)
  have e : d.rationalBaseRow c = algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)
      (MvPolynomial.X (Sum.inl ()) + ∑ k, MvPolynomial.X (Sum.inr ((0 : Fin (d.D + 1)), k)) *
        MvPolynomial.C (ratio (Ω := Ω c) (d.w ((d.jc c).succAbove k) c) (d.w (d.jc c) c))) := by
    unfold rationalBaseRow sH sHom
    rw [Fin.sum_univ_succAbove _ (d.jc c)]
    simp only [MvPolynomial.aeval_X, sImg, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same,
      Fin.insertNth_apply_succAbove, if_true, hr1, map_one, mul_one, map_add, map_sum, map_mul]
    congr 1
  rw [e]
  intro h0
  have hinj := IsFractionRing.injective (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)
  rw [← map_zero (algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N))] at h0
  have h1 := congrArg (MvPolynomial.coeff (Finsupp.single (Sum.inl ()) 1)) (hinj h0)
  simp [MvPolynomial.coeff_X', MvPolynomial.coeff_sum, MvPolynomial.coeff_X_mul', Finsupp.single_eq_single_iff] at h1

end Data

end ReciprocityTheory.ChartRestriction.G.T0

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem lineRatio_val_nonneg (c : ι) (p : Ideal (KTp K d.D d.N))
    (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (hw : w ∈ d.OverP c p)
    (htriv : ∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0) : 0 ≤ w (d.rationalBaseRow c) := by
  unfold rationalBaseRow
  refine AddValuation.map_le_sum w fun j _ => ?_
  rw [AddValuation.map_mul]
  have h1 : 0 ≤ w (d.sH c (MvPolynomial.X (0, j))) := (hw.2 _).1
  have h2 : 0 ≤ w (algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))) := by
    by_cases ha : ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) = 0
    · rw [ha, map_zero, AddValuation.map_zero]
      exact le_top
    · have h3 := htriv _ ha
      unfold Wres at h3
      exact le_of_eq h3.symm
  exact add_nonneg h1 h2

theorem good_valuation_balance (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (p : Ideal (KTp K d.D d.N)) (hp : p ∈ d.HtOne)
    (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (hw : w ∈ d.GoodP c p) :
    WithTop.untopD 0 (w (d.rationalBaseRow c)) + d.ordMM c (d.Wres c w) (d.w (d.jc c) c) = 0 := by
  obtain ⟨hwO, a, ha, hwa⟩ := hw
  rcases d.PlaceTrivialOrPositive hd h c p hp w hwO with htriv | ⟨hAdm, -, j0, hj0, hmin, hY⟩
  · exact absurd (htriv a ha) hwa
  have hjc := hd.w_base c
  have hsm : ∀ j, d.w j c ≠ 0 → ((d.ord c (d.Wres c w) d.wL (d.w j c) : ℤ) : WithTop ℤ) =
      d.Wres c w (ratio (Ω := Ω c) (d.w j c) (d.w j0 c)) + (d.ord c (d.Wres c w) d.wL (d.w j0 c) : WithTop ℤ) := by
    intro j hj
    have hl := eq_ratio_smul_on_line d (hd := hd) (hd.w_mem j c) (hd.w_mem j0 c) hj0
    have hr0 : ratio (Ω := Ω c) (d.w j c) (d.w j0 c) ≠ 0 := by
      intro h0; rw [h0, zero_smul] at hl; exact hj hl
    conv_lhs => rw [hl]
    exact hd.ord_smul c _ hAdm _ (hd.w_mem j0 c) hj0 hr0
  have hge : ∀ j, d.w j c ≠ 0 →
      d.ord c (d.Wres c w) d.wL (d.w j0 c) ≤ d.ord c (d.Wres c w) d.wL (d.w j c) := by
    intro j hj
    have h1 : ((d.ord c (d.Wres c w) d.wL (d.w j0 c) : ℤ) : WithTop ℤ) ≤
        (d.ord c (d.Wres c w) d.wL (d.w j c) : WithTop ℤ) := by
      rw [hsm j hj]; exact le_add_of_nonneg_left (hmin j)
    exact_mod_cast h1
  have hinf : (⨅ j : {j // d.w j c ≠ 0}, d.ord c (d.Wres c w) d.wL (d.w j c)) =
      d.ord c (d.Wres c w) d.wL (d.w j0 c) := by
    haveI : Nonempty {j // d.w j c ≠ 0} := ⟨(⟨j0, hj0⟩ : {j // d.w j c ≠ 0})⟩
    apply le_antisymm
    · exact ciInf_le (Set.finite_range _).bddBelow (⟨j0, hj0⟩ : {j // d.w j c ≠ 0})
    · exact le_ciInf fun j => hge j.1 j.2
  have hl1 := eq_ratio_smul_on_line d (hd := hd) (hd.w_mem j0 c) (hd.w_mem (d.jc c) c) hjc
  have hl2 := eq_ratio_smul_on_line d (hd := hd) (hd.w_mem (d.jc c) c) (hd.w_mem j0 c) hj0
  have hprod : ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) * ratio (Ω := Ω c) (d.w (d.jc c) c) (d.w j0 c) = 1 := by
    have e : d.w j0 c = (ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) * ratio (Ω := Ω c) (d.w (d.jc c) c) (d.w j0 c)) • d.w j0 c := by
      rw [← smul_smul, ← hl2, ← hl1]
    rw [← ratio_eq_of_eq_smul (Ω := Ω c) hj0 e, ratio_self_height (Ω := Ω c) hj0]
  have hr1ne : ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) ≠ 0 := fun h0 => by rw [h0, zero_smul] at hl1; exact hj0 hl1
  have hr2ne : ratio (Ω := Ω c) (d.w (d.jc c) c) (d.w j0 c) ≠ 0 := fun h0 => by rw [h0, zero_smul] at hl2; exact hjc hl2
  obtain ⟨m1, hm1⟩ := WithTop.ne_top_iff_exists.1
    (show d.Wres c w (ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c)) ≠ ⊤ from fun h0 => hr1ne ((AddValuation.top_iff _).1 h0))
  obtain ⟨m2, hm2⟩ := WithTop.ne_top_iff_exists.1
    (show d.Wres c w (ratio (Ω := Ω c) (d.w (d.jc c) c) (d.w j0 c)) ≠ ⊤ from fun h0 => hr2ne ((AddValuation.top_iff _).1 h0))
  have hsum : ((m1 + m2 : ℤ) : WithTop ℤ) = 0 := by
    rw [WithTop.coe_add, hm1, hm2, ← AddValuation.map_mul, hprod, AddValuation.map_one]
  have hsum' : m1 + m2 = 0 := by exact_mod_cast hsum
  have hjcv := hsm (d.jc c) hjc
  rw [← hm2] at hjcv
  have hjcv' : d.ord c (d.Wres c w) d.wL (d.w (d.jc c) c) = m2 + d.ord c (d.Wres c w) d.wL (d.w j0 c) := by
    exact_mod_cast hjcv
  rw [d.ratio_line_expansion hd c j0 hj0, AddValuation.map_mul, hY, add_zero]
  change WithTop.untopD 0 (d.Wres c w (ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c))) + d.ordMM c (d.Wres c w) (d.w (d.jc c) c) = 0
  rw [← hm1, WithTop.untopD_coe]
  unfold ordMM
  rw [hinf, hjcv']
  omega

end Data

end ReciprocityTheory.ChartRestriction.G.T0

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem generator_ne_zero_of_height (p : Ideal (KTp K d.D d.N)) (hp : p ∈ d.HtOne) : d.gen p ≠ 0 := by
  intro h0
  have e := d.gen_span hp
  rw [h0, Ideal.span_singleton_eq_bot.2 rfl] at e
  have h1 := hp.2
  rw [e, Ideal.height_bot] at h1
  exact zero_ne_one h1

theorem componentForm_poly (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    ∃ F : KTp K d.D d.N, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c ∧ F ≠ 0 := by
  classical
  have hy : d.rationalBaseRow c ≠ 0 := d.lineRatio_ne_zero hd c
  obtain ⟨hfin, hnb⟩ := d.norm_by_places hd h c
  obtain ⟨hT, κ, hκ, hN⟩ := hnb (d.rationalBaseRow c) hy
  obtain ⟨e1, he1⟩ : ∃ e1 : Ideal (KTp K d.D d.N) → ℤ, ∀ p, e1 p = ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.OverP c p),
      (d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c)) := ⟨_, fun _ => rfl⟩
  simp only [← he1] at hN
  have hg0 : ∀ p ∈ d.HtOne, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ≠ 0 := fun p hp =>
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (d.generator_ne_zero_of_height p hp)
  have hzero : ∀ p ∈ d.HtOne, p ∉ {p | p ∈ d.HtOne ∧ ∃ w ∈ d.OverP c p, w (d.rationalBaseRow c) ≠ 0} → e1 p = 0 ∧ d.nPMM h c (d.w (d.jc c) c) p = 0 := by
    intro p hp hpT
    have hw0 : ∀ w ∈ d.OverP c p, w (d.rationalBaseRow c) = 0 := fun w hw => by
      by_contra hne
      exact hpT ⟨hp, w, hw, hne⟩
    constructor
    · rw [he1, finsum_mem_congr rfl (fun w hw => (show (d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c)) = 0 by
        rw [hw0 w hw]; simp)), finsum_mem_zero _]
    · unfold nPMM
      refine (finsum_mem_congr rfl (fun w hw => ?_)).trans (finsum_mem_zero _)
      have h1 := d.good_valuation_balance hd h c p hp w hw
      rw [hw0 w hw.1] at h1
      simp at h1
      show (d.fze h c w : ℤ) * d.ordMM c (d.Wres c w) (d.w (d.jc c) c) = 0
      rw [h1, mul_zero]
  have hnn : ∀ p ∈ d.HtOne, 0 ≤ e1 p + d.nPMM h c (d.w (d.jc c) c) p := by
    intro p hp
    have hOf := (hfin p hp)
    have hGsub : d.GoodP c p ⊆ d.OverP c p := fun w hw => hw.1
    have hGf : (d.GoodP c p).Finite := hOf.subset hGsub
    have hRf : (d.OverP c p \ d.GoodP c p).Finite := hOf.diff
    rw [he1, ← Set.union_diff_cancel hGsub, finsum_mem_union Set.disjoint_sdiff_right hGf hRf]
    unfold nPMM
    rw [add_right_comm, ← finsum_mem_add_distrib hGf]
    have hG0 : ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
        ((d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c)) +
          (d.fze h c w : ℤ) * d.ordMM c (d.Wres c w) (d.w (d.jc c) c)) = 0 := by
      rw [finsum_mem_congr rfl (fun w hw => by rw [← mul_add, d.good_valuation_balance hd h c p hp w hw, mul_zero]),
        finsum_mem_zero _]
    rw [hG0, zero_add, finsum_mem_eq_finite_toFinset_sum _ hRf]
    refine Finset.sum_nonneg fun w hw => ?_
    rw [Set.Finite.mem_toFinset] at hw
    have htriv : ∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0 := by
      intro a ha
      by_contra hne
      exact hw.2 ⟨hw.1, a, ha, hne⟩
    exact mul_nonneg (Nat.cast_nonneg _) (untopD_nonneg (d.lineRatio_val_nonneg c p w hw.1 htriv))
  have hms1 : (d.HtOne ∩ Function.mulSupport fun p => algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ e1 p).Finite := by
    refine hT.subset fun p ⟨hp, hne⟩ => ?_
    by_contra hpT
    exact hne (by simp only [(hzero p hp hpT).1, zpow_zero])
  have hms2 : (d.HtOne ∩ Function.mulSupport fun p =>
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.w (d.jc c) c) p).Finite := by
    refine hT.subset fun p ⟨hp, hne⟩ => ?_
    by_contra hpT
    exact hne (by simp only [(hzero p hp hpT).2, zpow_zero])
  have hms3 : (d.HtOne ∩ Function.mulSupport fun p => d.gen p ^ (e1 p + d.nPMM h c (d.w (d.jc c) c) p).toNat).Finite := by
    refine hT.subset fun p ⟨hp, hne⟩ => ?_
    by_contra hpT
    obtain ⟨h1, h2⟩ := hzero p hp hpT
    exact hne (by simp only [h1, h2, add_zero, Int.toNat_zero, pow_zero])
  refine ⟨MvPolynomial.C κ * ∏ᶠ (p) (_ : p ∈ d.HtOne), d.gen p ^ (e1 p + d.nPMM h c (d.w (d.jc c) c) p).toNat, ?_, ?_⟩
  · have hmap : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (∏ᶠ (p) (_ : p ∈ d.HtOne), d.gen p ^ (e1 p + d.nPMM h c (d.w (d.jc c) c) p).toNat) =
        ∏ᶠ (p) (_ : p ∈ d.HtOne), algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p ^ (e1 p + d.nPMM h c (d.w (d.jc c) c) p).toNat) :=
      MonoidHom.map_finprod_mem' (algebraMap (KTp K d.D d.N) (KTf K d.D d.N)).toMonoidHom hms3
    rw [map_mul, hmap]
    unfold fZ
    rw [hN, mul_assoc, ← finprod_mem_mul_distrib' hms1 hms2,
      show algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (MvPolynomial.C κ) = algebraMap K (KTf K d.D d.N) κ from
        (IsScalarTower.algebraMap_apply K (KTp K d.D d.N) (KTf K d.D d.N) κ).symm]
    congr 1
    refine finprod_mem_congr rfl fun p hp => ?_
    rw [map_pow, ← zpow_natCast, Int.toNat_of_nonneg (hnn p hp), zpow_add₀ (hg0 p hp)]
  · refine mul_ne_zero (by simpa using hκ) ?_
    exact finprod_mem_induction (fun x => x ≠ 0) one_ne_zero (fun x y hx hy => mul_ne_zero hx hy)
      fun p hp => pow_ne_zero _ (d.generator_ne_zero_of_height p hp)

end Data

end ReciprocityTheory.ChartRestriction.G.T0
