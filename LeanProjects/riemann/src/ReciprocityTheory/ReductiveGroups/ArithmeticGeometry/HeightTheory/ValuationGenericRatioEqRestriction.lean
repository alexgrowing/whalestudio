import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.UniformizerOfResidueIndep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormFactorizationClause
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ComponentFormProperties
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.IntNsg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormByPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HNormPts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HPlaces
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.OrdEqValuationRatioBaseAdd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GoodPrimesProperties
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.SpecialFibreFactorization

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

theorem gen_ne_zero_of_htOne {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) : d.gen p ≠ 0 := by
  intro h0
  exact d.x4v4_gen_ne hp (by rw [h0, map_zero])

theorem valuation_genericRatio_eq_restriction (hd : d.AxH 𝒜) (c : ι) (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ))
    (j0 : Fin (d.N + 1)) (hj0 : d.w j0 c ≠ 0)
    (hunit : w (∑ j, d.sH c (MvPolynomial.X (0, j)) *
      algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) = 0) :
    w (d.rationalBaseRow c) = d.Wres c w (ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c)) := by
  have hg : d.w (d.jc c) c ≠ 0 := hd.w_base c
  have e0 : d.w j0 c = ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) • d.w (d.jc c) c :=
    d.x4v4_eq_smul hd c (hd.w_mem j0 c)
  have hr00 : ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) ≠ 0 := by
    intro h0
    apply hj0
    rw [e0, h0, zero_smul]
  have key : ∀ j, ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) =
      ratio (Ω := Ω c) (d.w j c) (d.w j0 c) * ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) := by
    intro j
    have ej : d.w j c = ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) • d.w (d.jc c) c :=
      d.x4v4_eq_smul hd c (hd.w_mem j c)
    have hrj : ratio (Ω := Ω c) (d.w j c) (d.w j0 c) =
        ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) / ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) := by
      apply x4v4_ratio_spec hj0
      calc d.w j c = ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) • d.w (d.jc c) c := ej
        _ = (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) / ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) *
              ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c)) • d.w (d.jc c) c := by
            rw [div_mul_cancel₀ _ hr00]
        _ = (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) / ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c)) •
              (ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c) • d.w (d.jc c) c) := by
            rw [smul_smul]
        _ = _ := by rw [← e0]
    rw [hrj, div_mul_cancel₀ _ hr00]
  have hsum : d.rationalBaseRow c = (∑ j, d.sH c (MvPolynomial.X (0, j)) *
      algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) *
      algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j0 c) (d.w (d.jc c) c)) := by
    unfold Data.rationalBaseRow
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [key j, map_mul, mul_assoc]
  rw [hsum, AddValuation.map_mul, hunit, zero_add]
  first
    | rfl
    | simp [Data.Wres, AddValuation.comap_apply]

theorem ordMinMax_at_good_place (hd : d.AxH 𝒜) (c : ι) (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ))
    (hv : d.admitted c (d.Wres c w)) (j0 : Fin (d.N + 1)) (hj0 : d.w j0 c ≠ 0)
    (hint : ∀ j, 0 ≤ d.Wres c w (ratio (Ω := Ω c) (d.w j c) (d.w j0 c)))
    (hunit : w (∑ j, d.sH c (MvPolynomial.X (0, j)) *
      algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) = 0)
    {f : A c} (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    d.ordMM c (d.Wres c w) f =
      (w (algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) f (d.w (d.jc c) c)))).untopD 0 -
        (w (d.rationalBaseRow c)).untopD 0 := by
  rw [d.ordMinMax_eq_ratio_untop_sub hd c _ hv j0 hj0 hint hf hf0, d.valuation_genericRatio_eq_restriction hd c w j0 hj0 hunit]
  rfl

theorem exists_ne_zero_of_finsum_mem_ne_zero' {α M : Type*} [AddCommMonoid M] {s : Set α} {f : α → M}
    (h : ∑ᶠ i ∈ s, f i ≠ 0) : ∃ i ∈ s, f i ≠ 0 := by
  by_contra hne
  push_neg at hne
  exact h (by rw [finsum_mem_congr rfl hne, finsum_mem_zero])

theorem ratio_self_eq_one (hd : d.AxH 𝒜) (c : ι) :
    ratio (Ω := Ω c) (d.w (d.jc c) c) (d.w (d.jc c) c) = 1 := by
  have hw := hd.w_base c
  have hex : ∃ a : Ω c, d.w (d.jc c) c = a • d.w (d.jc c) c := ⟨1, (one_smul _ _).symm⟩
  unfold ratio
  rw [dif_pos hex]
  have hs := hex.choose_spec
  have h0 : (hex.choose - 1) • d.w (d.jc c) c = 0 := by
    rw [sub_smul, one_smul, ← hs, sub_self]
  rcases smul_eq_zero.1 h0 with h | h
  · exact sub_eq_zero.1 h
  · exact absurd h hw

theorem good_place_admissible_unit (hd : d.AxH 𝒜) (h : d.S1) (c : ι) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne)
    {w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)} (hw : w ∈ d.GoodP c p) :
    d.admitted c (d.Wres c w) ∧ ∃ j0, d.w j0 c ≠ 0 ∧
      (∀ j, 0 ≤ d.Wres c w (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) ∧
        w (∑ j, d.sH c (MvPolynomial.X (0, j)) *
          algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) = 0 := by
  obtain ⟨hov, a, ha0, hwa⟩ := hw
  rcases d.PlaceTrivialOrPositive hd h c p hp w hov with htriv | ⟨hadm, -, hrest⟩
  · exact absurd (htriv a ha0) hwa
  · exact ⟨hadm, hrest⟩

theorem multiplicity_split_finsum (hd : d.AxH 𝒜) (h : d.S1) (c : ι) {p : Ideal (KTp K d.D d.N)}
    (hp : p ∈ d.HtOne) {f : A c} (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    d.nPMM h c f p =
      (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
        (d.fze h c w : ℤ) * WithTop.untopD 0 (d.Wres c w (ratio (Ω := Ω c) f (d.w (d.jc c) c)))) +
      d.nPMM h c (d.w (d.jc c) c) p := by
  exact d.x4v4_split hd h c hp hf hf0

theorem algebraMap_gen_ne_zero {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) :
    algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ≠ 0 := fun h => d.gen_ne_zero_of_htOne hp
  ((IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)) (h.trans (map_zero _).symm))

theorem substituted_factorization_exists (hd : d.AxH 𝒜) (h : d.S1) (x : Fin (d.N + 1) → K)
    (hx : ∀ c, d.wx x c ≠ 0) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) :
    ∃ κ : K, κ ≠ 0 ∧ d.heightSubstitutionCondition h x c F κ := by
  set a := ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c) with ha_def
  have hmem := d.linearCombination_mem_section hd x c
  have ha : a ≠ 0 := d.ratio_base_ne_zero hd c hmem (hx c)
  obtain ⟨κ1, hκ1, e1⟩ := d.SpecialFibreFactorization hd h c F hF x (hx c)
  obtain ⟨κ3, hκ3, e3⟩ := (d.norm_factorization hd h).1 c a ha
  set na : Ideal (KTp K d.D d.N) → ℤ := fun p =>
    ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
      (d.fze h c w : ℤ) * WithTop.untopD 0 (d.Wres c w a) with hna
  have hsplit : ∀ p ∈ d.HtOne, d.nPMM h c (d.wx x c) p = na p + d.nPMM h c (d.w (d.jc c) c) p :=
    fun p hp => d.multiplicity_split_finsum hd h c hp hmem (hx c)
  have hyne : algebraMap (Ω c) (OmS (Ω c) d.D d.N) a ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap (Ω c) (OmS (Ω c) d.D d.N)).injective).mpr ha
  have hSa := ((d.norm_by_places hd h c).2 _ hyne).1
  have hSj := (d.good_primes_properties hd h c).2.2.2 _ (hd.w_mem _ c) (hd.w_base c)
  set g : Ideal (KTp K d.D d.N) → KTf K d.D d.N := fun p =>
    algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) with hg
  have hfa : (d.HtOne ∩ Function.mulSupport fun p => g p ^ na p).Finite := by
    refine hSa.subset fun p hp => ⟨hp.1, ?_⟩
    have hn : na p ≠ 0 := by
      intro h0; apply hp.2; simp only [h0, zpow_zero]
    obtain ⟨w, hw, hne⟩ := exists_ne_zero_of_finsum_mem_ne_zero' hn
    refine ⟨w, hw.1, fun h0 => hne ?_⟩
    show (d.fze h c w : ℤ) * WithTop.untopD 0 (w _) = 0
    rw [h0]; simp
  have hfj : (d.HtOne ∩ Function.mulSupport fun p => g p ^ d.nPMM h c (d.w (d.jc c) c) p).Finite := by
    refine hSj.subset fun p hp => ⟨hp.1, ?_⟩
    intro h0; apply hp.2; simp only [h0, zpow_zero]
  have hprod : (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), g p ^ d.nPMM h c (d.wx x c) p) =
      (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), g p ^ na p) *
        ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), g p ^ d.nPMM h c (d.w (d.jc c) c) p := by
    rw [← finprod_mem_mul_distrib' hfa hfj]
    refine finprod_mem_congr rfl fun p hp => ?_
    rw [hsplit p hp, zpow_add₀ (d.algebraMap_gen_ne_zero hp)]
  refine ⟨κ1 / κ3, div_ne_zero hκ1 hκ3, ?_⟩
  unfold heightSubstitutionCondition translatedForm
  rw [hF, e1, e3, hprod]
  unfold fZ
  have h3 : algebraMap K (KTf K d.D d.N) κ3 ≠ 0 := (map_ne_zero _).mpr hκ3
  rw [map_div₀]
  simp only [hg, hna]
  field_simp

end Data

end ReciprocityTheory.ChartRestriction.G.T0
