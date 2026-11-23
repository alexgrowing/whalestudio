import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HHINDB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.UniformizerOfResidueIndep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HPlaces

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def aNla (h : d.S1) (O : ∀ c, AddValuation (Ω c) (WithTop ℤ) → A c → ℤ)
    (ta : ∀ c, A c) (la : HeightOneSpectrum (𝓞 K)) : ℝ :=
  ∑ c, ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.PlOver la c),
    (d.fze h c w : ℝ) * (O c (d.Wres c w) (ta c) : ℝ)

noncomputable def anP (h : d.S1) (O : ∀ c, AddValuation (Ω c) (WithTop ℤ) → A c → ℤ) (c : ι)
    (f : A c) (p : Ideal (KTp K d.D d.N)) : ℤ :=
  ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
    (d.fze h c w : ℤ) * O c (d.Wres c w) f

noncomputable def aI (Nr : ∀ c, A c → (Ω c →+* ℂ) → ℝ) (c : ι) (f : A c) (sg : K →+* ℂ)
    (z : BlockSphere d.D (d.N + 1)) : ℝ :=
  ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)), Real.log (Nr c f P)

noncomputable def AH (h : d.S1) (O : ∀ c, AddValuation (Ω c) (WithTop ℤ) → A c → ℤ)
    (Nr : ∀ c, A c → (Ω c →+* ℂ) → ℝ) (ta : ∀ c, A c) : ℝ :=
  (∑ᶠ la, d.aNla h O ta la * logNorm la) / (Module.finrank ℚ K : ℝ) +
    meanK (fun sg => ∑ c, ∫ z, (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
      -Real.log (Nr c (ta c) P)) ∂(blockSphereProb d.D (d.N + 1))) +
    ∑ c, ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), (d.anP h O c (ta c) p : ℝ) * h0 (d.gen p)

theorem Hgt_eq_AH (h : d.S1) (G : WT) (ta : ∀ c, A c) :
    d.Hgt h G ta = d.AH h (fun c v f => d.ord c v G f) (fun c f P => d.nrm c G f P) ta := rfl

theorem HgtMM_eq_AH (h : d.S1) (f : ∀ c, A c) :
    d.HgtMM h f = d.AH h (fun c v g => d.ordMM c v g) (fun c g P => d.nrm c d.wL g P / d.be c P) f :=
  rfl

theorem isOver_inj {c : ι} {v : AddValuation (Ω c) (WithTop ℤ)} {la la' : HeightOneSpectrum (𝓞 K)}
    (h1 : IsOver (K := K) v la) (h2 : IsOver (K := K) v la') : la = la' := by
  have hla : la.asIdeal = la'.asIdeal := by
    ext a
    rw [← h1 a, h2 a]
  exact HeightOneSpectrum.ext hla

theorem la_fin (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (O : AddValuation (Ω c) (WithTop ℤ) → ℤ)
    (hO : {v | d.admitted c v ∧ O v ≠ 0}.Finite) :
    {la : HeightOneSpectrum (𝓞 K) | ∃ w ∈ d.PlOver la c, O (d.Wres c w) ≠ 0}.Finite := by
  classical
  set s := {la : HeightOneSpectrum (𝓞 K) | ∃ w ∈ d.PlOver la c, O (d.Wres c w) ≠ 0}
  have hF : ∀ la (hla : la ∈ s), d.admitted c (d.Wres c hla.choose) ∧
      IsOver (K := K) (d.Wres c hla.choose) la ∧ O (d.Wres c hla.choose) ≠ 0 := by
    intro la hla
    have hs := (d.admissible_over_prime hd h la c _ hla.choose_spec.1)
    exact ⟨hs.1, hs.2.1, hla.choose_spec.2⟩
  have : Finite s := by
    have := hO.to_subtype
    refine Finite.of_injective (fun la : s => (⟨d.Wres c la.2.choose, (hF la la.2).1, (hF la la.2).2.2⟩ :
      {v | d.admitted c v ∧ O v ≠ 0})) ?_
    intro la la' heq
    have heq' : d.Wres c la.2.choose = d.Wres c la'.2.choose := congrArg Subtype.val heq
    exact Subtype.ext (isOver_inj (K := K) (hF la la.2).2.1 (heq' ▸ (hF la' la'.2).2.1))
  exact Set.toFinite s

end Data

end ReciprocityTheory.ChartRestriction.G.T0

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem admissible_of_good_valuation (hd : d.AxH 𝒜) (h : d.S1) (c : ι) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne)
    {w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)} (hw : w ∈ d.GoodP c p) : d.admitted c (d.Wres c w) := by
  rcases d.PlaceTrivialOrPositive hd h c p hp w hw.1 with h1 | h1
  · obtain ⟨b, hb, hb'⟩ := hw.2; exact absurd (h1 b hb) hb'
  · exact h1.1

theorem shift {c : ι} {v : AddValuation (Ω c) (WithTop ℤ)} (hv : d.admitted c v) {a : Ω c} (ha : a ≠ 0)
    {x y : ℤ} (hs : ((y : ℤ) : WithTop ℤ) = v a + (x : WithTop ℤ)) : y = WithTop.untopD 0 (v a) + x := by
  have hva : v a ≠ ⊤ := fun h0 => ha ((AddValuation.top_iff v).mp h0)
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hva
  rw [← hn] at hs ⊢
  rw [WithTop.untopD_coe]
  exact_mod_cast hs

theorem goodP_finite' (hd : d.AxH 𝒜) (h : d.S1) (c : ι) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) :
    (d.GoodP c p).Finite :=
  ((d.norm_by_places hd h c).1 p hp).subset fun _ hw => hw.1

theorem usage₆ (hd : d.AxH 𝒜) (h : d.S1) (O : ∀ c, AddValuation (Ω c) (WithTop ℤ) → A c → ℤ)
    (c : ι) (f : A c) (a : Ω c) (ha : a ≠ 0)
    (hOs : ∀ v, d.admitted c v → ((O c v (a • f) : ℤ) : WithTop ℤ) = v a + (O c v f : WithTop ℤ))
    {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) :
    d.anP h O c (a • f) p = d.anP h O c f p + d.nPa h c p a := by
  unfold anP nPa
  rw [← finsum_mem_add_distrib (d.goodP_finite' hd h c hp)]
  refine finsum_mem_congr rfl fun w hw => ?_
  have hv := d.admissible_of_good_valuation hd h c hp hw
  rw [d.shift hv ha (hOs _ hv)]
  ring

theorem aNla_smul (hd : d.AxH 𝒜) (h : d.S1) (O : ∀ c, AddValuation (Ω c) (WithTop ℤ) → A c → ℤ)
    (ta : ∀ c, A c) (a : ∀ c, Ω c) (ha : ∀ c, a c ≠ 0)
    (hOs : ∀ c v, d.admitted c v → ((O c v (a c • ta c) : ℤ) : WithTop ℤ) = v (a c) + (O c v (ta c) : WithTop ℤ))
    (la : HeightOneSpectrum (𝓞 K)) :
    d.aNla h O (fun c => a c • ta c) la =
      d.aNla h O ta la + ∑ c, (d.nLa h c la (algebraMap (Ω c) (OmS (Ω c) d.D d.N) (a c)) : ℝ) := by
  unfold aNla
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  have hfin := (d.places_over_la hd h la c).1
  unfold nLa
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin]
  push_cast
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  rw [Set.Finite.mem_toFinset] at hw
  have hv := (d.admissible_over_prime hd h la c w hw).1
  rw [d.shift hv (ha c) (hOs c _ hv)]
  push_cast
  rw [d.Wres_apply]
  ring

end Data

end ReciprocityTheory.ChartRestriction.G.T0

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem neg_aI (Nr : ∀ c, A c → (Ω c →+* ℂ) → ℝ) (c : ι) (f : A c) (sg : K →+* ℂ)
    (z : BlockSphere d.D (d.N + 1)) :
    ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)), -Real.log (Nr c f P) = -d.aI Nr c f sg z := by
  simp only [aI, ← finsum_neg_distrib]

theorem nsg_smul (hd : d.AxH 𝒜) (h : d.S1) (Nr : ∀ c, A c → (Ω c →+* ℂ) → ℝ) (c : ι) (f : A c)
    (a : Ω c) (ha : a ≠ 0) (hNs : ∀ P, Nr c (a • f) P = ‖P a‖ * Nr c f P) (hN0 : ∀ P, Nr c f P ≠ 0)
    (sg : K →+* ℂ) (hI : Integrable (d.aI Nr c f sg) (blockSphereProb d.D (d.N + 1)))
    (hI' : Integrable (d.aI Nr c (a • f) sg) (blockSphereProb d.D (d.N + 1))) :
    ∫ z, (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)), -Real.log (Nr c (a • f) P))
        ∂(blockSphereProb d.D (d.N + 1)) =
      ∫ z, (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)), -Real.log (Nr c f P))
        ∂(blockSphereProb d.D (d.N + 1)) - ∫ z, d.lsum c sg a z ∂(blockSphereProb d.D (d.N + 1)) := by
  have hae : d.aI Nr c (a • f) sg =ᵐ[blockSphereProb d.D (d.N + 1)]
      fun z => d.lsum c sg a z + d.aI Nr c f sg z := by
    filter_upwards [d.norm_at_sg hd h c sg] with z hz
    unfold aI lsum
    rw [finsum_mem_eq_finite_toFinset_sum _ hz.1, finsum_mem_eq_finite_toFinset_sum _ hz.1,
      finsum_mem_eq_finite_toFinset_sum _ hz.1, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro P _
    rw [hNs, Real.log_mul (norm_ne_zero_iff.2 ((map_ne_zero P).2 ha)) (hN0 P)]
  have hL : Integrable (d.lsum c sg a) (blockSphereProb d.D (d.N + 1)) := by
    refine (hI'.sub hI).congr ?_
    filter_upwards [hae] with z hz
    simp only [Pi.sub_apply, hz]; ring
  simp_rw [d.neg_aI]
  rw [integral_neg, integral_neg, integral_congr_ae hae, integral_add hL hI]
  ring

theorem aNla_supp (hd : d.AxH 𝒜) (h : d.S1) (O : ∀ c, AddValuation (Ω c) (WithTop ℤ) → A c → ℤ)
    (ta : ∀ c, A c) :
    Function.support (d.aNla h O ta) ⊆
      ⋃ c, {la : HeightOneSpectrum (𝓞 K) | ∃ w ∈ d.PlOver la c, O c (d.Wres c w) (ta c) ≠ 0} := by
  intro la hla
  by_contra hno
  apply hla
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_and, not_not] at hno
  unfold aNla
  refine Finset.sum_eq_zero fun c _ => ?_
  refine (finsum_mem_congr rfl fun w hw => ?_).trans (finsum_mem_zero _)
  simp [hno c w hw]

theorem nLa_supp (hd : d.AxH 𝒜) (h : d.S1) (O : ∀ c, AddValuation (Ω c) (WithTop ℤ) → A c → ℤ)
    (c : ι) (f : A c) (a : Ω c) (ha : a ≠ 0)
    (hOs : ∀ v, d.admitted c v → ((O c v (a • f) : ℤ) : WithTop ℤ) = v a + (O c v f : WithTop ℤ)) :
    Function.support (fun la => d.nLa h c la (algebraMap (Ω c) (OmS (Ω c) d.D d.N) a)) ⊆
      {la : HeightOneSpectrum (𝓞 K) | ∃ w ∈ d.PlOver la c, O c (d.Wres c w) f ≠ 0} ∪
      {la : HeightOneSpectrum (𝓞 K) | ∃ w ∈ d.PlOver la c, O c (d.Wres c w) (a • f) ≠ 0} := by
  intro la hla
  obtain ⟨w, hw, hw0⟩ := exists_ne_zero_of_finsum_mem_ne_zero hla
  have hv := (d.admissible_over_prime hd h la c w hw).1
  have hs := d.shift hv ha (hOs _ hv)
  by_cases h0 : O c (d.Wres c w) f = 0
  · right
    refine ⟨w, hw, ?_⟩
    rw [hs, h0, add_zero]
    intro h1; apply hw0; rw [← d.Wres_apply, h1, mul_zero]
  · exact Or.inl ⟨w, hw, h0⟩

theorem meanK_sub (F G : (K →+* ℂ) → ℝ) : meanK (fun sg => F sg - G sg) = meanK F - meanK G := by
  simp only [meanK, Finset.sum_sub_distrib, sub_div]

theorem meanK_sum (F : ι → (K →+* ℂ) → ℝ) : meanK (fun sg => ∑ c, F c sg) = ∑ c, meanK (F c) := by
  simp only [meanK]
  rw [Finset.sum_comm, Finset.sum_div]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
