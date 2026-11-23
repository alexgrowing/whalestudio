import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HHINDC

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

theorem AH_smul (hd : d.AxH 𝒜) (h : d.S1) (O : ∀ c, AddValuation (Ω c) (WithTop ℤ) → A c → ℤ)
    (Nr : ∀ c, A c → (Ω c →+* ℂ) → ℝ) (ta : ∀ c, A c) (a : ∀ c, Ω c) (ha : ∀ c, a c ≠ 0)
    (hOs : ∀ c v, d.admitted c v →
      ((O c v (a c • ta c) : ℤ) : WithTop ℤ) = v (a c) + (O c v (ta c) : WithTop ℤ))
    (hOf : ∀ c, {v | d.admitted c v ∧ O c v (ta c) ≠ 0}.Finite)
    (hOf' : ∀ c, {v | d.admitted c v ∧ O c v (a c • ta c) ≠ 0}.Finite)
    (hPf : ∀ c, {p | p ∈ d.HtOne ∧ d.anP h O c (ta c) p ≠ 0}.Finite)
    (hNs : ∀ c P, Nr c (a c • ta c) P = ‖P (a c)‖ * Nr c (ta c) P)
    (hN0 : ∀ c P, Nr c (ta c) P ≠ 0)
    (hI : ∀ c sg, Integrable (d.aI Nr c (ta c) sg) (blockSphereProb d.D (d.N + 1)))
    (hI' : ∀ c sg, Integrable (d.aI Nr c (a c • ta c) sg) (blockSphereProb d.D (d.N + 1))) :
    d.AH h O Nr (fun c => a c • ta c) = d.AH h O Nr ta := by
  set U := ⋃ c, ({la : HeightOneSpectrum (𝓞 K) | ∃ w ∈ d.PlOver la c, O c (d.Wres c w) (ta c) ≠ 0} ∪
    {la : HeightOneSpectrum (𝓞 K) | ∃ w ∈ d.PlOver la c, O c (d.Wres c w) (a c • ta c) ≠ 0}) with hUdef
  have hU : U.Finite := Set.finite_iUnion fun c =>
    (d.la_fin hd h c (fun v => O c v (ta c)) (hOf c)).union (d.la_fin hd h c (fun v => O c v (a c • ta c)) (hOf' c))
  have e1 : ∑ᶠ la, d.aNla h O ta la * logNorm la = ∑ la ∈ hU.toFinset, d.aNla h O ta la * logNorm la := by
    apply finsum_eq_sum_of_support_subset
    intro la hla
    rw [Set.Finite.coe_toFinset]
    obtain ⟨c, hc⟩ := Set.mem_iUnion.1 (d.aNla_supp hd h O ta (Function.support_mul_subset_left _ _ hla))
    exact Set.mem_iUnion.2 ⟨c, Or.inl hc⟩
  have e2 : ∑ᶠ la, d.aNla h O (fun c => a c • ta c) la * logNorm la =
      ∑ la ∈ hU.toFinset, d.aNla h O (fun c => a c • ta c) la * logNorm la := by
    apply finsum_eq_sum_of_support_subset
    intro la hla
    rw [Set.Finite.coe_toFinset]
    obtain ⟨c, hc⟩ := Set.mem_iUnion.1
      (d.aNla_supp hd h O (fun c => a c • ta c) (Function.support_mul_subset_left _ _ hla))
    exact Set.mem_iUnion.2 ⟨c, Or.inr hc⟩
  have e3 : ∀ c, ∑ᶠ la, (d.nLa h c la (algebraMap (Ω c) (OmS (Ω c) d.D d.N) (a c)) : ℝ) * logNorm la =
      ∑ la ∈ hU.toFinset, (d.nLa h c la (algebraMap (Ω c) (OmS (Ω c) d.D d.N) (a c)) : ℝ) * logNorm la := by
    intro c
    apply finsum_eq_sum_of_support_subset
    intro la hla
    rw [Set.Finite.coe_toFinset]
    have hla' : la ∈ Function.support
        (fun la => d.nLa h c la (algebraMap (Ω c) (OmS (Ω c) d.D d.N) (a c))) := by
      intro h0; apply hla; simp only at h0 ⊢; rw [h0]; simp
    exact Set.mem_iUnion.2 ⟨c, d.nLa_supp hd h O c (ta c) (a c) (ha c) (hOs c) hla'⟩
  have hla : ∑ᶠ la, d.aNla h O (fun c => a c • ta c) la * logNorm la =
      ∑ᶠ la, d.aNla h O ta la * logNorm la +
        ∑ c, ∑ᶠ la, (d.nLa h c la (algebraMap (Ω c) (OmS (Ω c) d.D d.N) (a c)) : ℝ) * logNorm la := by
    rw [e1, e2, Finset.sum_congr rfl fun c _ => e3 c, Finset.sum_comm, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro la _
    rw [d.aNla_smul hd h O ta a ha hOs la, add_mul, Finset.sum_mul]
  have hP : ∀ c, ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
      (d.anP h O c (a c • ta c) p : ℝ) * h0 (d.gen p) =
      ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), (d.anP h O c (ta c) p : ℝ) * h0 (d.gen p) +
      ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), (d.nPa h c p (a c) : ℝ) * h0 (d.gen p) := by
    intro c
    rw [finsum_mem_congr rfl (fun p hp => by
      rw [d.usage₆ hd h O c (ta c) (a c) (ha c) (hOs c) hp, Int.cast_add, add_mul])]
    apply finsum_mem_add_distrib'
    · refine (hPf c).subset ?_
      rintro p ⟨hp, hp0⟩
      exact ⟨hp, fun h0' => hp0 (by simp only; rw [h0']; simp)⟩
    · refine (d.nPa_support hd h c (a c) (ha c)).subset ?_
      rintro p ⟨hp, hp0⟩
      exact ⟨hp, fun h0' => hp0 (by simp only; rw [h0']; simp)⟩
  have hS : (fun sg => ∑ c, ∫ z, (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
      -Real.log (Nr c (a c • ta c) P)) ∂(blockSphereProb d.D (d.N + 1))) =
      fun sg => (∑ c, ∫ z, (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
        -Real.log (Nr c (ta c) P)) ∂(blockSphereProb d.D (d.N + 1))) -
        ∑ c, ∫ z, d.lsum c sg (a c) z ∂(blockSphereProb d.D (d.N + 1)) := by
    funext sg
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ =>
      d.nsg_smul hd h Nr c (ta c) (a c) (ha c) (hNs c) (hN0 c) sg (hI c sg) (hI' c sg)
  have hpf := fun c => d.pf hd h c (a c) (ha c)
  unfold AH
  rw [hla, hS, meanK_sub, Finset.sum_congr rfl fun c _ => hP c, Finset.sum_add_distrib]
  simp only [meanK_sum]
  rw [← Finset.sum_congr rfl fun c _ => hpf c, Finset.sum_add_distrib, add_div, Finset.sum_div]
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

def IntOK (G : WT) (ta : ∀ c, A c) : Prop :=
  ∀ c sg, Integrable (d.aI (fun c f P => d.nrm c G f P) c (ta c) sg) (blockSphereProb d.D (d.N + 1))

theorem meanK_add (F G : (K →+* ℂ) → ℝ) : meanK (fun sg => F sg + G sg) = meanK F + meanK G := by
  first
    | (simp only [meanK, Finset.sum_add_distrib, add_div])
    | (unfold meanK; rw [Finset.sum_add_distrib, add_div])
    | (simp [meanK, Finset.sum_add_distrib, add_div])

theorem aI_mul_ae (hd : d.AxH 𝒜) (h : d.S1) {G G' : WT} (c : ι) {f g : A c}
    (hf : f ∈ 𝒜 c G) (hg : g ∈ 𝒜 c G') (hf0 : f ≠ 0) (hg0 : g ≠ 0) (sg : K →+* ℂ) :
    d.aI (fun c f P => d.nrm c (G + G') f P) c (f * g) sg =ᵐ[blockSphereProb d.D (d.N + 1)]
      fun z => d.aI (fun c f P => d.nrm c G f P) c f sg z + d.aI (fun c f P => d.nrm c G' f P) c g sg z := by
  filter_upwards [d.norm_at_sg hd h c sg] with z hz
  unfold aI
  rw [finsum_mem_eq_finite_toFinset_sum _ hz.1, finsum_mem_eq_finite_toFinset_sum _ hz.1,
    finsum_mem_eq_finite_toFinset_sum _ hz.1, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro P _
  dsimp only
  rw [hd.nrm_mul c P hf hg hf0 hg0, Real.log_mul (hd.nrm_pos c P hf hf0).ne' (hd.nrm_pos c P hg hg0).ne']

theorem Hgt_mul (hd : d.AxH 𝒜) (h : d.S1) (G G' : WT) (f g : ∀ c, A c)
    (hf : ∀ c, f c ∈ 𝒜 c G ∧ f c ≠ 0) (hg : ∀ c, g c ∈ 𝒜 c G' ∧ g c ≠ 0)
    (hIf : d.IntOK G f) (hIg : d.IntOK G' g) :
    d.IntOK (G + G') (f * g) ∧ d.Hgt h (G + G') (f * g) = d.Hgt h G f + d.Hgt h G' g := by
  have hae := fun c sg => d.aI_mul_ae hd h c (hf c).1 (hg c).1 (hf c).2 (hg c).2 sg
  have hI : d.IntOK (G + G') (f * g) := fun c sg => ((hIf c sg).add (hIg c sg)).congr (hae c sg).symm
  refine ⟨hI, ?_⟩

  have hOf := fun c => hd.a3' c (hf c).1 (hf c).2
  have hOg := fun c => hd.a3' c (hg c).1 (hg c).2
  have hla : ∀ la, d.aNla h (fun c v x => d.ord c v (G + G') x) (f * g) la =
      d.aNla h (fun c v x => d.ord c v G x) f la + d.aNla h (fun c v x => d.ord c v G' x) g la := by
    intro la
    unfold aNla
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    have hfin := (d.places_over_la hd h la c).1
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
      finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w hw
    rw [Set.Finite.mem_toFinset] at hw
    have hv := (d.admissible_over_prime hd h la c w hw).1
    rw [Pi.mul_apply]
    dsimp only
    rw [hd.ord_mul c _ hv (hf c).1 (hg c).1 (hf c).2 (hg c).2]
    push_cast; ring
  have hsf : (Function.support fun la => d.aNla h (fun c v x => d.ord c v G x) f la * logNorm la).Finite :=
    (Set.finite_iUnion fun c => d.la_fin hd h c (fun v => d.ord c v G (f c)) (hOf c)).subset
    ((Function.support_mul_subset_left _ _).trans (d.aNla_supp hd h (fun c v x => d.ord c v G x) f))
  have hsg : (Function.support fun la => d.aNla h (fun c v x => d.ord c v G' x) g la * logNorm la).Finite :=
    (Set.finite_iUnion fun c => d.la_fin hd h c (fun v => d.ord c v G' (g c)) (hOg c)).subset
    ((Function.support_mul_subset_left (fun la => d.aNla h (fun c v x => d.ord c v G' x) g la)
      logNorm).trans (d.aNla_supp hd h (fun c v x => d.ord c v G' x) g))
  have hN : ∑ᶠ la, d.aNla h (fun c v x => d.ord c v (G + G') x) (f * g) la * logNorm la =
      ∑ᶠ la, d.aNla h (fun c v x => d.ord c v G x) f la * logNorm la +
      ∑ᶠ la, d.aNla h (fun c v x => d.ord c v G' x) g la * logNorm la := by
    rw [← finsum_add_distrib hsf hsg]
    exact finsum_congr fun la => by rw [hla, add_mul]

  have hS : ∀ sg c, ∫ z, (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
      -Real.log (d.nrm c (G + G') ((f * g) c) P)) ∂(blockSphereProb d.D (d.N + 1)) =
      ∫ z, (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
        -Real.log (d.nrm c G (f c) P)) ∂(blockSphereProb d.D (d.N + 1)) +
      ∫ z, (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
        -Real.log (d.nrm c G' (g c) P)) ∂(blockSphereProb d.D (d.N + 1)) := by
    intro sg c
    have e1 := d.neg_aI (fun c f P => d.nrm c (G + G') f P) c ((f * g) c) sg
    have e2 := d.neg_aI (fun c f P => d.nrm c G f P) c (f c) sg
    have e3 := d.neg_aI (fun c f P => d.nrm c G' f P) c (g c) sg
    simp_rw [e1, e2, e3]
    rw [integral_neg, integral_neg, integral_neg, Pi.mul_apply, integral_congr_ae (hae c sg),
      integral_add (hIf c sg) (hIg c sg)]
    ring

  have hP : ∀ c, ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
      (d.anP h (fun c v x => d.ord c v (G + G') x) c ((f * g) c) p : ℝ) * h0 (d.gen p) =
      ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        (d.anP h (fun c v x => d.ord c v G x) c (f c) p : ℝ) * h0 (d.gen p) +
      ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        (d.anP h (fun c v x => d.ord c v G' x) c (g c) p : ℝ) * h0 (d.gen p) := by
    intro c
    rw [finsum_mem_congr rfl (fun p hp => by
      rw [show d.anP h (fun c v x => d.ord c v (G + G') x) c ((f * g) c) p =
          d.anP h (fun c v x => d.ord c v G x) c (f c) p + d.anP h (fun c v x => d.ord c v G' x) c (g c) p from by
        have hfin := d.goodP_finite' hd h c hp
        unfold anP
        rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
          finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro w hw
        rw [Set.Finite.mem_toFinset] at hw
        rw [Pi.mul_apply]
        dsimp only
        rw [hd.ord_mul c _ (d.admissible_of_good_valuation hd h c hp hw) (hf c).1 (hg c).1 (hf c).2 (hg c).2]
        ring, Int.cast_add, add_mul])]
    apply finsum_mem_add_distrib'
    · refine ((d.good_primes_properties hd h c).2.2.1 G (f c) (hf c).1 (hf c).2).subset ?_
      rintro p ⟨hp, hp0⟩
      exact ⟨hp, fun h0' => hp0 (by simp only; rw [show d.anP h _ c (f c) p = d.nP h c G (f c) p from rfl, h0']; simp)⟩
    · refine ((d.good_primes_properties hd h c).2.2.1 G' (g c) (hg c).1 (hg c).2).subset ?_
      rintro p ⟨hp, hp0⟩
      exact ⟨hp, fun h0' => hp0 (by simp only; rw [show d.anP h _ c (g c) p = d.nP h c G' (g c) p from rfl, h0']; simp)⟩
  rw [d.Hgt_eq_AH, d.Hgt_eq_AH, d.Hgt_eq_AH]
  unfold AH
  rw [hN]
  simp only [hS, Finset.sum_add_distrib, meanK_add, hP]
  ring

end Data

end ReciprocityTheory.ChartRestriction.G.T0
