import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GenericSectionOfAxioms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HFour
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.IntNsg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscB

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

theorem isOver_unique {Ωc : Type*} [Field Ωc] [Algebra K Ωc] (v : AddValuation Ωc (WithTop ℤ))
    (la la' : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (h1 : IsOver (K := K) v la)
    (h2 : IsOver (K := K) v la') : la = la' :=
  IsDedekindDomain.HeightOneSpectrum.ext (Ideal.ext fun a => (h1 a).symm.trans (h2 a))

theorem nl_nonneg_fin (hd : d.AxH 𝒜) (h : d.S1) :
    (∀ la, 0 ≤ d.Nl h la) ∧ (Function.support (d.Nl h)).Finite := by
  refine ⟨fun la => ?_, ?_⟩
  · unfold Data.Nl
    refine Finset.sum_nonneg fun c _ => finsum_nonneg fun w => finsum_nonneg fun hw => ?_
    have h1 := hd.ord_nonneg_et c _ (d.admissible_over_prime hd h la c w hw).1
    have h2 : (0 : ℝ) ≤ (d.ord c (d.Wres c w) (d.n1 • d.wde) (d.et c) : ℝ) := by exact_mod_cast h1
    exact mul_nonneg (Nat.cast_nonneg _) h2
  · have hS : ∀ c, {v | d.admitted c v ∧ d.ord c v (d.n1 • d.wde) (d.et c) ≠ 0}.Finite :=
      fun c => hd.a3' c (hd.et_mem c) (hd.et_ne c)
    refine Set.Finite.subset (Set.finite_iUnion fun c => (hS c).biUnion
      (fun v _ => (show ({la | IsOver (K := K) v la} : Set _).Subsingleton from
        fun a ha b hb => isOver_unique v a b ha hb).finite)) ?_
    intro la hla
    by_contra hno
    apply hla
    unfold Data.Nl
    refine Finset.sum_eq_zero fun c _ => finsum_eq_zero_of_forall_eq_zero fun w => ?_
    classical
    rw [finsum_eq_if]
    split_ifs with hw
    swap; · rfl
    have hs4 := d.admissible_over_prime hd h la c w hw
    by_cases h0 : d.ord c (d.Wres c w) (d.n1 • d.wde) (d.et c) = 0
    · simp [h0]
    · exact absurd (Set.mem_iUnion.2 ⟨c, Set.mem_biUnion (x := d.Wres c w)
      (show d.Wres c w ∈ {v | d.admitted c v ∧ d.ord c v (d.n1 • d.wde) (d.et c) ≠ 0} from ⟨hs4.1, h0⟩)
      (show la ∈ {la | IsOver (K := K) (d.Wres c w) la} from hs4.2.1)⟩) hno

theorem disc_two (hd : d.AxH 𝒜) (h : d.S1) (hI2et : d.HeightIntegralEstimateTrivialPlace) (hI2be : d.HeightIntegralBoundEstimate) :
    ((∑ᶠ la, d.Nl h la * logNorm la) / (Module.finrank ℚ K : ℝ)) / d.i ≤
      d.g0 * (d.Hgt h (d.n1 • d.wde) d.et / d.n1 + d.D * ((d.aG h (d.n1 • d.wde) d.et : ℝ) / d.n1) *
        (Real.log (d.N + 1 : ℕ) + 1 / 2)) + d.del * d.Pet := by
  have hta : ∀ c, d.et c ∈ 𝒜 c (d.n1 • d.wde) ∧ d.et c ≠ 0 := fun c => ⟨hd.et_mem c, hd.et_ne c⟩
  have hbdd : ∀ sg : K →+* ℂ, BddAbove (Set.range fun p : (Σ c, PT (Ω := Ω c) sg) =>
      d.nrm p.1 (d.n1 • d.wde) (d.et p.1) p.2) :=
    fun sg => hd.bdd sg _ d.et (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  have hint := fun c sg => (d.int_Nsg hd h hI2be c sg).1 (d.n1 • d.wde) (d.et c)
    (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) (hd.et_mem c) (hd.et_ne c)
  have h4 := (d.h_four hd h (d.n1 • d.wde) d.et hta (hd.ord_nonneg_et) hbdd hint).2
  have hNl : (fun la => d.Nl h la * logNorm la) =
      (fun la => d.NlaG h (d.n1 • d.wde) d.et la * logNorm la) := rfl
  rw [hNl]
  have hi : (0 : ℝ) < d.i := by exact_mod_cast hd.i_ge
  have hg : (0 : ℝ) < d.g0 := by exact_mod_cast hd.g_zero_ge_ask_sum
  have hn1 : ((d.n1 : ℕ) : ℝ) = (d.i : ℝ) * d.g0 := by simp [Data.n1]
  have hdel : (0 : ℝ) ≤ d.del := Nat.cast_nonneg _
  have hE : meanK (fun sg => Real.log (d.supN sg (d.n1 • d.wde) d.et)) / d.i ≤ d.Pet := hI2et
  calc _ ≤ (d.Hgt h (d.n1 • d.wde) d.et + d.del * meanK (fun sg => Real.log (d.supN sg (d.n1 • d.wde) d.et)) +
          d.D * d.aG h (d.n1 • d.wde) d.et * (Real.log (d.N + 1 : ℕ) + 1 / 2)) / d.i :=
        div_le_div_of_nonneg_right h4 hi.le
    _ = d.g0 * (d.Hgt h (d.n1 • d.wde) d.et / d.n1 + d.D * ((d.aG h (d.n1 • d.wde) d.et : ℝ) / d.n1) *
          (Real.log (d.N + 1 : ℕ) + 1 / 2)) +
          d.del * (meanK (fun sg => Real.log (d.supN sg (d.n1 • d.wde) d.et)) / d.i) := by
        rw [hn1]; field_simp; ring
    _ ≤ _ := by gcongr

theorem disc_one (hd : d.AxH 𝒜) (h : d.S1) (hI2et : d.HeightIntegralEstimateTrivialPlace) (hI2be : d.HeightIntegralBoundEstimate) (ta' : ∀ c, A c)
    (hta' : ∀ c, ta' c ∈ 𝒜 c d.wF ∧ ta' c ≠ 0) :
    (∀ la c, (d.PlOver la c).Finite) ∧ (∀ la, (d.htOf hd h).Ila la ≠ ⊤) ∧
    (Function.support (d.IL h hd.sel hd.a4.choose)).Finite ∧
    2 * ((∑ᶠ la, d.IL h hd.sel hd.a4.choose la * logNorm la) / (Module.finrank ℚ K : ℝ)) ≤
      d.del * Real.log d.del +
        2 * ∑ k, meanK (fun sg => Real.log (d.supN sg d.wF (d.thp (hd.sel k)))) +
        2 * d.D * d.aG h d.wF ta' * (Real.log (d.N + 1 : ℕ) + 1 / 2) + 2 * d.Hgt h d.wF ta' := by
  obtain ⟨_hDe0, hloc⟩ := d.disc_lattice hd h
  obtain ⟨hgf, hNef, hglob⟩ := d.disc_global hd h hI2be ta' hta'
  have hl : ∀ la : IsDedekindDomain.HeightOneSpectrum (𝓞 K), 0 ≤ logNorm la := by
    intro la
    apply Real.log_nonneg
    have : Ideal.absNorm la.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact la.ne_bot
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hIL0 : ∀ la, 0 ≤ d.IL h hd.sel hd.a4.choose la := fun _ => Nat.cast_nonneg _
  have hsupp : (Function.support (d.IL h hd.sel hd.a4.choose)).Finite := by
    apply (hgf.union hNef).subset
    intro la hla
    simp only [Function.mem_support, Set.mem_union] at hla ⊢
    by_contra hc
    push_neg at hc
    have h2 := (hloc la).2
    rw [hc.1, hc.2] at h2
    push_cast at h2
    exact hla (le_antisymm (by linarith) (hIL0 la))
  refine ⟨fun la c => (d.places_over_la hd h la c).1, fun la => (hloc la).1, hsupp, ?_⟩
  have hf1 : (Function.support fun la => 2 * (d.IL h hd.sel hd.a4.choose la * logNorm la)).Finite :=
    hsupp.subset fun la hla => by
      simp only [Function.mem_support] at hla ⊢
      intro h0; apply hla; rw [h0]; ring
  have hf2 : (Function.support fun la =>
      ((d.gOrd la (d.De hd h) : ℝ) + 2 * d.NlaG h d.wF hd.a4.choose la) * logNorm la).Finite :=
    (hgf.union hNef).subset fun la hla => by
      simp only [Function.mem_support, Set.mem_union] at hla ⊢
      by_contra hc; push_neg at hc; apply hla; rw [hc.1, hc.2]; simp
  have hf0 : (Function.support fun la => d.IL h hd.sel hd.a4.choose la * logNorm la).Finite :=
    hsupp.subset fun la hla => by
      simp only [Function.mem_support] at hla ⊢
      intro h0; apply hla; rw [h0, zero_mul]
  have hle : (∑ᶠ la, 2 * (d.IL h hd.sel hd.a4.choose la * logNorm la)) ≤
      ∑ᶠ la, ((d.gOrd la (d.De hd h) : ℝ) + 2 * d.NlaG h d.wF hd.a4.choose la) * logNorm la :=
    finsum_le_finsum' hf1 hf2 fun la => by
      have := (hloc la).2
      have := hl la
      nlinarith
  have hnK : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  rw [← mul_finsum' _ _ hf0] at hle
  calc 2 * ((∑ᶠ la, d.IL h hd.sel hd.a4.choose la * logNorm la) / (Module.finrank ℚ K : ℝ))
      = (2 * ∑ᶠ la, d.IL h hd.sel hd.a4.choose la * logNorm la) / (Module.finrank ℚ K : ℝ) := by ring
    _ ≤ (∑ᶠ la, ((d.gOrd la (d.De hd h) : ℝ) + 2 * d.NlaG h d.wF hd.a4.choose la) * logNorm la) /
          (Module.finrank ℚ K : ℝ) := div_le_div_of_nonneg_right hle hnK.le
    _ ≤ _ := hglob

theorem disc (hd : d.AxH 𝒜) (h : d.S1) (hI2et : d.HeightIntegralEstimateTrivialPlace) (hI2be : d.HeightIntegralBoundEstimate) (ta' : ∀ c, A c)
    (hta' : ∀ c, ta' c ∈ 𝒜 c d.wF ∧ ta' c ≠ 0) :
    let lr := Real.log (d.N + 1 : ℕ) + 1 / 2
    (∀ la c, (d.PlOver la c).Finite) ∧ (∀ la, (d.htOf hd h).Ila la ≠ ⊤) ∧
    (Function.support (d.IL h hd.sel hd.a4.choose)).Finite ∧
    2 * ((∑ᶠ la, d.IL h hd.sel hd.a4.choose la * logNorm la) / (Module.finrank ℚ K : ℝ)) ≤
      d.del * Real.log d.del +
        2 * ∑ k, meanK (fun sg => Real.log (d.supN sg d.wF (d.thp (hd.sel k)))) +
        2 * d.D * d.aG h d.wF ta' * lr + 2 * d.Hgt h d.wF ta' ∧
    (∀ la, 0 ≤ d.Nl h la) ∧ (Function.support (d.Nl h)).Finite ∧
    ((∑ᶠ la, d.Nl h la * logNorm la) / (Module.finrank ℚ K : ℝ)) / d.i ≤
      d.g0 * (d.Hgt h (d.n1 • d.wde) d.et / d.n1 + d.D * ((d.aG h (d.n1 • d.wde) d.et : ℝ) / d.n1) * lr) +
        d.del * d.Pet := by
  intro lr
  obtain ⟨h1, h2, h3, h4⟩ := d.disc_one hd h hI2et hI2be ta' hta'
  obtain ⟨h5, h6⟩ := d.nl_nonneg_fin hd h
  exact ⟨h1, h2, h3, h4, h5, h6, d.disc_two hd h hI2et hI2be⟩

end Data

end ReciprocityTheory.ChartRestriction.G.T0
