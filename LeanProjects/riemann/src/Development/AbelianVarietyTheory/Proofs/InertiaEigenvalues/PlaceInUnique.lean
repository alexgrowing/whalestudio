import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoefMove
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical

namespace GlobalTheory.TowerPlace

theorem placeIn_unique : ∀ (Λ : Subring ℂ) [IsDiscreteValuationRing Λ] (l : ℕ), l.Prime → ¬ IsUnit ((l : ℕ) : Λ) → ∃ e : ℕ, ∀ (L : Type) [Field L] [NumberField L] (ι : L →+* ℂ), (∀ x, ι x ∈ Λ ∨ (ι x)⁻¹ ∈ Λ) → ∃ la : HeightOneSpectrum (𝓞 L), placesIn ι Λ = {la} ∧ (∀ x, ι x ∈ Λ ↔ la.valuation L x ≤ 1) ∧ ((l : ℕ) : 𝓞 L) ∈ la.asIdeal ∧ ((l : ℕ) : 𝓞 L) ∉ la.asIdeal ^ (e + 1) := by
  intro Λ _ l hl hlu
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Λ
  have hl0 : ((l : ℕ) : Λ) ≠ 0 := by
    intro h
    have h' : ((((l : ℕ) : Λ)) : ℂ) = 0 := by rw [h]; rfl
    push_cast at h'
    exact hl.ne_zero (by exact_mod_cast h')
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  refine ⟨e, fun L _ _ ι hval => ?_⟩
  let B : ValuationSubring L :=
    { toSubring := Λ.comap ι
      mem_or_inv_mem' := fun x => by
        rcases hval x with h | h
        · exact Or.inl h
        · right
          show ι x⁻¹ ∈ Λ
          rw [map_inv₀]; exact h }
  have hint : ∀ x : 𝓞 L, (ι.comp (algebraMap (𝓞 L) L)) x ∈ Λ := fun x => by
    have : IsIntegral B (algebraMap (𝓞 L) L x) := (x.isIntegral_coe).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
    show ι (algebraMap (𝓞 L) L x) ∈ Λ
    rw [← hy]; exact y.2
  let g : 𝓞 L →+* Λ := (ι.comp (algebraMap (𝓞 L) L)).codRestrict Λ hint
  have hg : ∀ x : 𝓞 L, ((g x : Λ) : ℂ) = ι (algebraMap (𝓞 L) L x) := fun x => rfl
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal Λ).comap g
  have hlP : ((l : ℕ) : 𝓞 L) ∈ P := by
    show g l ∈ IsLocalRing.maximalIdeal Λ
    rw [map_natCast, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact hlu
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hlP
    exact hl.ne_zero (by exact_mod_cast hlP)
  let la : HeightOneSpectrum (𝓞 L) := ⟨P, Ideal.comap_isPrime _ _, hPne⟩
  have hunit : ∀ s : 𝓞 L, s ∉ la.asIdeal → IsUnit (g s) := fun s hs => by
    by_contra h
    exact hs ((IsLocalRing.mem_maximalIdeal _).2 h)
  have hsup : ∀ x : L, la.valuation L x ≤ 1 → ι x ∈ Λ := by
    intro x hx
    obtain ⟨a, s, h⟩ := la.exists_primeCompl_mul_eq_of_integer (K := L) x hx
    obtain ⟨w, hw⟩ := hunit s s.2
    have h3 : (((w⁻¹ : Λˣ) : Λ) : ℂ) * ι (algebraMap (𝓞 L) L s) = 1 := by
      rw [← hg, ← hw]
      have := congrArg Subtype.val w.inv_mul
      exact this
    have hs0 : ι (algebraMap (𝓞 L) L s) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at h3; exact zero_ne_one h3
    have hw' : (ι (algebraMap (𝓞 L) L s))⁻¹ ∈ Λ := by
      rw [← eq_inv_of_mul_eq_one_left h3]; exact ((w⁻¹ : Λˣ) : Λ).2
    have hx' : ι x = ι (algebraMap (𝓞 L) L a) * (ι (algebraMap (𝓞 L) L s))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hs0, ← map_mul, h]
    rw [hx']
    exact Λ.mul_mem (hint a) hw'
  have hsub : ∀ x : L, ι x ∈ Λ → la.valuation L x ≤ 1 := by
    intro x hx
    by_contra hv
    push_neg at hv
    have hx0 : x ≠ 0 := by rintro rfl; simp at hv
    have hy : la.valuation L x⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hv
    obtain ⟨a, s, h⟩ := la.exists_primeCompl_mul_eq_of_integer (K := L) x⁻¹ hy.le
    have hs1 : la.valuation L (algebraMap (𝓞 L) L s) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := L) (v := la)).2 s.2
    have ha : a ∈ la.asIdeal := by
      refine (la.valuation_lt_one_iff_mem (K := L) a).1 ?_
      show la.valuation L (algebraMap (𝓞 L) L a) < 1
      rw [← h, map_mul, hs1, mul_one]; exact hy
    have h4 : (⟨ι x, hx⟩ : Λ) * g a = g s := Subtype.ext (show ι x * ι (algebraMap (𝓞 L) L a) = ι (algebraMap (𝓞 L) L s) by
      rw [← map_mul, ← h, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul])
    have hga : g a ∈ IsLocalRing.maximalIdeal Λ := ha
    have := hunit s s.2
    rw [← h4] at this
    exact ((IsLocalRing.mem_maximalIdeal _).1 (Ideal.mul_mem_left _ _ hga)) this
  refine ⟨la, ?_, fun x => ⟨hsub x, hsup x⟩, hlP, ?_⟩
  · ext la'
    constructor
    · intro h'
      rw [Set.mem_singleton_iff]
      have hle : la.asIdeal ≤ la'.asIdeal := by
        intro r hr
        by_contra hr'
        have h1 : la'.valuation L (algebraMap (𝓞 L) L r) = 1 :=
          (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := L) (v := la')).2 hr'
        have h2 : la'.valuation L (algebraMap (𝓞 L) L r)⁻¹ ≤ 1 := by rw [map_inv₀, h1, inv_one]
        have h3 := hsub _ (h' _ h2)
        have h5 : la.valuation L (algebraMap (𝓞 L) L r) < 1 := (la.valuation_lt_one_iff_mem (K := L) r).2 hr
        have hr0' : r ≠ 0 := by rintro rfl; exact hr' la'.asIdeal.zero_mem
        have hr0 : la.valuation L (algebraMap (𝓞 L) L r) ≠ 0 :=
          (Valuation.ne_zero_iff _).2 ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 L) L)).2 hr0')
        rw [map_inv₀] at h3
        have := one_lt_inv_iff₀.2 ⟨zero_lt_iff.2 hr0, h5⟩
        exact absurd h3 (not_le.2 this)
      have hEq : la.asIdeal = la'.asIdeal := la.isMaximal.eq_of_le la'.isPrime.ne_top hle
      exact HeightOneSpectrum.ext hEq.symm
    · intro h
      rw [Set.mem_singleton_iff] at h
      subst h
      exact hsup
  · intro hmem
    have hmap : Ideal.map g (la.asIdeal ^ (e + 1)) ≤ (IsLocalRing.maximalIdeal Λ) ^ (e + 1) := by
      rw [Ideal.map_pow]; exact Ideal.pow_right_mono Ideal.map_comap_le (e + 1)
    have h5 := hmap (Ideal.mem_map_of_mem g hmem)
    rw [map_natCast, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, hu] at h5
    obtain ⟨c, hc⟩ := h5
    have hpe : ϖ ^ e ≠ 0 := pow_ne_zero _ hϖ.ne_zero
    have hu' : (u : Λ) = ϖ * c := by
      apply mul_right_cancel₀ hpe
      rw [hc]; ring
    exact hϖ.not_isUnit (isUnit_of_mul_isUnit_left (hu' ▸ u.isUnit))

end GlobalTheory.TowerPlace
