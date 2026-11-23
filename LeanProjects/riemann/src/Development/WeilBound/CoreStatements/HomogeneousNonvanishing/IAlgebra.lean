import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

theorem ialg_one {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] :
    IsMultiHomog (1 : MRing ι) 0 := by
  classical
  intro m hm k
  have : m = 0 := by
    by_contra h
    rw [mem_support_iff, coeff_one, if_neg (Ne.symm h)] at hm
    exact hm rfl
  simp [this]

theorem ialg_mul {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {f g : MRing ι} {a b : K → ℕ}
    (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.1 (support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m₁ h₁ k, hg m₂ h₂ k]

theorem ialg_rename {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {κ : K → K'}
    {v : (Σ k, ι k) → Σ k, ι' k} (hv : IsBlockMap κ v) {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) :
    IsMultiHomog (rename v f : MRing ι') (Function.extend κ a 0) := by
  classical
  intro m' hm' k'
  rw [support_rename_of_injective hv.2.1] at hm'
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hm'
  by_cases hk : ∃ k, κ k = k'
  · obtain ⟨k, rfl⟩ := hk
    rw [hv.1.extend_apply, ← hf m hm k]
    have hc : ∀ i : ι k, ∃ j : ι' (κ k), v ⟨k, i⟩ = ⟨κ k, j⟩ := by
      intro i
      have h1 := hv.2.2.1 ⟨k, i⟩
      generalize v ⟨k, i⟩ = q at h1
      obtain ⟨k₁, j⟩ := q
      obtain rfl : k₁ = κ k := h1
      exact ⟨j, rfl⟩
    choose e he using hc
    have hb : Function.Bijective e := by
      constructor
      · intro i i' h
        have : v ⟨k, i⟩ = v ⟨k, i'⟩ := by rw [he, he, h]
        exact sigma_mk_injective (β := ι) (hv.2.1 this)
      · intro j
        obtain ⟨⟨k₀, i⟩, hq⟩ := hv.2.2.2 ⟨κ k, j⟩ ⟨k, rfl⟩
        have hk : κ k₀ = κ k := by
          have := hv.2.2.1 ⟨k₀, i⟩
          rw [hq] at this
          exact this.symm
        obtain rfl := hv.1 hk
        exact ⟨i, sigma_mk_injective (β := ι') ((he i).symm.trans hq)⟩
    refine (Fintype.sum_bijective e hb _ _ fun i => ?_).symm
    rw [← he, Finsupp.mapDomain_apply hv.2.1]
  · rw [Function.extend_apply' _ _ _ hk]
    refine Finset.sum_eq_zero fun i _ => Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨p, hp⟩
    refine hk ⟨p.1, ?_⟩
    rw [← hv.2.2.1 p, hp]

theorem i_algebra : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)), IsMultiProjPrime P → (∀ a, IsLineIso P a a 1 1) ∧ (∀ a b f g, IsLineIso P a b f g → IsLineIso P b a g f) ∧ (∀ a b c f g f' g', IsLineIso P a b f g → IsLineIso P b c f' g' → IsLineIso P a c (f * f') (g * g')) ∧ (∀ a b a' b' f g f' g', IsLineIso P a b f g → IsLineIso P a' b' f' g' → IsLineIso P (a + a') (b + b') (f * f') (g * g')) ∧ ∀ (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (P' : Ideal (MRing ι')), IsBlockMap κ v → imageZ v P' = P → ∀ a b f g, IsLineIso P a b f g → IsLineIso P' (pullDeg κ a) (pullDeg κ b) (rename v f) (rename v g) := by
  intro K _ ι _ P hP
  have hp : P.IsPrime := hP.1
  have tens : ∀ f g f' g' : MRing ι, UnitRatio P f g → UnitRatio P f' g' → UnitRatio P (f * f') (g * g') := by
    rintro f g f' g' ⟨hf, hg, h⟩ ⟨hf', hg', h'⟩
    refine ⟨fun hh => (hp.mem_or_mem hh).elim hf hf', fun hh => (hp.mem_or_mem hh).elim hg hg',
      fun W hW hPW hr => ?_⟩
    obtain ⟨u, v, hu, hv, huv⟩ := h W hW hPW hr
    obtain ⟨u', v', hu', hv', huv'⟩ := h' W hW hPW hr
    refine ⟨u * u', v * v', fun hh => (hW.mem_or_mem hh).elim hu hu', fun hh => (hW.mem_or_mem hh).elim hv hv', ?_⟩
    have := P.add_mem (P.mul_mem_left (u' * f') huv) (P.mul_mem_left (v * g) huv')
    convert this using 1
    ring
  refine ⟨fun a => ⟨⟨0, 0, ialg_one, ialg_one, by simp⟩, ?_⟩, ?_, ?_, ?_, ?_⟩
  · have h1 : (1 : MRing ι) ∉ P := (Ideal.ne_top_iff_one P).1 hp.ne_top
    exact ⟨h1, h1, fun W hW _ _ => ⟨1, 1, (Ideal.ne_top_iff_one W).1 hW.ne_top,
      (Ideal.ne_top_iff_one W).1 hW.ne_top, by simp⟩⟩
  · rintro a b f g ⟨⟨α, γ, h1, h2, h3⟩, hf, hg, h⟩
    refine ⟨⟨γ, α, h2, h1, fun k => by linarith [h3 k]⟩, hg, hf, fun W hW hPW hr => ?_⟩
    obtain ⟨u, v, hu, hv, huv⟩ := h W hW hPW hr
    exact ⟨v, u, hv, hu, by simpa using P.neg_mem huv⟩
  · rintro a b c f g f' g' ⟨⟨α, γ, h1, h2, h3⟩, h⟩ ⟨⟨α', γ', h1', h2', h3'⟩, h'⟩
    refine ⟨⟨α + α', γ + γ', ialg_mul h1 h1', ialg_mul h2 h2', fun k => ?_⟩, tens _ _ _ _ h h'⟩
    simp only [Pi.add_apply, Nat.cast_add]
    linarith [h3 k, h3' k]
  · rintro a b a' b' f g f' g' ⟨⟨α, γ, h1, h2, h3⟩, h⟩ ⟨⟨α', γ', h1', h2', h3'⟩, h'⟩
    refine ⟨⟨α + α', γ + γ', ialg_mul h1 h1', ialg_mul h2 h2', fun k => ?_⟩, tens _ _ _ _ h h'⟩
    simp only [Pi.add_apply, Nat.cast_add]
    linarith [h3 k, h3' k]
  · rintro K' _ ι' _ κ v P' hv rfl a b f g ⟨⟨α, γ, h1, h2, h3⟩, hf, hg, h⟩
    refine ⟨⟨Function.extend κ α 0, Function.extend κ γ 0, ialg_rename hv h1, ialg_rename hv h2, fun k' => ?_⟩,
      hf, hg, fun W hW hPW hr => ?_⟩
    · unfold pullDeg
      by_cases hk : ∃ k, κ k = k'
      · obtain ⟨k, rfl⟩ := hk
        simp only [hv.1.extend_apply]
        exact h3 k
      · simp only [Function.extend_apply' _ _ _ hk]
        simp
    · have hr' : IsRelevant (imageZ v W) := by
        intro k
        obtain ⟨i, hi⟩ := hr (κ k)
        obtain ⟨⟨k₀, j⟩, hq⟩ := hv.2.2.2 ⟨κ k, i⟩ ⟨k, rfl⟩
        have hk : κ k₀ = κ k := by
          have := hv.2.2.1 ⟨k₀, j⟩
          rw [hq] at this
          exact this.symm
        obtain rfl := hv.1 hk
        refine ⟨j, fun hh => hi ?_⟩
        have : rename v (X ⟨k₀, j⟩ : MRing ι) ∈ W := hh
        rwa [rename_X, hq] at this
      obtain ⟨u, w, hu, hw, huw⟩ := h (imageZ v W) (Ideal.comap_isPrime _ W) (Ideal.comap_mono hPW) hr'
      refine ⟨rename v u, rename v w, hu, hw, ?_⟩
      have : rename v (u * f - w * g) ∈ P' := huw
      simpa using this

end PositivityTheory.UnitarySelfGeneration
