import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqSemiMeasOfCovolOne

open MeasureTheory Function GlobalTheory.MixPer GlobalTheory.SemiHaar
open scoped Pointwise NNReal ENNReal

namespace GlobalTheory

theorem semiHaar_exists_fd_setIntegral : ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (N R : Subgroup G) (s : H →* G), IsClosed (N : Set G) → Continuous s → (∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N) →
    N ⊔ s.range = R → (∃ p : R → H, Continuous p ∧ ∀ (h : H) (n : N) (hm : n.1 * s h ∈ R), p ⟨n.1 * s h, hm⟩ = h) →
    ∀ (Γ : Subgroup G) [Countable Γ] (Λ : Subgroup H) [Countable Λ], (∀ n ∈ N, ∀ h, n * s h ∈ Γ ↔ n ∈ Γ ∧ h ∈ Λ) →
    ∀ (K : Set H), IsCompact K → (∀ h, ∃ δ ∈ Λ, δ * h ∈ K) →
    ∀ (μ : Measure H) [μ.IsHaarMeasure] (𝓕 : Set H), IsFundamentalDomain Λ 𝓕 μ → μ 𝓕 = 1 →
    ∀ (ν : Measure N) [ν.IsHaarMeasure] (𝓐 : Set N), IsFundamentalDomain (Γ.subgroupOf N) 𝓐 ν → ν 𝓐 = 1 →
    ∃ (κ : Measure R) (𝓡 : Set R), κ.IsHaarMeasure ∧ IsFundamentalDomain (Γ.subgroupOf R) 𝓡 κ ∧ κ 𝓡 = 1 ∧
      ∀ φ : G → ℂ, Continuous φ → (∃ C, ∀ x ∈ R, ‖φ x‖ ≤ C) →
        ∫ x in 𝓡, φ x ∂κ = ∫ h in 𝓕, ∫ m in 𝓐, φ (m.1 * s h) ∂ν ∂μ := by
  intro G H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N R s hN hs hnorm hR hp Γ _ Λ _ hrat K hK hcov μ _ 𝓕 h𝓕 h𝓕1 ν _ 𝓐 h𝓐 h𝓐1
  subst hR
  haveI : LocallyCompactSpace N := hN.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology (N ⊔ s.range : Subgroup G) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI := countable_subgroupOf Γ N
  haveI := countable_subgroupOf Γ (N ⊔ s.range)
  obtain ⟨p, hp1, hp2⟩ := hp
  have hp' : ∃ p : (N ⊔ s.range : Subgroup G) → H, Continuous p ∧ ∀ (h : H) (n : N), p (mk N s (h, n)) = h :=
    ⟨p, hp1, fun h n => hp2 h n _⟩
  obtain ⟨e, he⟩ := exists_homeo N s hnorm hs hp'
  have hΛ : ∀ δ ∈ Λ, s δ ∈ Γ := fun δ hδ => by simpa using (hrat 1 (one_mem _) δ).2 ⟨one_mem _, hδ⟩
  have hfin : ν 𝓐 ≠ ⊤ := by rw [h𝓐1]; exact ENNReal.one_ne_top
  obtain ⟨hhaar, -⟩ := semiMeas_haar_inv N s hN hs hnorm hp' Γ Λ hΛ hK hcov μ h𝓕 ν h𝓐 hfin
  have hsm : semiMeas N s μ ν = (μ.prod ν).map e := by rw [he]; rfl
  have hmp : MeasurePreserving e.toMeasurableEquiv (μ.prod ν) (semiMeas N s μ ν) :=
    ⟨e.toMeasurableEquiv.measurable, hsm.symm⟩
  have happ : ∀ S, semiMeas N s μ ν S = μ.prod ν (e ⁻¹' S) := fun S => by
    rw [hsm]; exact MeasurableEquiv.map_apply e.toMeasurableEquiv S
  set A : Set (N ⊔ s.range : Subgroup G) := e.symm ⁻¹' (𝓕 ×ˢ 𝓐) with hA
  have hmemA : ∀ q, e q ∈ A ↔ q.1 ∈ 𝓕 ∧ q.2 ∈ 𝓐 := fun q => by simp [hA]
  have hpre : e ⁻¹' A = 𝓕 ×ˢ 𝓐 := Set.ext hmemA
  have hA1 : semiMeas N s μ ν A = 1 := by
    rw [happ, hpre, Measure.prod_prod, h𝓕1, h𝓐1, mul_one]
  have hfd : IsFundamentalDomain (Γ.subgroupOf (N ⊔ s.range)) A (semiMeas N s μ ν) := by
    refine IsFundamentalDomain.mk'' ?_ ?_ ?_ ?_
    · exact (h𝓕.nullMeasurableSet.prod h𝓐.nullMeasurableSet).preimage hmp.symm.quasiMeasurePreserving
    · rw [hsm]
      refine (e.toMeasurableEquiv.measurableEmbedding.ae_map_iff).2 ?_
      have h1 : ∀ᵐ n ∂ν, ∀ δ : Λ, ∃ g : Γ.subgroupOf N, g • cj N s hnorm δ n ∈ 𝓐 := ae_all_iff.2 fun δ =>
        (MeasurePreserving.quasiMeasurePreserving ⟨(map_continuous (cj N s hnorm δ)).measurable,
          map_cj_of_mem N s hN hnorm Γ ν h𝓐 hfin (hΛ δ δ.2)⟩).ae h𝓐.ae_covers
      filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae h𝓕.ae_covers,
        (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae h1] with q ⟨δ, hδ⟩ h2
      obtain ⟨g, hg⟩ := h2 δ
      refine ⟨⟨mk N s (δ.1, g.1), (hrat _ g.1.2 _).2 ⟨g.2, δ.2⟩⟩, ?_⟩
      change mk N s (δ.1, g.1) * e q ∈ A
      rw [he, mk_mul N s hnorm, ← he, hmemA]
      exact ⟨hδ, hg⟩
    · rintro ⟨g, hg⟩ hne
      obtain ⟨⟨δ, n'⟩, rfl⟩ := mk_surjective N s hnorm g
      obtain ⟨hn', hδ⟩ := (hrat _ n'.2 _).1 hg
      have key : ∀ q ∈ e ⁻¹' (((⟨mk N s (δ, n'), hg⟩ : Γ.subgroupOf (N ⊔ s.range)) • A) ∩ A),
          (q.1 ∈ 𝓕 ∧ q.2 ∈ 𝓐) ∧ ∃ h₁ ∈ 𝓕, ∃ n₁ ∈ 𝓐, q = (δ * h₁, n' * cj N s hnorm δ n₁) := by
        rintro q ⟨⟨a, ha, hq⟩, h2⟩
        obtain ⟨q₁, rfl⟩ := e.surjective a
        refine ⟨(hmemA q).1 h2, q₁.1, ((hmemA q₁).1 ha).1, q₁.2, ((hmemA q₁).1 ha).2, e.injective ?_⟩
        rw [← hq]
        change mk N s (δ, n') * e q₁ = _
        rw [he, mk_mul N s hnorm]
      rw [AEDisjoint, happ]
      by_cases h1 : δ = 1
      · subst h1
        have hn1 : (⟨n', hn'⟩ : Γ.subgroupOf N) ≠ 1 := fun h => hne (by
          have : n' = 1 := congrArg Subtype.val h
          subst this
          exact Subtype.ext (Subtype.ext (by simp [mk])))
        have h0 := h𝓐.aedisjoint hn1
        refine measure_mono_null (t := Set.univ ×ˢ (((⟨n', hn'⟩ : Γ.subgroupOf N) • 𝓐) ∩ (1 : Γ.subgroupOf N) • 𝓐))
          (fun q hq => ?_) (by rw [Measure.prod_prod, show ν _ = 0 from h0, mul_zero])
        obtain ⟨h2, h₁, -, n₁, hn₁, rfl⟩ := key q hq
        refine ⟨trivial, ⟨n₁, hn₁, ?_⟩, by rw [one_smul]; exact h2.2⟩
        exact Subtype.ext (by change n'.1 * n₁.1 = n'.1 * (s 1 * n₁.1 * (s 1)⁻¹); simp)
      · have h0 := h𝓕.aedisjoint (show (⟨δ, hδ⟩ : Λ) ≠ 1 from fun h => h1 (congrArg Subtype.val h))
        refine measure_mono_null (t := (((⟨δ, hδ⟩ : Λ) • 𝓕) ∩ (1 : Λ) • 𝓕) ×ˢ Set.univ)
          (fun q hq => ?_) (by rw [Measure.prod_prod, show μ _ = 0 from h0, zero_mul])
        obtain ⟨h2, h₁, hh₁, n₁, -, rfl⟩ := key q hq
        exact ⟨⟨⟨h₁, hh₁, rfl⟩, by rw [one_smul]; exact h2.1⟩, trivial⟩
    · intro g
      exact (measurePreserving_mul_left (semiMeas N s μ ν) g.1).quasiMeasurePreserving
  refine ⟨semiMeas N s μ ν, A, hhaar, hfd, hA1, fun φ hφ hC => ?_⟩
  obtain ⟨C, hC⟩ := hC
  have hcont : Continuous fun q : H × N => φ (q.2.1 * s q.1) :=
    hφ.comp ((continuous_subtype_val.comp continuous_snd).mul (hs.comp continuous_fst))
  have h1 : ∫ x in A, φ x ∂(semiMeas N s μ ν) = ∫ q in 𝓕 ×ˢ 𝓐, φ (q.2.1 * s q.1) ∂(μ.prod ν) := by
    rw [← hpre, ← hmp.setIntegral_preimage_emb e.toMeasurableEquiv.measurableEmbedding]
    change ∫ x in e ⁻¹' A, φ ((e x : (N ⊔ s.range : Subgroup G)) : G) ∂(μ.prod ν) = _
    rw [he]; rfl
  rw [h1]
  have hint : IntegrableOn (fun q : H × N => φ (q.2.1 * s q.1)) (𝓕 ×ˢ 𝓐) (μ.prod ν) := by
    refine Measure.integrableOn_of_bounded (M := C) ?_ hcont.aestronglyMeasurable ?_
    · rw [Measure.prod_prod, h𝓕1, h𝓐1, mul_one]; exact ENNReal.one_ne_top
    · exact Filter.Eventually.of_forall fun q => hC _ (mk N s q).2
  exact setIntegral_prod _ hint

end GlobalTheory
