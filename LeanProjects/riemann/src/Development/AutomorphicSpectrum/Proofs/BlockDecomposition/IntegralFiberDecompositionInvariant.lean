import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousConjNilSymm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableNilrad
open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.LocVan.NormaliserAbs

theorem exists_normaliser {H X : Type} [MeasurableSpace H] [MeasurableSpace X] (ν : Measure H)
    [SFinite ν]
    (act : H → X → X) (hact : Measurable (fun p : H × X => act p.1 p.2))
    (r : H → H → H) (hr : ∀ h₀, MeasurePreserving (r h₀) ν ν)
    (hrr : ∀ h₀ h x, act (r h₀ h) x = act h (act h₀ x))
    (D Z : ℕ → Set X) (hD : ∀ i, MeasurableSet (D i)) (hZ : ∀ i, MeasurableSet (Z i))
    (hinv : ∀ i h x, act h x ∈ Z i ↔ x ∈ Z i) (hcov : ∀ x, ∃ i, x ∈ Z i)
    (hfin : ∀ i x, ν {h | act h x ∈ D i} ≠ ⊤)
    (hpos : ∀ i x, x ∈ Z i → ν {h | act h x ∈ D i} ≠ 0)
    (S : Set (X → X)) (hSD : ∀ s ∈ S, ∀ i x, s x ∈ D i ↔ x ∈ D i)
    (hSZ : ∀ s ∈ S, ∀ i x, s x ∈ Z i ↔ x ∈ Z i)
    (hSa : ∀ s ∈ S, ∀ h, ∃ s' ∈ S, ∀ x, act h (s x) = s' (act h x)) :
    ∃ ρ : X → ℝ≥0∞, Measurable ρ ∧ (∀ x, ∫⁻ h, ρ (act h x) ∂ν = 1) ∧
      ∀ s ∈ S, ∀ x, ρ (s x) = ρ x := by
  classical
  set E : ℕ → Set X := fun i => D i \ ⋃ j : {j // j < i}, Z j with hE
  have hEm : ∀ i, MeasurableSet (E i) := fun i =>
    (hD i).diff (MeasurableSet.iUnion fun j => hZ j)
  set b : X → ℝ≥0∞ := fun x => ∑' i, (E i).indicator (1 : X → ℝ≥0∞) x with hb
  have hbm : Measurable b :=
    Measurable.ennreal_tsum fun i => measurable_one.indicator (hEm i)
  set B : X → ℝ≥0∞ := fun x => ∫⁻ h, b (act h x) ∂ν with hB
  have hBm : Measurable B :=
    Measurable.lintegral_prod_left' (μ := ν) (f := fun p : H × X => b (act p.1 p.2)) (hbm.comp hact)
  have hsec : ∀ x, Measurable fun h => act h x := fun x =>
    hact.comp (measurable_id.prodMk measurable_const)
  have hind : ∀ (i : ℕ) (x : X),
      ∫⁻ h, (D i).indicator (1 : X → ℝ≥0∞) (act h x) ∂ν = ν {h | act h x ∈ D i} := by
    intro i x
    have hm : MeasurableSet {h | act h x ∈ D i} := hsec x (hD i)
    have : (fun h => (D i).indicator (1 : X → ℝ≥0∞) (act h x))
        = {h | act h x ∈ D i}.indicator 1 := by
      funext h
      by_cases hh : act h x ∈ D i
      · simp [Set.indicator, hh]
      · simp [Set.indicator, hh]
    rw [this, lintegral_indicator_one hm]

  have hBpos : ∀ x, B x ≠ 0 ∧ B x ≠ ⊤ := by
    intro x
    have hex := hcov x
    set i₀ := Nat.find hex with hi₀
    have hxi : x ∈ Z i₀ := Nat.find_spec hex
    have hmin : ∀ j < i₀, x ∉ Z j := fun j hj => Nat.find_min hex hj
    have hup : ∀ h, b (act h x) ≤
        ∑ i ∈ Finset.range (i₀ + 1), (D i).indicator (1 : X → ℝ≥0∞) (act h x) := by
      intro h
      have hz : ∀ i ∉ Finset.range (i₀ + 1), (E i).indicator (1 : X → ℝ≥0∞) (act h x) = 0 := by
        intro i hi
        have hlt : i₀ < i := by simpa [Nat.lt_succ_iff] using hi
        apply Set.indicator_of_notMem
        intro hmem
        apply hmem.2
        exact Set.mem_iUnion.2 ⟨⟨i₀, hlt⟩, (hinv i₀ h x).2 hxi⟩
      rw [hb]
      simp only
      rw [tsum_eq_sum hz]
      refine Finset.sum_le_sum fun i _ => ?_
      exact Set.indicator_le_indicator_of_subset Set.diff_subset (fun _ => zero_le) _
    have hlow : ∀ h, (D i₀).indicator (1 : X → ℝ≥0∞) (act h x) ≤ b (act h x) := by
      intro h
      have : (D i₀).indicator (1 : X → ℝ≥0∞) (act h x)
          = (E i₀).indicator (1 : X → ℝ≥0∞) (act h x) := by
        by_cases hh : act h x ∈ D i₀
        · have hmem : act h x ∈ E i₀ := by
            refine ⟨hh, fun hu => ?_⟩
            obtain ⟨⟨j, hj⟩, hjz⟩ := Set.mem_iUnion.1 hu
            exact hmin j hj ((hinv j h x).1 hjz)
          simp [Set.indicator, hh, hmem]
        · have hmem : act h x ∉ E i₀ := fun hm => hh hm.1
          simp [Set.indicator, hh, hmem]
      rw [this]
      exact ENNReal.le_tsum i₀
    constructor
    · intro h0
      have : ν {h | act h x ∈ D i₀} ≤ B x := by
        rw [← hind]
        exact lintegral_mono hlow
      exact hpos i₀ x hxi (le_antisymm (h0 ▸ this) zero_le)
    · have h1 : B x ≤ ∑ i ∈ Finset.range (i₀ + 1), ν {h | act h x ∈ D i} := by
        calc B x ≤ ∫⁻ h, ∑ i ∈ Finset.range (i₀ + 1),
              (D i).indicator (1 : X → ℝ≥0∞) (act h x) ∂ν := lintegral_mono hup
          _ = ∑ i ∈ Finset.range (i₀ + 1),
              ∫⁻ h, (D i).indicator (1 : X → ℝ≥0∞) (act h x) ∂ν := by
              refine lintegral_finset_sum _ fun i _ => ?_
              exact (measurable_one.indicator (hD i)).comp (hsec x)
          _ = _ := Finset.sum_congr rfl fun i _ => hind i x
      exact ne_top_of_le_ne_top (ENNReal.sum_ne_top.2 fun i _ => hfin i x) h1
  have hBact : ∀ h₀ x, B (act h₀ x) = B x := by
    intro h₀ x
    have hg : Measurable fun h => b (act h x) := hbm.comp (hsec x)
    calc B (act h₀ x) = ∫⁻ h, b (act (r h₀ h) x) ∂ν :=
          lintegral_congr fun h => by rw [hrr]
      _ = B x := (hr h₀).lintegral_comp hg
  have hbS : ∀ s ∈ S, ∀ x, b (s x) = b x := by
    intro s hs x
    refine tsum_congr fun i => ?_
    have hiff : s x ∈ E i ↔ x ∈ E i := by
      simp only [hE, Set.mem_diff, Set.mem_iUnion, hSD s hs, hSZ s hs]
    by_cases hx : x ∈ E i
    · simp [Set.indicator, hx, hiff.2 hx]
    · have : s x ∉ E i := fun h => hx (hiff.1 h)
      simp [Set.indicator, hx, this]
  have hBS : ∀ s ∈ S, ∀ x, B (s x) = B x := by
    intro s hs x
    refine lintegral_congr fun h => ?_
    obtain ⟨s', hs', he⟩ := hSa s hs h
    rw [he, hbS s' hs']
  refine ⟨fun x => b x / B x, hbm.div hBm, ?_, ?_⟩
  · intro x
    have : (fun h => b (act h x) / B (act h x)) = fun h => b (act h x) * (B x)⁻¹ := by
      funext h
      rw [hBact, div_eq_mul_inv]
    simp only [this]
    have hgm : Measurable fun h => b (act h x) := hbm.comp (hsec x)
    rw [lintegral_mul_const _ hgm]
    exact ENNReal.mul_inv_cancel (hBpos x).1 (hBpos x).2
  · intro s hs x
    simp only [hbS s hs, hBS s hs]

end GlobalTheory.CompanionTheory.LocVan.NormaliserAbs
