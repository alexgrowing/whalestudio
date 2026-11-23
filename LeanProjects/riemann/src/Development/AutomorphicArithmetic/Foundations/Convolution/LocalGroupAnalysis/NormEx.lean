import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotStage

noncomputable section

open MeasureTheory Topology Set
open scoped ENNReal Pointwise

namespace UpperTheory.ConvolutionTheory.G

private theorem exists_bump {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] (H : Set G)
    (hH : IsClosed H) (h1 : (1 : G) ∈ H) (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    (hinv : ∀ a ∈ H, a⁻¹ ∈ H) :
    ∃ f : G → ℝ, Continuous f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, ∃ h ∈ H, 0 < f (h * x)) ∧
      ∀ C : Set G, IsCompact C → ∃ D : Set G, IsCompact D ∧ ∀ g ∈ H * C, f g ≠ 0 → g ∈ D := by
  classical
  let L : CompactExhaustion G := (CompactExhaustion.choice G).shiftr
  have L0 : L 0 = ∅ := rfl
  let A : ℕ → Set G := fun n => H * L n
  let O : ℕ → Set G := fun n => H * interior (L n)
  have hA : ∀ n, IsClosed (A n) := fun n => hH.mul_right_of_isCompact (L.isCompact n)
  have hO : ∀ n, IsOpen (O n) := fun n => isOpen_interior.mul_left
  have hOA : ∀ n, O n ⊆ A n := fun n => mul_subset_mul_left interior_subset
  have hAO : ∀ n, A n ⊆ O (n + 1) := fun n => mul_subset_mul_left (L.subset_interior_succ n)
  have hAm : Monotone A := fun a b h => mul_subset_mul_left (L.subset h)
  have hA0 : A 0 = ∅ := by simp [A, L0]
  have hLA : ∀ n, (L n : Set G) ⊆ A n := fun n x hx => ⟨1, h1, x, hx, one_mul x⟩
  have hdisj : ∀ n, Disjoint ((L (n + 1) : Set G) \ O n) (A (n - 1)) := by
    intro n
    rw [Set.disjoint_left]
    rintro x ⟨-, hx⟩ hxA
    cases n with
    | zero => simp [hA0] at hxA
    | succ n => exact hx (hAO n hxA)
  have hex : ∀ n, ∃ φ : C(G, ℝ), EqOn φ 1 ((L (n + 1) : Set G) \ O n) ∧ EqOn φ 0 (A (n - 1)) ∧
      HasCompactSupport φ ∧ ∀ x, φ x ∈ Icc (0 : ℝ) 1 := fun n =>
    exists_continuous_one_zero_of_isCompact ((L.isCompact (n + 1)).diff (hO n)) (hA (n - 1))
      (hdisj n)
  choose φ hφ1 hφ0 hφc hφI using hex
  have hvan : ∀ n k x, k < n → x ∈ A k → φ n x = 0 := fun n k x hkn hx =>
    hφ0 n (hAm (Nat.le_sub_one_of_lt hkn) hx)
  have hlf : LocallyFinite fun n => Function.support (φ n) := by
    intro x
    obtain ⟨k, hk⟩ := L.exists_mem_nhds x
    refine ⟨_, hk, (Set.finite_Iic k).subset ?_⟩
    rintro n ⟨y, hy, hyk⟩
    by_contra hn
    exact hy (hvan n k y (not_le.mp hn) (hLA k hyk))
  refine ⟨fun x => ∑ᶠ n, φ n x, continuous_finsum (fun n => (φ n).continuous) hlf,
    fun x => finsum_nonneg fun n => (hφI n x).1, ?_, ?_⟩
  · intro x
    have hexA : ∃ m, x ∈ A m := by
      obtain ⟨k, hk⟩ := L.exists_mem_nhds x
      exact ⟨k, hLA k (mem_of_mem_nhds hk)⟩
    have hm0 : Nat.find hexA ≠ 0 := by
      intro h0
      have := Nat.find_spec hexA
      rw [h0, hA0] at this
      exact this
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    have hxn : x ∉ A n := Nat.find_min hexA (by omega)
    have hxs : x ∈ A (n + 1) := by
      have := Nat.find_spec hexA
      rwa [hn] at this
    obtain ⟨h, hh, y, hy, rfl⟩ := hxs
    have hyO : y ∉ O n := by
      intro hyO
      obtain ⟨h', hh', z, hz, rfl⟩ := hyO
      exact hxn (hOA n ⟨h * h', hmul _ hh _ hh', z, hz, by simp [mul_assoc]⟩)
    refine ⟨h⁻¹, hinv h hh, ?_⟩
    have hy1 : φ n y = 1 := hφ1 n ⟨hy, hyO⟩
    have hfin : (Function.support fun m => φ m y).Finite := hlf.point_finite y
    have hle := single_le_finsum (f := fun m => φ m y) n hfin (fun m => (hφI m y).1)
    simp only [inv_mul_cancel_left]
    have : (1 : ℝ) ≤ ∑ᶠ m, φ m y := by simpa [hy1] using hle
    linarith
  · intro C hC
    obtain ⟨k, hk⟩ := L.exists_superset_of_isCompact hC
    refine ⟨⋃ n ∈ Finset.range (k + 1), tsupport (φ n),
      (Finset.range (k + 1)).isCompact_biUnion fun n _ => hφc n, ?_⟩
    intro g hg hfg
    have hgA : g ∈ A k := mul_subset_mul_left hk hg
    obtain ⟨n, hn⟩ : ∃ n, φ n g ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hfg (by simp [hcon])
    have hnk : n ≤ k := by
      by_contra hnk
      exact hn (hvan n k g (not_le.mp hnk) hgA)
    exact mem_biUnion (Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)))
      (subset_tsupport _ hn)

private theorem exists_nrm {G T : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [MeasurableSpace T] [BorelSpace T]
    (j : T →* G) (hj : IsClosedEmbedding j) (ν : Measure T) [ν.IsHaarMeasure]
    [ν.IsMulRightInvariant] (f : G → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hpos : ∀ x, ∃ h ∈ Set.range j, 0 < f (h * x))
    (hsupp : ∀ C : Set G, IsCompact C → ∃ D : Set G, IsCompact D ∧
      ∀ g ∈ Set.range j * C, f g ≠ 0 → g ∈ D) :
    ∃ ρ : G → NNReal, Continuous ρ ∧ IsNrm j ν (fun g => ρ g) ∧
      ∀ C : Set G, IsCompact C → ∃ D : Set G, IsCompact D ∧
        ∀ g ∈ Set.range j * C, ρ g ≠ 0 → g ∈ D := by
  have hcont2 : Continuous fun p : G × T => f (j p.2 * p.1) :=
    hf.comp ((hj.continuous.comp continuous_snd).mul continuous_fst)
  have hk : ∀ N : Set G, IsCompact N → ∃ k : Set T, IsCompact k ∧
      ∀ x ∈ N, ∀ t, t ∉ k → f (j t * x) = 0 := by
    intro N hN
    obtain ⟨D, hD, hDs⟩ := hsupp N hN
    refine ⟨j ⁻¹' (D * N⁻¹), hj.isCompact_preimage (hD.mul hN.inv), ?_⟩
    intro x hx t ht
    by_contra hne
    apply ht
    have hmem := hDs (j t * x) ⟨j t, mem_range_self t, x, hx, rfl⟩ hne
    exact ⟨j t * x, hmem, x⁻¹, Set.inv_mem_inv.mpr hx, by simp⟩
  have hcs : ∀ x, HasCompactSupport fun t => f (j t * x) := by
    intro x
    obtain ⟨k, hkc, hks⟩ := hk {x} isCompact_singleton
    exact HasCompactSupport.intro hkc fun t ht => hks x rfl t ht
  have hc1 : ∀ x, Continuous fun t => f (j t * x) := fun x =>
    hcont2.comp (Continuous.prodMk continuous_const continuous_id)
  have hint : ∀ x, Integrable (fun t => f (j t * x)) ν := fun x =>
    (hc1 x).integrable_of_hasCompactSupport (hcs x)
  let I : G → ℝ := fun x => ∫ t, f (j t * x) ∂ν
  have hIc : Continuous I := by
    rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨N, hNc, hNx⟩ := exists_compact_mem_nhds x
    obtain ⟨k, hkc, hks⟩ := hk N hNc
    have : ContinuousOn I N :=
      continuousOn_integral_of_compact_support (f := fun x t => f (j t * x)) hkc
        hcont2.continuousOn fun p t hp ht => hks p hp t ht
    exact this.continuousAt hNx
  have hIpos : ∀ x, 0 < I x := by
    intro x
    obtain ⟨_, ⟨t, rfl⟩, ht⟩ := hpos x
    exact (hc1 x).integral_pos_of_hasCompactSupport_nonneg_nonzero (hcs x)
      (fun s => hf0 _) ht.ne'
  have hIinv : ∀ s x, I (j s * x) = I x := by
    intro s x
    have := integral_mul_right_eq_self (μ := ν) (fun t => f (j t * x)) s
    simpa [I, mul_assoc] using this
  refine ⟨fun g => Real.toNNReal (f g / I g),
    continuous_real_toNNReal.comp (hf.div hIc fun x => (hIpos x).ne'), ⟨?_, ?_⟩, ?_⟩
  · exact measurable_coe_nnreal_ennreal.comp
      (continuous_real_toNNReal.comp (hf.div hIc fun x => (hIpos x).ne')).measurable
  · intro x
    have hrw : ∀ t, ((Real.toNNReal (f (j t * x) / I (j t * x)) : NNReal) : ℝ≥0∞) =
        ENNReal.ofReal (f (j t * x) / I x) := fun t => by rw [hIinv]; rfl
    simp_rw [hrw]
    rw [← ofReal_integral_eq_lintegral_ofReal ((hint x).div_const _)
      (Filter.Eventually.of_forall fun t => div_nonneg (hf0 _) (hIpos x).le), integral_div]
    rw [div_self (hIpos x).ne', ENNReal.ofReal_one]
  · intro C hC
    obtain ⟨D, hD, hDs⟩ := hsupp C hC
    refine ⟨D, hD, fun g hg hne => hDs g hg ?_⟩
    intro h0
    apply hne
    simp [h0]

theorem normEx : NormEx := by
  intro G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ μ j ν hp
  obtain ⟨-, hj, hν⟩ := hp
  haveI := hν.1
  haveI := hν.2
  haveI : ν.IsMulRightInvariant := by
    have h : ν.inv.IsMulRightInvariant := inferInstance
    rwa [Measure.inv_eq_self] at h
  obtain ⟨f, hf, hf0, hpos, hsupp⟩ := exists_bump (Set.range j) hj.isClosed_range
    ⟨1, map_one j⟩ (by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a * b, map_mul j a b⟩)
    (by rintro _ ⟨a, rfl⟩; exact ⟨a⁻¹, map_inv j a⟩)
  exact exists_nrm j hj ν f hf hf0 hpos hsupp

end UpperTheory.ConvolutionTheory.G
