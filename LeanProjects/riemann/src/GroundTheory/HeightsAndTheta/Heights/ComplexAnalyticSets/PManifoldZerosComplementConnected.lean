import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StManifoldZerosComplementConnected
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Set

theorem ManifoldZerosComplementConnected.isPreconnected_of_local {α : Type*} [TopologicalSpace α]
    {X S : Set α} (hX : IsPreconnected X) (hSX : S ⊆ X) (hdense : ∀ x ∈ X, x ∈ closure S)
    (hloc : ∀ x ∈ X, ∃ W, IsOpen W ∧ x ∈ W ∧ IsPreconnected (W ∩ S)) : IsPreconnected S := by
  intro u v hu hv hSuv ⟨a, haS, hau⟩ ⟨b, hbS, hbv⟩
  by_contra hne
  have hne' : ∀ y ∈ S, y ∈ u → y ∈ v → False := fun y hy hyu hyv => hne ⟨y, hy, hyu, hyv⟩
  let P : Set α := {x | ∃ W, IsOpen W ∧ x ∈ W ∧ W ∩ S ⊆ u}
  let Q : Set α := {x | ∃ W, IsOpen W ∧ x ∈ W ∧ W ∩ S ⊆ v}
  have hP : IsOpen P := isOpen_iff_forall_mem_open.mpr fun x ⟨W, hW, hxW, hWS⟩ =>
    ⟨W, fun y hy => ⟨W, hW, hy, hWS⟩, hW, hxW⟩
  have hQ : IsOpen Q := isOpen_iff_forall_mem_open.mpr fun x ⟨W, hW, hxW, hWS⟩ =>
    ⟨W, fun y hy => ⟨W, hW, hy, hWS⟩, hW, hxW⟩
  have hcov : X ⊆ P ∪ Q := by
    intro x hx
    obtain ⟨W, hW, hxW, hWc⟩ := hloc x hx
    by_cases h1 : (W ∩ S ∩ u).Nonempty
    · by_cases h2 : (W ∩ S ∩ v).Nonempty
      · obtain ⟨y, hyWS, hyu, hyv⟩ := hWc u v hu hv (fun y hy => hSuv hy.2) h1 h2
        exact (hne' y hyWS.2 hyu hyv).elim
      · refine Or.inl ⟨W, hW, hxW, fun y hy => ?_⟩
        rcases hSuv hy.2 with h | h
        · exact h
        · exact absurd ⟨y, hy, h⟩ h2
    · refine Or.inr ⟨W, hW, hxW, fun y hy => ?_⟩
      rcases hSuv hy.2 with h | h
      · exact absurd ⟨y, hy, h⟩ h1
      · exact h
  obtain ⟨x, hxX, ⟨W₁, hW₁, hxW₁, hW₁u⟩, ⟨W₂, hW₂, hxW₂, hW₂v⟩⟩ :=
    hX P Q hP hQ hcov ⟨a, hSX haS, u, hu, hau, inter_subset_left⟩
      ⟨b, hSX hbS, v, hv, hbv, inter_subset_left⟩
  obtain ⟨y, ⟨hy₁, hy₂⟩, hyS⟩ := mem_closure_iff.mp (hdense x hxX) _ (hW₁.inter hW₂) ⟨hxW₁, hxW₂⟩
  exact hne' y hyS (hW₁u ⟨hy₁, hyS⟩) (hW₂v ⟨hy₂, hyS⟩)

theorem ManifoldZerosComplementConnected.isPreconnected_ball_diff_countable {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (hE : 1 < Module.rank ℝ E) (c : E) {r : ℝ} (hr : 0 < r)
    {s : Set E} (hs : s.Countable) : IsPreconnected (Metric.ball c r \ s) := by
  let e : OpenPartialHomeomorph E E := OpenPartialHomeomorph.univBall c r
  have hsrc : e.source = univ := OpenPartialHomeomorph.univBall_source c r
  have htgt : e.target = Metric.ball c r := OpenPartialHomeomorph.univBall_target c hr
  have hc : (e ⁻¹' s).Countable := hs.preimage_of_injOn (e.injOn.mono (by rw [hsrc]; exact subset_univ _))
  have hcont : ContinuousOn e univ := hsrc ▸ e.continuousOn
  have heq : e '' (e ⁻¹' s)ᶜ = Metric.ball c r \ s := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨htgt ▸ e.map_source (hsrc ▸ mem_univ v), hv⟩
    · rintro ⟨hw, hws⟩
      rw [← htgt] at hw
      exact ⟨e.symm w, by simpa [mem_compl_iff, mem_preimage, e.right_inv hw] using hws, e.right_inv hw⟩
  rw [← heq]
  exact (hc.isConnected_compl_of_one_lt_rank hE).isPreconnected.image e (hcont.mono (subset_univ _))

theorem ManifoldZerosComplementConnected.isPreconnected_inter_ne_zero_of_complex {V : Set ℂ}
    (hVo : IsOpen V) (hV : IsPreconnected V) {φ : ℂ → ℂ} (hφ : AnalyticOnNhd ℂ φ V) {z₀ : ℂ}
    (hz₀ : z₀ ∈ V) (hφz₀ : φ z₀ ≠ 0) : IsPreconnected (V ∩ {z | φ z ≠ 0}) := by
  have hev : ∀ z ∈ V, ∀ᶠ w in 𝓝[≠] z, φ w ≠ 0 := by
    intro z hz
    rcases (hφ z hz).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd (hφ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hV hz h hz₀) hφz₀
    · exact h
  refine ManifoldZerosComplementConnected.isPreconnected_of_local hV inter_subset_left ?_ ?_
  · intro z hz
    have h1 : ∀ᶠ w in 𝓝[≠] z, w ∈ V ∩ {z | φ z ≠ 0} :=
      ((hev z hz).and (nhdsWithin_le_nhds (hVo.mem_nhds hz))).mono fun w hw => ⟨hw.2, hw.1⟩
    exact mem_closure_iff_frequently.mpr (h1.frequently.filter_mono nhdsWithin_le_nhds)
  · intro z hz
    obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp hVo z hz
    obtain ⟨r', hr', hr'φ⟩ := Metric.eventually_nhds_iff_ball.mp (eventually_nhdsWithin_iff.mp (hev z hz))
    have hρ : 0 < min r r' := lt_min hr hr'
    refine ⟨Metric.ball z (min r r'), Metric.isOpen_ball, Metric.mem_ball_self hρ, ?_⟩
    have heq : Metric.ball z (min r r') ∩ (V ∩ {w | φ w ≠ 0}) =
        Metric.ball z (min r r') \ ({z} \ {w | φ w ≠ 0}) := by
      ext w
      simp only [mem_inter_iff, Set.mem_sdiff, mem_singleton_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨hb, -, hne⟩
        exact ⟨hb, fun h => h.2 hne⟩
      · rintro ⟨hb, hw⟩
        refine ⟨hb, hrV (Metric.ball_subset_ball (min_le_left _ _) hb), ?_⟩
        by_cases hwz : w = z
        · intro h0
          exact hw ⟨hwz, fun h => h h0⟩
        · exact hr'φ w (Metric.ball_subset_ball (min_le_right _ _) hb) hwz
    rw [heq]
    exact ManifoldZerosComplementConnected.isPreconnected_ball_diff_countable
      (by rw [Complex.rank_real_complex]; exact_mod_cast (by norm_num : (1 : ℕ) < 2)) z hρ ((countable_singleton z).mono sdiff_subset)

theorem ManifoldZerosComplementConnected.isPreconnected_convex_inter_ne_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E} (hUo : IsOpen U) (hUc : Convex ℝ U)
    {f : E → ℂ} (hf : AnalyticOnNhd ℂ f U) : IsPreconnected (U ∩ {z | f z ≠ 0}) := by
  refine isPreconnected_of_forall_pair ?_
  rintro p ⟨hpU, hp⟩ q ⟨hqU, hq⟩
  let ℓ : ℂ → E := fun t => p + t • (q - p)
  have hℓc : Continuous ℓ := by fun_prop
  have hℓa : ∀ t, AnalyticAt ℂ ℓ t := fun t =>
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hVo : IsOpen (ℓ ⁻¹' U) := hUo.preimage hℓc
  have hVc : Convex ℝ (ℓ ⁻¹' U) := by
    intro a ha b hb s t hs ht hst
    have hmem := hUc ha hb hs ht hst
    show ℓ (s • a + t • b) ∈ U
    convert hmem using 1
    obtain rfl : t = 1 - s := by linarith
    simp only [ℓ, ← Complex.coe_smul]
    push_cast
    module
  have h0 : (0 : ℂ) ∈ ℓ ⁻¹' U := by simpa [ℓ] using hpU
  have h1 : (1 : ℂ) ∈ ℓ ⁻¹' U := by simpa [ℓ] using hqU
  refine ⟨ℓ '' (ℓ ⁻¹' U ∩ {t | f (ℓ t) ≠ 0}), ?_, ⟨0, ⟨h0, by simpa [ℓ] using hp⟩, by simp [ℓ]⟩,
    ⟨1, ⟨h1, by simpa [ℓ] using hq⟩, by simp [ℓ]⟩, ?_⟩
  · rintro _ ⟨t, ⟨htV, ht⟩, rfl⟩
    exact ⟨htV, ht⟩
  · exact (ManifoldZerosComplementConnected.isPreconnected_inter_ne_zero_of_complex hVo
      hVc.isPreconnected (φ := fun t => f (ℓ t)) (fun t ht => (hf (ℓ t) ht).comp (hℓa t)) h0
      (by simpa [ℓ] using hp)).image ℓ hℓc.continuousOn

theorem ManifoldZerosComplementConnected.proof : ManifoldZerosComplementConnected.Statement := by
  intro σ _ R h hR hreg hh ⟨x₀, hx₀R, hx₀⟩

  have chart : ∀ x ∈ R, ∃ (d : ℕ) (B : Set (Fin d → ℂ)) (W : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen B ∧ Convex ℝ B ∧ IsOpen W ∧ x ∈ W ∧ AnalyticOnNhd ℂ g B ∧ R ∩ W = g '' B := by
    intro x hx
    obtain ⟨-, d, A, O, V, g, hO, hV, hxV, hg, hAg, hRV⟩ := hreg x hx
    have hxO : A x ∈ O := by
      obtain ⟨y, hy, hgy⟩ : x ∈ g '' O := hRV ▸ ⟨hx, hxV⟩
      rw [← hgy, hAg y hy]
      exact hy
    obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.mp hO (A x) hxO
    refine ⟨d, Metric.ball (A x) ε, V ∩ A ⁻¹' Metric.ball (A x) ε, g, Metric.isOpen_ball,
      convex_ball _ _, hV.inter (Metric.isOpen_ball.preimage A.continuous),
      ⟨hxV, Metric.mem_ball_self hε⟩, hg.mono hεO, ?_⟩
    ext z
    constructor
    · rintro ⟨hzR, hzV, hzB⟩
      obtain ⟨y, hy, rfl⟩ : z ∈ g '' O := hRV ▸ ⟨hzR, hzV⟩
      have hAy : A (g y) ∈ Metric.ball (A x) ε := hzB
      rw [hAg y hy] at hAy
      exact ⟨y, hAy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      have hgy : g y ∈ R ∩ V := by rw [hRV]; exact ⟨y, hεO hy, rfl⟩
      refine ⟨hgy.1, hgy.2, ?_⟩
      show A (g y) ∈ Metric.ball (A x) ε
      rw [hAg y (hεO hy)]
      exact hy
  have chartR : ∀ {d : ℕ} {B : Set (Fin d → ℂ)} {W : Set (σ → ℂ)} {g : (Fin d → ℂ) → σ → ℂ},
      R ∩ W = g '' B → ∀ y ∈ B, g y ∈ R := by
    intro d B W g hRW y hy
    have : g y ∈ R ∩ W := by rw [hRW]; exact ⟨y, hy, rfl⟩
    exact this.1

  let T : Set (σ → ℂ) := {x | ∀ᶠ z in 𝓝 x, z ∈ R → h z = 0}
  have hTo : IsOpen T := isOpen_setOfPred_eventually_nhds
  let T₂ : Set (σ → ℂ) := {x | ∃ W, IsOpen W ∧ x ∈ W ∧ ∀ z ∈ W ∩ R, z ∉ T}
  have hT₂o : IsOpen T₂ := isOpen_iff_forall_mem_open.mpr fun x ⟨W, hW, hxW, hWT⟩ =>
    ⟨W, fun y hy => ⟨W, hW, hy, hWT⟩, hW, hxW⟩
  have hcov : R ⊆ T ∪ T₂ := by
    intro x hx
    obtain ⟨d, B, W, g, hBo, hBc, hWo, hxW, hg, hRW⟩ := chart x hx
    have hhg : AnalyticOnNhd ℂ (fun y => h (g y)) B := fun y hy =>
      (hh (g y) (chartR hRW y hy)).comp (hg y hy)
    by_cases hzero : ∃ y ∈ B, ∀ᶠ y' in 𝓝 y, h (g y') = 0
    · obtain ⟨y, hy, hev⟩ := hzero
      have hEq := hhg.eqOn_zero_of_preconnected_of_eventuallyEq_zero hBc.isPreconnected hy hev
      left
      show ∀ᶠ z in 𝓝 x, z ∈ R → h z = 0
      filter_upwards [hWo.mem_nhds hxW] with z hzW hzR
      obtain ⟨y', hy', rfl⟩ : z ∈ g '' B := hRW ▸ ⟨hzR, hzW⟩
      exact hEq hy'
    · right
      refine ⟨W, hWo, hxW, ?_⟩
      rintro z ⟨hzW, hzR⟩ hzT
      obtain ⟨y, hy, rfl⟩ : z ∈ g '' B := hRW ▸ ⟨hzR, hzW⟩
      have hzT' : ∀ᶠ w in 𝓝 (g y), w ∈ R → h w = 0 := hzT
      refine hzero ⟨y, hy, ?_⟩
      filter_upwards [(hg y hy).continuousAt.tendsto.eventually hzT', hBo.mem_nhds hy] with y' h1 h2
      exact h1 (chartR hRW y' h2)

  have hTR : ∀ x ∈ R, ¬ ∀ᶠ z in 𝓝 x, z ∈ R → h z = 0 := by
    intro x hx hxT
    have hx₀T₂ : x₀ ∈ T₂ := by
      rcases hcov hx₀R with h1 | h1
      · exact absurd ((show ∀ᶠ z in 𝓝 x₀, z ∈ R → h z = 0 from h1).self_of_nhds hx₀R) hx₀
      · exact h1
    obtain ⟨y, hyR, hyT, W, -, hyW, hWT⟩ := hR T T₂ hTo hT₂o hcov ⟨x, hx, hxT⟩ ⟨x₀, hx₀R, hx₀T₂⟩
    exact hWT y ⟨hyW, hyR⟩ hyT
  refine ManifoldZerosComplementConnected.isPreconnected_of_local hR sdiff_subset ?_ ?_
  · intro x hx
    rw [mem_closure_iff_frequently]
    exact (Filter.not_eventually.mp (hTR x hx)).mono fun z hz => Classical.not_imp.mp hz
  · intro x hx
    obtain ⟨d, B, W, g, hBo, hBc, hWo, hxW, hg, hRW⟩ := chart x hx
    have hhg : AnalyticOnNhd ℂ (fun y => h (g y)) B := fun y hy =>
      (hh (g y) (chartR hRW y hy)).comp (hg y hy)
    refine ⟨W, hWo, hxW, ?_⟩
    have heq : W ∩ (R \ {z | h z = 0}) = g '' (B ∩ {y | h (g y) ≠ 0}) := by
      ext z
      constructor
      · rintro ⟨hzW, hzR, hz⟩
        obtain ⟨y, hy, rfl⟩ : z ∈ g '' B := hRW ▸ ⟨hzR, hzW⟩
        exact ⟨y, ⟨hy, hz⟩, rfl⟩
      · rintro ⟨y, ⟨hy, hy'⟩, rfl⟩
        have hgy : g y ∈ R ∩ W := by rw [hRW]; exact ⟨y, hy, rfl⟩
        exact ⟨hgy.2, hgy.1, hy'⟩
    rw [heq]
    exact (ManifoldZerosComplementConnected.isPreconnected_convex_inter_ne_zero hBo hBc hhg).image g
      (hg.continuousOn.mono inter_subset_left)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
