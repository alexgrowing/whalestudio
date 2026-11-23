import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CompatibleChartProductProjectionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsSncAdaptedChartAtPointStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncAdaptedChartSectionFormStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.SncPull

theorem holoOn_comp_pr {e n : ℕ} {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    {A : FinHolAtlas e X} {Ab : FinHolAtlas n Z} {pr : X → Z} (hp : HoloMap A Ab pr)
    {U : Set Z} {g : Z → ℂ} (hg : Ab.HoloOn U g) : A.HoloOn (pr ⁻¹' U) (fun x => g (pr x)) := by
  intro j t ht
  obtain ⟨k, hk⟩ := Ab.cover (pr ((A.chart j).symm t))
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (pr ⁻¹' (Ab.chart k).source)) :=
    (A.chart j).isOpen_inter_preimage_symm ((Ab.chart k).open_source.preimage hp.1)
  have htO : t ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (pr ⁻¹' (Ab.chart k).source) :=
    ⟨ht.1, hk⟩
  have h1 : AnalyticAt ℂ (Ab.chart k ∘ pr ∘ (A.chart j).symm) t := hp.2 j k t htO
  have hmem : (Ab.chart k ∘ pr ∘ (A.chart j).symm) t ∈
      (Ab.chart k).target ∩ (Ab.chart k).symm ⁻¹' U := by
    refine ⟨(Ab.chart k).map_source hk, ?_⟩
    simp only [Function.comp, Set.mem_preimage, (Ab.chart k).left_inv hk]
    exact ht.2
  have h2 : AnalyticAt ℂ (g ∘ (Ab.chart k).symm) ((Ab.chart k ∘ pr ∘ (A.chart j).symm) t) :=
    hg k _ hmem
  have h3 := AnalyticAt.comp (g := g ∘ (Ab.chart k).symm)
    (f := Ab.chart k ∘ pr ∘ (A.chart j).symm) h2 h1
  refine h3.congr ?_
  filter_upwards [hO.mem_nhds htO] with t' ht'
  simp [Function.comp, (Ab.chart k).left_inv ht'.2]

theorem isSection_pull {e n : ℕ} {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    {A : FinHolAtlas e X} {Ab : FinHolAtlas n Z} {pr : X → Z} (hp : HoloMap A Ab pr)
    {L : LocPot Z} {s : Z → Z → ℂ} (hs : IsSection Ab L s) :
    IsSection A (L.pullback pr hp.1) (fun x y => s (pr x) (pr y)) :=
  ⟨fun x => holoOn_comp_pr hp (hs.1 (pr x)), fun x x' y hy => hs.2 (pr x) (pr x') (pr y) hy⟩

theorem isSNC_pull {e n : ℕ} {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    {A : FinHolAtlas e X} {Ab : FinHolAtlas n Z} {pr : X → Z} (hp : HoloMap A Ab pr)
    {L : LocPot Z} {s : Z → Z → ℂ} {nb : ℕ} {m : Fin nb → ℕ} {W : Fin nb → Set Z}
    (hsnc : IsSNC Ab L s m W)
    (hprod : ∀ x, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin Ab.n) (σ : Fin n ↪ Fin e),
      IsCompatChart A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (Ab.chart kb).source ∧
        ∀ i, Ab.chart kb (pr x') i = ψ x' (σ i))) :
    IsSNC A (L.pullback pr hp.1) (fun x y => s (pr x) (pr y)) m (fun k => pr ⁻¹' W k) := by
  intro x
  obtain ⟨ψb, hcb, hxb, hsub, σb, hinj, hW, u, hu, hu0, hfac⟩ := hsnc (pr x)
  obtain ⟨ψ, kb, σ, hc, hx, hpr⟩ := hprod x
  obtain ⟨ψ', hc', hsrc, hco⟩ := GlobalTheory.T.compatible_chart_product_projection e n X Z A Ab pr ψ kb σ ψb hc hcb hpr
  have hsrc' : ∀ y ∈ ψ'.source, pr y ∈ ψb.source := fun y hy => by
    rw [hsrc] at hy; exact hy.2
  refine ⟨ψ', hc', by rw [hsrc]; exact ⟨hx, hxb⟩, fun y hy => hsub (hsrc' y hy),
    fun k => (σb k).map σ, ?_, ?_, fun y => u (pr y), ?_, fun y hy => hu0 _ (hsrc' y hy), ?_⟩
  · intro k k' i hk hk'
    obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 hk
    obtain ⟨b, hb, hab⟩ := Option.map_eq_some_iff.1 hk'
    obtain rfl := σ.injective hab
    exact hinj k k' _ ha hb
  · intro k
    ext y
    constructor
    · rintro ⟨hyW, hy⟩
      have h1 : pr y ∈ W k ∩ ψb.source := ⟨hyW, hsrc' y hy⟩
      rw [hW k] at h1
      obtain ⟨-, i, hi, h0⟩ := h1
      exact ⟨hy, σ i, by simp [hi], by rw [hco y hy]; exact h0⟩
    · rintro ⟨hy, i, hi, h0⟩
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 hi
      rw [hco y hy] at h0
      have h1 : pr y ∈ W k ∩ ψb.source := by
        rw [hW k]; exact ⟨hsrc' y hy, a, ha, h0⟩
      exact ⟨h1.1, hy⟩
  · exact fun j => (holoOn_comp_pr hp hu j).mono fun t ht => ⟨ht.1, hsrc' _ ht.2⟩
  · intro y hy
    show s (pr x) (pr y) = _
    rw [hfac _ (hsrc' y hy)]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    cases h : σb k with
    | none => simp [h]
    | some i => simp [h, hco y hy]

theorem exists_adapted {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) {nb : ℕ} {m : Fin nb → ℕ}
    {W : Fin nb → Set X} (hL : IsPotential A L) (hs : IsSection A L s) (hsnc : IsSNC A L s m W) :
    ∃ B : FinHolAtlas e X, IsAdaptedAtlas A B L s := by
  choose φ S μ v hc hx hball h0 hU hμ hv hv0 hfac using GlobalTheory.T.exists_snc_adapted_chart_at_point e X A L s nb m W hsnc
  have hb := fun x => GlobalTheory.T.snc_adapted_chart_section_form e X A L s hL hs x (φ x) (S x) (μ x) (v x) (hc x) (hball x) (hU x)
    (hμ x) (hv x) (hv0 x) (hfac x)
  choose hzero M hM using fun x => And.intro (hb x).1 (hb x).2
  have hopen : ∀ x, IsOpen ((φ x).source ∩ φ x ⁻¹' Metric.ball (0 : Fin e → ℂ) 1) := fun x =>
    (φ x).continuousOn.isOpen_inter_preimage (φ x).open_source Metric.isOpen_ball
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ hopen (fun x _ =>
    Set.mem_iUnion.2 ⟨x, hx x, by simp [h0 x]⟩)
  let E := t.equivFin
  have hcov : ∀ x, ∃ i : Fin t.card, x ∈ (φ (E.symm i).1).source ∧
      φ (E.symm i).1 x ∈ Metric.ball (0 : Fin e → ℂ) 1 := by
    intro x
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    refine ⟨E ⟨p, hp⟩, ?_⟩
    simpa using hxp
  obtain ⟨B, hAB, hB1, hB2⟩ := atlasOfCompat A (fun i : Fin t.card => φ (E.symm i).1)
    (fun i => hc _) (fun x => (hcov x).imp fun _ h => h.1)
  refine ⟨B, hAB, ?_, ?_, ∑ i : Fin t.card, |M (E.symm i).1|, ?_⟩
  · intro j
    obtain ⟨i, hi⟩ := hB2 j
    rw [hi]; exact hball _
  · intro x
    obtain ⟨i, hi, hi'⟩ := hcov x
    obtain ⟨j, hj⟩ := hB1 i
    exact ⟨j, by rw [hj]; exact hi, by rw [hj]; exact hi'⟩
  · intro j
    obtain ⟨i, hi⟩ := hB2 j
    refine ⟨S (E.symm i).1, μ (E.symm i).1, hμ _, ?_, ?_⟩
    · rw [hi]; exact hzero _
    · rw [hi]
      intro y hy hy'
      exact ((hM _ y hy hy').trans (le_abs_self _)).trans
        (Finset.single_le_sum (f := fun i : Fin t.card => |M (E.symm i).1|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ i))

theorem pullback_projection : ∀ (e n : ℕ) (X Z : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [TopologicalSpace Z] [CompactSpace Z] [T2Space Z] (A : FinHolAtlas e X) (Ab Bb : FinHolAtlas n Z) (pr : X → Z) (hp : HoloMap A Ab pr) (L : LocPot Z) (s : Z → Z → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set Z), IsPotential Ab L → IsSection Ab L s → IsSNC Ab L s m W → (∀ x, logNormSec L s x ≤ 0) → (∀ x, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin Ab.n) (σ : Fin n ↪ Fin e), IsCompatChart A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (Ab.chart kb).source ∧ ∀ i, Ab.chart kb (pr x') i = ψ x' (σ i))) → IsPotential A (L.pullback pr hp.1) ∧ IsSection A (L.pullback pr hp.1) (fun x y => s (pr x) (pr y)) ∧ IsSNC A (L.pullback pr hp.1) (fun x y => s (pr x) (pr y)) m (fun k => pr ⁻¹' W k) ∧ ∃ B : FinHolAtlas e X, IsAdaptedAtlas A B (L.pullback pr hp.1) (fun x y => s (pr x) (pr y)) := by
  intro e n X Z _ _ _ _ _ _ A Ab Bb pr hp L s nb m W hL hs hsnc _ hprod
  have hL' := ReciprocityTheory.AnForm.M.isPotentialPullback Ab A pr hp L hL
  have hs' := isSection_pull hp hs
  have hn' := isSNC_pull hp hsnc hprod
  exact ⟨hL', hs', hn', exists_adapted A _ _ hL' hs' hn'⟩

end GlobalTheory.CompanionTheory.Ar.PB.SncPull
