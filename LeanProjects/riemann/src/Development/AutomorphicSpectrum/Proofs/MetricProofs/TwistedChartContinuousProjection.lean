import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsLocSec
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CompatibleChartProductProjectionTwistedStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.SncProd

theorem compat_restr {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (h : IsCompatChart A ψ) (V : Set X) (hV : IsOpen V) :
    IsCompatChart A (ψ.restrOpen V hV) := by
  intro j
  refine ⟨?_, ?_⟩
  · refine (h j).1.mono ?_
    rintro z ⟨hz, hs⟩
    refine ⟨hz, ?_⟩
    have : (A.chart j).symm z ∈ ψ.source ∩ V := by
      simpa [OpenPartialHomeomorph.restrOpen_source] using hs
    exact this.1
  · have hsymm : ((ψ.restrOpen V hV).symm : (Fin e → ℂ) → X) = ψ.symm := rfl
    rw [hsymm]
    refine (h j).2.mono ?_
    rintro z ⟨hz, hs⟩
    refine ⟨?_, hs⟩
    have h1 : ψ.symm z ∈ ψ.source ∩ V := by
      have := (ψ.restrOpen V hV).map_target hz
      rwa [OpenPartialHomeomorph.restrOpen_source] at this
    have h2 : ψ (ψ.symm z) = z := (ψ.restrOpen V hV).right_inv hz
    rw [← h2]
    exact ψ.map_source h1.1

theorem holoOn_comp {e n : ℕ} {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z] (A : FinHolAtlas e X)
    (B : FinHolAtlas n Z) (pr : X → Z) (hp : HoloMap A B pr) (S : Set Z) (g : Z → ℂ) (hg : B.HoloOn S g) :
    A.HoloOn (pr ⁻¹' S) (fun y => g (pr y)) := by
  rintro j z ⟨hzt, hzS⟩
  obtain ⟨k, hk⟩ := B.cover (pr ((A.chart j).symm z))
  have h1 : AnalyticAt ℂ (B.chart k ∘ pr ∘ (A.chart j).symm) z := hp.2 j k z ⟨hzt, hk⟩
  have h2 : AnalyticAt ℂ (g ∘ (B.chart k).symm) ((B.chart k ∘ pr ∘ (A.chart j).symm) z) := by
    refine hg k _ ⟨(B.chart k).map_source hk, ?_⟩
    have : (B.chart k).symm ((B.chart k) (pr ((A.chart j).symm z))) = pr ((A.chart j).symm z) :=
      (B.chart k).left_inv hk
    simpa [this] using hzS
  have h3 := h2.comp h1
  refine h3.congr ?_
  have hc : ContinuousAt (pr ∘ (A.chart j).symm) z :=
    hp.1.continuousAt.comp ((A.chart j).continuousAt_symm hzt)
  filter_upwards [hc.preimage_mem_nhds ((B.chart k).open_source.mem_nhds hk)] with w hw
  have : (B.chart k).symm ((B.chart k) (pr ((A.chart j).symm w))) = pr ((A.chart j).symm w) :=
    (B.chart k).left_inv hw
  simp [this]

theorem snoc_inj {r n e : ℕ} (σb : Fin r → Option (Fin n)) (s : Fin n ↪ Fin e) (i₀ : Fin e)
    (hne : ∀ i, s i ≠ i₀) (hσ : ∀ k k' i, σb k = some i → σb k' = some i → k = k') (k k' : Fin (r + 1)) (i : Fin e)
    (h : (Fin.snoc (α := fun _ => Option (Fin e)) (fun k => (σb k).map s) (some i₀) : Fin (r + 1) → Option (Fin e)) k = some i)
    (h' : (Fin.snoc (α := fun _ => Option (Fin e)) (fun k => (σb k).map s) (some i₀) : Fin (r + 1) → Option (Fin e)) k' = some i) :
    k = k' := by
  induction k using Fin.lastCases with
  | last =>
    induction k' using Fin.lastCases with
    | last => rfl
    | cast l =>
      simp only [Fin.snoc_last, Fin.snoc_castSucc, Option.some.injEq] at h h'
      obtain ⟨b, -, hb⟩ := Option.map_eq_some_iff.1 h'
      exact absurd (hb.trans h.symm) (hne b)
  | cast l =>
    induction k' using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last, Fin.snoc_castSucc, Option.some.injEq] at h h'
      obtain ⟨b, -, hb⟩ := Option.map_eq_some_iff.1 h
      exact absurd (hb.trans h'.symm) (hne b)
    | cast l' =>
      simp only [Fin.snoc_castSucc] at h h'
      obtain ⟨b, hb, hbi⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨b', hb', hbi'⟩ := Option.map_eq_some_iff.1 h'
      have : b = b' := s.injective (hbi.trans hbi'.symm)
      subst this
      rw [hσ l l' b hb hb']

theorem mul_rearrange (A B a b c : ℂ) (h : A = B) : a * A * (b * c) = a * b * (B * c) := by
  subst h
  ring

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (BM : BaseMetric M n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → BM.Rb.X) (hc : Continuous pr) (ψ : RW.X → OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : RW.X → Fin BM.Rb.A.n) (σ : RW.X → Fin n ↪ Fin e) (i₀ : RW.X → Fin e) (V : RW.X → Set RW.X) (u : RW.X → RW.X → ℂ) (hL : ∀ x, IsLocSec M BM.Rb τ a k₀ ca cb RW pr x (ψ x) (kb x) (σ x) (i₀ x) (V x) (u x)), HoloMap RW.A BM.Rb.A pr → ∀ c : ℝ, IsSNC RW.A (BM.L.pullback pr hc + secPot RW (potA M τ a k₀) V (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c) (fun x y => BM.s (pr x) (pr y) * diagSec ψ i₀ u x y) (Fin.snoc BM.m 1) (Fin.snoc (fun k => pr ⁻¹' BM.W k) (diagSet k₀ RW)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e BM τ a k₀ ca cb RW pr hc ψ kb σ i₀ V u hL hp c x
  obtain ⟨⟨F, H, hW⟩, hVo, hxV, hVs, hVU, huh, hu0, hdiag, -⟩ := hL x
  obtain ⟨hcomp, -, hne, hbase, -, -⟩ := hW
  obtain ⟨ψb, hψbc, hxb, hψbU, σb, hσi, hσW, ub, hubh, hub0, hs⟩ := BM.snc (pr x)
  obtain ⟨ψ', hψ'c, hsrc, hk1, hk2⟩ :=
    GlobalTheory.T.compatible_chart_product_projection_twisted e n RW.X BM.Rb.X RW.A BM.Rb.A pr (ψ x) (kb x) (σ x) ψb hcomp hψbc hbase
  have hsrc'' : (ψ'.restrOpen (V x) hVo).source = ψ'.source ∩ V x := ψ'.restrOpen_source (V x) hVo
  have hcoe : ∀ y, (ψ'.restrOpen (V x) hVo) y = ψ' y := fun y => rfl
  have hmem : ∀ y ∈ (ψ'.restrOpen (V x) hVo).source, y ∈ ψ'.source ∧ y ∈ V x ∧ pr y ∈ ψb.source := by
    intro y hy
    rw [hsrc''] at hy
    refine ⟨hy.1, hy.2, ?_⟩
    have := hy.1
    rw [hsrc] at this
    exact this.2
  refine ⟨ψ'.restrOpen (V x) hVo, compat_restr _ _ hψ'c _ hVo, ?_, ?_,
    Fin.snoc (α := fun _ => Option (Fin e)) (fun k => (σb k).map (σ x)) (some (i₀ x)),
    snoc_inj σb (σ x) (i₀ x) hne hσi, ?_, fun y => ub (pr y) * u x y, ?_, ?_, ?_⟩
  · rw [hsrc'', hsrc]
    exact ⟨⟨hVs hxV, hxb⟩, hxV⟩
  · intro y hy
    obtain ⟨-, hyV, hyb⟩ := hmem y hy
    exact ⟨hψbU hyb, hyV⟩
  · intro k
    induction k using Fin.lastCases with
    | last =>
      ext y
      simp only [Fin.snoc_last, Set.mem_inter_iff, Set.mem_setOf_eq, Option.some.injEq, exists_eq_left']
      constructor
      · rintro ⟨hd, hy⟩
        obtain ⟨hy', hyV, -⟩ := hmem y hy
        refine ⟨hy, ?_⟩
        rw [hcoe, hk2 y hy' _ hne]
        exact (hdiag y hyV).2 hd
      · rintro ⟨hy, h0⟩
        obtain ⟨hy', hyV, -⟩ := hmem y hy
        refine ⟨(hdiag y hyV).1 ?_, hy⟩
        rw [hcoe, hk2 y hy' _ hne] at h0
        exact h0
    | cast k =>
      ext y
      simp only [Fin.snoc_castSucc, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage]
      have hWk := Set.ext_iff.1 (hσW k) (pr y)
      constructor
      · rintro ⟨hw, hy⟩
        obtain ⟨hy', -, hyb⟩ := hmem y hy
        obtain ⟨-, i, hi, h0⟩ := hWk.1 ⟨hw, hyb⟩
        refine ⟨hy, σ x i, by rw [hi]; rfl, ?_⟩
        rw [hcoe, hk1 y hy']
        exact h0
      · rintro ⟨hy, i', hi', h0⟩
        obtain ⟨hy', -, hyb⟩ := hmem y hy
        obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.1 hi'
        rw [hcoe, hk1 y hy'] at h0
        exact ⟨(hWk.2 ⟨hyb, i, hi, h0⟩).1, hy⟩
  · intro l z hz
    have h1 := holoOn_comp RW.A BM.Rb.A pr hp ψb.source ub hubh l z ⟨hz.1, (hmem _ hz.2).2.2⟩
    have h2 := huh l z ⟨hz.1, (hmem _ hz.2).2.1⟩
    exact h1.mul h2
  · intro y hy
    obtain ⟨-, hyV, hyb⟩ := hmem y hy
    exact mul_ne_zero (hub0 _ hyb) (hu0 _ hyV)
  · intro y hy
    obtain ⟨hy', hyV, hyb⟩ := hmem y hy
    have hi₀ : ψ' y (i₀ x) = ψ x y (i₀ x) := hk2 y hy' _ hne
    beta_reduce
    rw [Fin.prod_univ_castSucc, hs (pr y) hyb]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, pow_one, hcoe, diagSec, hi₀]
    refine mul_rearrange _ _ _ _ _ (Finset.prod_congr rfl fun k _ => ?_)
    cases h : σb k <;> simp [hk1 y hy']

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.SncProd
