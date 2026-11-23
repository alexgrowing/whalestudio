import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBaseChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentSwapVarietiesArithmeticStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticSecond
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsOrbitChartProjectiveLine
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HoloMapOfLocalProductChartsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagDimensionIndexEquivStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsContinuousOrbitSectionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsBaseChartAtGoodPointStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.OrbitChartTransitionAnalyticStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFromOrbitChartsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartFirstStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartSecondStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartThirdStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartFourthStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartFifthStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartSixthStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartSeventhStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartEighthStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartNinthStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentArithmeticHeightStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
open GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan

theorem sameOrbit_baseOf {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
    {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ} (M : FlagModel y Ψ N j) {k₀ : K}
    {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (baseOf M k₀ z) (baseOf M k₀ z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c (some k.1), fun k => hc _, rfl⟩

theorem sameOrbit_fstPt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {k₀ : K}
    {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (fstPt k₀ z) (fstPt k₀ z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c (some k), fun k => hc _, rfl⟩

theorem sameOrbit_sndPt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {k₀ : K}
    {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (sndPt k₀ z) (sndPt k₀ z') := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => if k = k₀ then c none else c (some k), fun k => ?_, ?_⟩
  · dsimp only
    split_ifs
    exacts [hc _, hc _]
  · funext p
    obtain ⟨k, m⟩ := p
    by_cases e : k = k₀
    · subst e
      simp only [sndPt, Function.comp, v₁_self, if_true]
    · simp only [sndPt, Function.comp, v₁_ne (show (⟨k, m⟩ : Σ k, ι k).1 ≠ k₀ from e), if_neg e]

theorem not_mem_mcPts_top {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (z : (Σ k, ι k) → ℂ) :
    z ∉ mcPts (⊤ : Ideal (MRing ι)) := fun h => by
  have := h.2 1 trivial
  simp at this

theorem fibreSquare_atlas : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → ∃ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (pr : RW.X → Rb.X), IsWAtlas M Rb τ a k₀ ca cb RW pr := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb hb hab hk hca hcb hy hd
  have hA := (GlobalTheory.T.flag_adjacent_swap_varieties_arithmetic K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hab hk hca hcb hy).1
  obtain ⟨ε⟩ := GlobalTheory.T.flag_dimension_index_equiv Ψ N j n d M.j_le hd
  have hcov := GlobalTheory.T.flag_adjacent_arithmetic_height K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb hb hab hk hca hcb hy
  have mk : ∀ (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
      (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
      (h : Ψ → Matrix (Fin N) (Fin N) ℂ), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h →
      ∃ C : OrbitChart (wP M τ a k₀ ca cb) (d + 2), C.D = wD ε V ∧ C.φ = wPhi M F bl h ε k₀ τ ca cb ∧
        C.O = wO M Rb τ a k₀ ca cb F kb V r h := by
    intro F kb V bl r h hc
    have hV : IsOpen V := hc.2.2.2.2.2.2.2.1.1
    have hh := GlobalTheory.T.flag_adjacent_chart_first K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    have hm := GlobalTheory.T.wPhi_mem_mcPts_wP K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    have hr := GlobalTheory.T.flag_adjacent_chart_fourth K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    have ho := GlobalTheory.T.flag_adjacent_chart_fifth K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    have hO := GlobalTheory.T.flag_adjacent_chart_sixth K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h hc
    have hb' := GlobalTheory.T.flag_adjacent_chart_seventh K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    have ht := GlobalTheory.T.flag_adjacent_chart_eighth K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    have hi := GlobalTheory.T.flag_adjacent_chart_ninth K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    exact ⟨{ D := wD ε V
             isOpen_D := hV.preimage (continuous_pi fun i => continuous_apply _)
             φ := wPhi M F bl h ε k₀ τ ca cb
             holo := hh
             mem := hm
             O := wO M Rb τ a k₀ ca cb F kb V r h
             O_open := hO
             O_orbit := fun z hz z' hz' e => (hb' z hz z' hz' e).1
             ρ := wRho M Rb τ k₀ ca cb F kb r h ε
             ρ_cont := ht
             ρ_orbit := fun z hz z' hz' e => (hb' z hz z' hz'.1 e).2
             φ_mem_O := fun w hw => (hr w hw).1
             ρ_φ := fun w hw => (hr w hw).2
             ρ_mem := fun z hz => (ho z hz).1
             φ_ρ := fun z hz => (ho z hz).2
             immersion := hi }, rfl, rfl, rfl⟩
  obtain ⟨R, hR⟩ := GlobalTheory.T.log_resolution_from_orbit_charts (Option K) (fun o => ι (o.getD k₀)) (wP M τ a k₀ ca cb) (d + 2) hA.1 hA.2.1.2.1
    (fun h => hA.2.1.1.ne_top (top_le_iff.mp h)) (fun z hz => by
      obtain ⟨F, kb, V, bl, r, h, hc, hzO⟩ := hcov z hz
      obtain ⟨C, -, -, hO⟩ := mk F kb V bl r h hc
      exact ⟨C, hO ▸ hzO⟩)

  have key : ∀ x : R.X, ∃ (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
      (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
      (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ψ : OpenPartialHomeomorph R.X (Fin (d + 2) → ℂ)),
      IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h ∧ IsCompatChart R.A ψ ∧ ψ.target = wD ε V ∧ x ∈ ψ.source ∧
        ∀ x' ∈ ψ.source, SameOrbit (wPhi M F bl h ε k₀ τ ca cb (ψ x')) (R.lift x' x') := by
    intro x
    obtain ⟨F, kb, V, bl, r, h, hc, hzO⟩ := hcov _ (R.mem x x (R.mem_U x))
    obtain ⟨C, hD, hφ, hO⟩ := mk F kb V bl r h hc
    obtain ⟨ψ, h1, h2, h3, h4⟩ := hR C ⟨_, R.mem x x (R.mem_U x)⟩
    exact ⟨F, kb, V, bl, r, h, ψ, hc, h1, h2.trans hD, (h3 x).2 (hO ▸ hzO), fun x' hx' => hφ ▸ h4 x' hx'⟩

  have hbase : ∀ x : R.X, ∃ x' : Rb.X, SameOrbit (Rb.lift x' x') (baseOf M k₀ (R.lift x x)) := by
    intro x
    obtain ⟨F, kb, V, bl, r, h, ψ, hc, -, hT, hx, hs⟩ := key x
    have hB := hc.2.2.2.2.2.2.2.1
    have hw : ψ x ∈ wD ε V := hT ▸ ψ.map_source hx
    have hE := (GlobalTheory.T.flag_adjacent_chart_second K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc).2 _ hw
    refine ⟨(Rb.A.chart kb).symm (wB ε (ψ x)), orbit_trans (hB.2.2.2.2 _ hw).2.2.2 ?_⟩
    have := sameOrbit_baseOf M (hs x hx)
    rwa [hE.2.1] at this
  choose pr hpr using hbase
  have hcoord : ∀ (x : R.X) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
      (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
      (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ψ : OpenPartialHomeomorph R.X (Fin (d + 2) → ℂ)),
      IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ψ.target = wD ε V → x ∈ ψ.source →
      SameOrbit (wPhi M F bl h ε k₀ τ ca cb (ψ x)) (R.lift x x) →
      pr x ∈ (Rb.A.chart kb).source ∧ ∀ i, Rb.A.chart kb (pr x) i = ψ x (ε (Sum.inl i)) := by
    intro x F kb V bl r h ψ hc hT hx hs
    have hB := hc.2.2.2.2.2.2.2.1
    have hw : ψ x ∈ wD ε V := hT ▸ ψ.map_source hx
    have hE := (GlobalTheory.T.flag_adjacent_chart_second K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc).2 _ hw
    have h1 : SameOrbit (bl (wB ε (ψ x))) (baseOf M k₀ (R.lift x x)) := by
      have := sameOrbit_baseOf M hs
      rwa [hE.2.1] at this
    have h2 := orbit_trans (hB.2.2.2.2 _ hw).2.2.2 (orbit_trans h1 (orbit_symm (hpr x)))
    have h3 : (Rb.A.chart kb).symm (wB ε (ψ x)) = pr x := Rb.inj _ _ (not_mem_mcPts_top _) h2
    have hwt : wB ε (ψ x) ∈ (Rb.A.chart kb).target := hB.2.1 hw
    rw [← h3]
    exact ⟨(Rb.A.chart kb).map_target hwt, fun i => by
      rw [(Rb.A.chart kb).right_inv hwt]
      rfl⟩
  refine ⟨R, pr, ?_, hpr, fun x => ?_⟩
  · refine GlobalTheory.T.holoMap_of_local_product_charts (d + 2) n R.X Rb.X R.A Rb.A pr fun x => ?_
    obtain ⟨F, kb, V, bl, r, h, ψ, hc, hC, hT, hx, hs⟩ := key x
    exact ⟨ψ, kb, fun i => ε (Sum.inl i), hC, hx, fun x' hx' => hcoord x' F kb V bl r h ψ hc hT hx' (hs x' hx')⟩
  · obtain ⟨F, kb, V, bl, r, h, ψ, hc, hC, hT, hx, hs⟩ := key x
    have hE := GlobalTheory.T.flag_adjacent_chart_second K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    have hB := hc.2.2.2.2.2.2.2.1
    refine ⟨ψ, kb, ⟨fun i => ε (Sum.inl i), fun i i' e => Sum.inl_injective (ε.injective e)⟩, ε (Sum.inr (Sum.inr ())), F,
      fun τ' => wH h ε τ', hx, hC, hc.2.2.2.2.2.2.1, fun i e => Sum.inl_ne_inr (ε.injective e), fun x' hx' =>
        hcoord x' F kb V bl r h ψ hc hT hx' (hs x' hx'), fun τ' r' s' => hT ▸ hE.1 τ' r' s', fun x' hx' => ?_⟩
    have hw : ψ x' ∈ wD ε V := hT ▸ ψ.map_source hx'
    obtain ⟨e1, e2, e3⟩ := hE.2 _ hw
    have h1 := sameOrbit_baseOf M (hs x' hx')
    rw [e2] at h1
    refine ⟨e1, ?_, fstPt k₀ (wPhi M F bl h ε k₀ τ ca cb (ψ x')), sndPt k₀ (wPhi M F bl h ε k₀ τ ca cb (ψ x')),
      sameOrbit_fstPt (hs x' hx'), sameOrbit_sndPt (hs x' hx'), e3⟩
    have h2 : mCoordIdeal (bl (wB ε (ψ x'))) = mCoordIdeal (basePart M.blk (fstPt k₀ (R.lift x' x'))) :=
      GlobalTheory.CompanionTheory.Ar.PB.CovMap.mCoordIdeal_eq_of_sameOrbit h1
    exact h2 ▸ (hB.2.2.2.2 _ hw).2.2.1

end GlobalTheory.CompanionTheory.Ar.PB.WMan
