import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsLocSec
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsValueAtOfTorus
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedAtlasCompatibility
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedMetricLogFormulaStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicFrameMetricNearPointStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwoFramesOrbitStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolutionAltBis
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolutionStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.LocGen

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem holoOn_mul_prod_zpow {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {U : Set X} {κ : Type}
    [Fintype κ] {f : X → ℂ} {c : κ → X → ℂ} (d : κ → ℤ) (hf : A.HoloOn U f) (hc : ∀ k, A.HoloOn U (c k))
    (h0 : ∀ k, ∀ y ∈ U, c k y ≠ 0) : A.HoloOn U fun y => f y * ∏ k, c k y ^ d k := by
  intro j z hz
  have h1 : AnalyticAt ℂ (fun v => ∏ k, ((c k ∘ (A.chart j).symm) v) ^ d k) z :=
    Finset.analyticAt_fun_prod _ fun k _ => (hc k j z hz).zpow (h0 k _ hz.2)
  exact (hf j z hz).mul h1

theorem holoOn_comp_chart {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} (hψ : IsCompatChart A ψ) {g : (Fin e → ℂ) → ℂ}
    (hg : AnalyticOnNhd ℂ g ψ.target) {V : Set X} (hV : V ⊆ ψ.source) : A.HoloOn V fun w => g (ψ w) := by
  intro j z hz
  have hs : (A.chart j).symm z ∈ ψ.source := hV hz.2
  have h1 : AnalyticAt ℂ (g ∘ (ψ ∘ (A.chart j).symm)) z :=
    AnalyticAt.comp (g := g) (f := ψ ∘ (A.chart j).symm) (hg _ (ψ.map_source hs)) ((hψ j).1 z ⟨hz.1, hs⟩)
  exact h1

def mixPt (k₀ : K) (z₀ z₁ : (Σ k, ι k) → ℂ) : (Σ o : Option K, ι (o.getD k₀)) → ℂ := fun p =>
  match p with
  | ⟨some k, m⟩ => z₀ ⟨k, m⟩
  | ⟨none, m⟩ => z₁ ⟨k₀, m⟩

theorem fstPt_mixPt (k₀ : K) (z₀ z₁ : (Σ k, ι k) → ℂ) : fstPt k₀ (mixPt k₀ z₀ z₁) = z₀ := by
  funext q
  obtain ⟨k, m⟩ := q
  rfl

theorem sndPt_mixPt {k₀ : K} {z₀ z₁ : (Σ k, ι k) → ℂ} (h : ∀ q : Σ k, ι k, q.1 ≠ k₀ → z₁ q = z₀ q) :
    sndPt k₀ (mixPt k₀ z₀ z₁) = z₁ := by
  funext q
  obtain ⟨k, m⟩ := q
  by_cases e : k = k₀
  · subst e
    change mixPt k z₀ z₁ (v₁ k ⟨k, m⟩) = _
    rw [v₁_self]
    rfl
  · change mixPt k₀ z₀ z₁ (v₁ k₀ ⟨k, m⟩) = _
    rw [v₁_ne (p := ⟨k, m⟩) e]
    exact (h ⟨k, m⟩ e).symm

theorem mixPt_blocks {k₀ : K} {z₀ z₁ : (Σ k, ι k) → ℂ} (h₀ : ∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0)
    (h₁ : ∀ k, ∃ i, z₁ ⟨k, i⟩ ≠ 0) : ∀ o, ∃ i, mixPt k₀ z₀ z₁ ⟨o, i⟩ ≠ 0 := by
  intro o
  cases o with
  | none => exact h₁ k₀
  | some k => exact h₀ k

theorem log_norm_sub {k₀ : K} (A : HermLine fun o : Option K => ι (o.getD k₀)) {c : Option K → ℂ}
    (hc : ∀ o, c o ≠ 0) {z zz : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (hz : z = fun p => c p.1 * zz p)
    (hzz : ∀ o, ∃ i, zz ⟨o, i⟩ ≠ 0) {f t : ℂ} (hf : f ≠ 0) (ht : t ≠ 0) :
    Real.log ‖f * (∏ o, c o ^ A.a o) * t‖ - Real.log (A.h z) = Real.log ‖t * f‖ - Real.log (A.h zz) := by
  have hC : (∏ o, ‖c o‖ ^ A.a o) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun o _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc o))
  have hP : ‖∏ o, c o ^ A.a o‖ = ∏ o, ‖c o‖ ^ A.a o := by
    rw [norm_prod]
    exact Finset.prod_congr rfl fun o _ => norm_zpow _ _
  have hN : ‖f * (∏ o, c o ^ A.a o) * t‖ = (∏ o, ‖c o‖ ^ A.a o) * ‖t * f‖ := by
    rw [norm_mul, norm_mul, norm_mul, hP]
    ring
  have hA : A.h z = (∏ o, ‖c o‖ ^ A.a o) * A.h zz := by
    rw [hz]
    exact A.smul c zz hc
  have hp : A.h zz ≠ 0 := (A.pos zz hzz).ne'
  have hn : ‖t * f‖ ≠ 0 := norm_ne_zero_iff.2 (mul_ne_zero ht hf)
  rw [hN, hA, Real.log_mul hC hn, Real.log_mul hC hp]
  ring

theorem goodAt_of_orbit {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ} (M : FlagModel y Ψ N j)
    {F : FrameData ι Ψ N M.Ω M.blk} {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z')
    (hG : M.GoodAt F (mCoordIdeal (basePart M.blk z'))) : M.GoodAt F (mCoordIdeal (basePart M.blk z)) := by
  obtain ⟨c, hc0, hzc⟩ := h
  have e₀ : basePart M.blk z = fun q : Σ k, baseIdx ι M.blk k =>
      (fun k : NonPluckerBlocks M.blk => c k.1) q.1 * basePart M.blk z' q := by
    rw [hzc]; rfl
  rw [e₀, GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.mCoordIdeal_torus (K := NonPluckerBlocks M.blk) (ι := baseIdx ι M.blk)
    (fun k : NonPluckerBlocks M.blk => c k.1) (fun k => hc0 k.1) (basePart M.blk z')]
  exact hG

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X), IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ x, ∃ ψ kb σ i₀ V u, IsLocSec M Rb τ a k₀ ca cb RW pr x ψ kb σ i₀ V u := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a b k₀ ca cb hb hj hk hca hcb RW pr hW x
  obtain ⟨ψ, kb, σ, i₀, F, H, hx, hC⟩ := hW.2.2 x
  obtain ⟨V, z₀, z₁, c, hVo, hxV, hVs, hVU, hz₀h, hch, hc0, hL⟩ :=
    GlobalTheory.T.flag_adjacent_twisted_resolution_alt K ι Φ y Ψ N j M n e Rb τ a b k₀ ca cb hb hj hk hca hcb RW pr hW x ψ kb σ i₀ F H hx hC
  have hFr : M.IsFrame F := hC.2.1
  have hsrc := hC.2.2.2.2.2
  have hfacts : ∀ w ∈ V, basePart M.blk (z₀ w) ∈ mcPts (mCoordIdeal M.x) ∧ (∀ k, ∃ i, z₀ w ⟨k, i⟩ ≠ 0) ∧
      (∀ k, ∃ i, z₁ w ⟨k, i⟩ ≠ 0) ∧ basePart M.blk (z₁ w) = basePart M.blk (z₀ w) ∧
      M.GoodAt F (mCoordIdeal (basePart M.blk (z₀ w))) := by
    intro w hw
    obtain ⟨ho₀, ho₁, -, hoff, -, -⟩ := hL w hw
    obtain ⟨h1, -, h3, h4⟩ := PtBase.main K ι Φ y Ψ N j M n e Rb τ a k₀ ca cb RW pr hk hW w (z₀ w) (z₁ w) ho₀ ho₁
    refine ⟨h1, h3, h4, ?_, goodAt_of_orbit M ho₀ (hsrc w (hVs hw)).2.1⟩
    funext q
    exact hoff ⟨q.1.1, q.2⟩ fun e' => q.1.2 (τ, a) (hk.trans (congrArg some (Eq.symm e')))
  have hdata : ∀ w ∈ V, ψ w i₀ ≠ 0 → IsPtData M τ a k₀ ca cb RW w (z₀ w) (z₁ w) F (H τ (ψ w)) (ψ w i₀) := by
    intro w hw h0
    obtain ⟨ho₀, ho₁, hex, -⟩ := hL w hw
    have hH := (hsrc w (hVs hw)).1 τ
    exact ⟨hFr, (hfacts w hw).2.2.2.2, ho₀, ho₁, hH.1, hH.2, h0, fun i => (hex τ i).1, fun i => by
      simpa using (hex τ i).2⟩
  obtain ⟨V', hV'o, hxV', hV'V, hfh, hf0⟩ := GlobalTheory.T.holomorphic_frame_metric_near_point K ι Φ y Ψ N j M e RW.X RW.A V x
    (fun w => basePart M.blk (z₀ w)) (fun w => H τ (ψ w)) F τ a hVo hxV (fun q => hz₀h ⟨q.1.1, q.2⟩)
    (fun w hw => (hfacts w hw).1) (fun w hw => (hfacts w hw).2.2.2.2)
    (fun r s => holoOn_comp_chart RW.A hC.1 (hC.2.2.2.2.1 τ r s) hVs) (fun w hw => (hsrc w (hVs hw)).1 τ)
  obtain ⟨f, hfh, hf0, hfd⟩ : ∃ f : RW.X → ℂ, RW.A.HoloOn V' f ∧ (∀ w ∈ V', f w ≠ 0) ∧ ∀ w, f w =
      ∏ i : Fin N, (if IsProperStep N j i then 1 else valAt M.x (F.υ (τ, i)) (basePart M.blk (z₀ w)) *
        (if (i : ℕ) + 1 = j then (if (a : ℕ) < j then minorIJ (H τ (ψ w)) (wIdx N j) (wIdx N j) else 1)
          else minorIJ (H τ (ψ w)) (omIdx N j) (omIdx N j))) ^ xiCoef τ a (τ, i) :=
    ⟨_, hfh, hf0, fun _ => rfl⟩
  refine ⟨ψ, kb, σ, i₀, V', fun w => f w * ∏ o, c o w ^ aDeg M τ a k₀ o, ⟨F, H, hC⟩, hV'o, hxV',
    hV'V.trans hVs, hV'V.trans hVU, ?_, ?_, ?_, ?_⟩
  · exact holoOn_mul_prod_zpow RW.A _ hfh (fun o j' => (hch o j').mono
      (Set.inter_subset_inter_right _ (Set.preimage_mono hV'V))) fun o w hw => hc0 o w (hV'V hw)
  · intro w hw
    exact mul_ne_zero (hf0 w hw) (Finset.prod_ne_zero_iff.2 fun o _ => zpow_ne_zero _ (hc0 o w (hV'V hw)))
  · intro w hw
    have hwV := hV'V hw
    constructor
    · intro h0
      obtain ⟨ho₀, ho₁, hex, hoff, -, -⟩ := hL w hwV
      have hbase := (hfacts w hwV).2.2.2.1
      have hz : z₁ w = z₀ w := by
        funext q
        obtain ⟨k, m⟩ := q
        by_cases e' : k = k₀
        · subst e'
          have h1 := (hex τ a).1.2 k hk m
          have h2 := (hex τ a).2.2 k hk m
          rw [if_pos rfl, h0, Matrix.single_zero, add_zero, mul_one, hbase] at h2
          exact h2.trans h1.symm
        · exact hoff ⟨k, m⟩ e'
      rw [hz] at ho₁
      exact orbit_trans (orbit_symm ho₀) ho₁
    · intro hs
      by_contra h0
      exact GlobalTheory.T.flag_adjacent_twisted_resolution K ι Φ y Ψ N j M n e Rb τ a b k₀ ca cb hb hj hk hca hcb RW pr hW w _ _ _ _ _
        (hdata w hwV h0) hs
  · intro w hw h0 z₀' z₁' F' h' t' hD
    have hwV := hV'V hw
    obtain ⟨ho₀, ho₁, -, hoff, hl0, hl1⟩ := hL w hwV
    obtain ⟨hmc, hn₀, hn₁, hbase, hG⟩ := hfacts w hwV
    obtain ⟨hF', hG', hp₀, hp₁, hB', hd', ht', he₀', he₁'⟩ := hD
    have hd := hdata w hwV h0
    have hind := GlobalTheory.T.flag_adjacent_two_frames_orbit K ι Φ y Ψ N j M τ a b k₀ ca cb hb hj hk hca hcb F F' (z₀ w) (z₁ w) z₀' z₁'
      (H τ (ψ w)) h' (ψ w i₀) t' hmc hn₀ hn₁ hbase hFr hF' hG hG' (orbit_trans ho₀ (orbit_symm hp₀))
      (orbit_trans ho₁ (orbit_symm hp₁)) hd.2.2.2.2.1 hd.2.2.2.2.2.1 hB' hd' h0 ht' hd.2.2.2.2.2.2.2.1
      hd.2.2.2.2.2.2.2.2 he₀' he₁'
    rw [← hind]
    have hlift : RW.lift x w = fun p => c p.1 w * mixPt k₀ (z₀ w) (z₁ w) p := by
      funext p
      obtain ⟨o, m⟩ := p
      cases o with
      | none => exact hl1 m
      | some k => exact hl0 ⟨k, m⟩
    have hzz := mixPt_blocks (k₀ := k₀) hn₀ hn₁
    have hnorm := log_norm_sub (potA M τ a k₀) (c := fun o => c o w) (fun o => hc0 o w hwV) hlift hzz
      (hf0 w hw) h0
    have hcombo := GlobalTheory.T.twisted_metric_log_formula K ι Φ y Ψ N j M τ a k₀ hk _ hzz
    rw [fstPt_mixPt, sndPt_mixPt hoff] at hcombo
    have e₁ : Real.log ‖(f w * ∏ o, c o w ^ aDeg M τ a k₀ o) * ψ w i₀‖ -
        Real.log ((potA M τ a k₀).h (RW.lift x w)) = _ := hnorm
    refine e₁.trans ?_
    rw [hcombo, normRhs, ← hfd w]
    ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.LocGen
