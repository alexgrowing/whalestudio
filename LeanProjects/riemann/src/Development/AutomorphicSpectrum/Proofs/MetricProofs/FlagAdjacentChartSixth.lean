import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBaseChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentSwapVarietiesArithmeticStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticSecond
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Opn

section Values

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem continuousWithinAt_valAt {x : (Σ k, ι k) → Ω} {b₀ : (Σ k, ι k) → ℂ} (hb : b₀ ∈ mcPts (mCoordIdeal x)) {s : Ω}
    (hs : RegAt x (mCoordIdeal b₀) s) : ContinuousWithinAt (valAt x s) (mcPts (mCoordIdeal x)) b₀ := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  have hx := ValRing.aeval_ne_zero_of_notMem hb hh hn
  have h0 := ValRing.eval_ne_zero_of_notMem hh hn
  have cg : Continuous fun b : (Σ k, ι k) → ℂ => eval b (map (Int.castRingHom ℂ) g) :=
    MvPolynomial.continuous_eval _
  have ch : Continuous fun b : (Σ k, ι k) → ℂ => eval b (map (Int.castRingHom ℂ) h) :=
    MvPolynomial.continuous_eval _
  have hne : ∀ᶠ b in 𝓝 b₀, eval b (map (Int.castRingHom ℂ) h) ≠ 0 := ch.continuousAt.eventually_ne h0
  have key : valAt x s =ᶠ[𝓝[mcPts (mCoordIdeal x)] b₀]
      fun b => eval b (map (Int.castRingHom ℂ) g) / eval b (map (Int.castRingHom ℂ) h) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hne] with b hbm hbn
    exact valAt_eq hbm ⟨d, g, h, hg, hh, hx, heq, hbn, rfl⟩
  have hq : ContinuousWithinAt
      (fun b : (Σ k, ι k) → ℂ => eval b (map (Int.castRingHom ℂ) g) / eval b (map (Int.castRingHom ℂ) h))
      (mcPts (mCoordIdeal x)) b₀ := (cg.continuousAt.div ch.continuousAt h0).continuousWithinAt
  exact hq.congr_of_eventuallyEq key (key.self_of_nhdsWithin hb)

end Values

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem continuousWithinAt_twMinor (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {Z : Type}
    [TopologicalSpace Z] {A : Set Z} {z₀ : Z} {bs : Z → (Σ k, baseIdx ι M.blk k) → ℂ} {pt : Z → (Σ k, ι k) → ℂ}
    (hbs : Continuous bs) (hpt : Continuous pt) (hA : Set.MapsTo bs A (mcPts (mCoordIdeal M.x))) (hz₀ : z₀ ∈ A)
    (hG : M.GoodAt F (mCoordIdeal (bs z₀))) (i : Fin N) (k : K) (g : Matrix (Fin N) (Fin N) ℂ)
    (J : Finset (Fin N)) : ContinuousWithinAt (fun z => twMinor M F (bs z) i k g (pt z) J) A z₀ := by
  unfold twMinor pluck
  refine tendsto_finsetSum _ fun I _ => Tendsto.const_mul _ (tendsto_finsetSum _ fun m _ => Tendsto.mul ?_ ?_)
  · exact (continuousWithinAt_valAt (hA hz₀) (hG.2.1 _ _).2).comp hbs.continuousWithinAt hA
  · exact ((continuous_apply _).comp hpt).continuousWithinAt

theorem isBlockMap_v₀ (k₀ : K) : IsBlockMap (some : K → Option K) (v₀ (ι := ι) k₀) := by
  refine ⟨Option.some_injective _, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨k, m⟩ ⟨k', m'⟩ e
    simp only [v₀] at e
    obtain ⟨e1, e2⟩ := Sigma.mk.inj_iff.1 e
    obtain rfl := Option.some_injective _ e1
    rw [eq_of_heq e2]
  · rintro ⟨_, m⟩ ⟨k, rfl⟩
    exact ⟨⟨k, m⟩, rfl⟩

theorem continuous_fstPt (k₀ : K) : Continuous (fstPt (ι := ι) k₀) :=
  continuous_pi fun p => continuous_apply (v₀ k₀ p)

theorem continuous_sndPt (k₀ : K) : Continuous (sndPt (ι := ι) k₀) :=
  continuous_pi fun p => continuous_apply (v₁ k₀ p)

theorem continuous_baseOf (M : FlagModel y Ψ N j) (k₀ : K) : Continuous (baseOf M k₀) :=
  continuous_pi fun q => continuous_apply (v₀ k₀ ⟨q.1.1, q.2⟩)

theorem fstPt_mem (M : FlagModel y Ψ N j) {d : ℕ} {τ : Ψ} {a b : Fin N} {k₀ : K} {ca cb : Fin N}
    (hb : (b : ℕ) = a + 1) (hba : (b : ℕ) < j ∨ j ≤ (a : ℕ)) (hk : M.blk (τ, a) = some k₀)
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) (hV : IsArithVar (mCoordIdeal y) (d + 2))
    {z : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (hz : z ∈ mcPts (wP M τ a k₀ ca cb)) :
    fstPt k₀ z ∈ mcPts (mCoordIdeal y) := by
  have hI := (GlobalTheory.T.flag_adjacent_swap_varieties_arithmetic K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hba hk hca hcb hV).2.2.2.1
  exact GlobalTheory.CompanionTheory.Ar.Chg.mem_mcPts_restr (isBlockMap_v₀ k₀) hI.ge hz

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∃ O' : Set ((Σ o : Option K, ι (o.getD k₀)) → ℂ), IsOpen O' ∧ wO M Rb τ a k₀ ca cb F kb V r h = O' ∩ mcPts (wP M τ a k₀ ca cb) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h hc
  obtain ⟨hb, hba, hk₀, hca, hcb, hAV, -, hBC, hr, hrc, -⟩ := hc
  have hmaps : Set.MapsTo (baseOf M k₀) (mcPts (wP M τ a k₀ ca cb)) (mcPts (mCoordIdeal M.x)) := fun z hz =>
    CPts.base_mem M (fstPt_mem M hb hba hk₀ hca hcb hAV hz)
  have key : ∀ z₀ ∈ wO M Rb τ a k₀ ca cb F kb V r h,
      wO M Rb τ a k₀ ca cb F kb V r h ∈ 𝓝[mcPts (wP M τ a k₀ ca cb)] z₀ := by
    rintro z₀ ⟨hz₀, hsrc, hV₀, hm₁, hm₂⟩
    have hbm := hmaps hz₀
    have hG : M.GoodAt F (mCoordIdeal (baseOf M k₀ z₀)) := by
      obtain ⟨-, -, hgood, horb⟩ := hBC.2.2.2.2 _ hV₀
      rw [(Rb.A.chart kb).left_inv hsrc] at horb
      rwa [CovMap.mCoordIdeal_eq_of_sameOrbit (orbit_trans (orbit_symm (hr _ hbm)) horb)]
    have hrb : ContinuousWithinAt (fun z => r (baseOf M k₀ z)) (mcPts (wP M τ a k₀ ca cb)) z₀ :=
      (hrc _ hbm).comp (continuous_baseOf M k₀).continuousWithinAt hmaps
    have e₁ := hrb.tendsto.eventually_mem ((Rb.A.chart kb).open_source.mem_nhds hsrc)
    have e₂ := (((Rb.A.chart kb).continuousAt hsrc).tendsto.comp hrb.tendsto).eventually_mem (hBC.1.mem_nhds hV₀)
    have tw := fun (pt : _ → (Σ k, ι k) → ℂ) (hpt : Continuous pt) =>
      continuousWithinAt_twMinor M F (continuous_baseOf M k₀) hpt hmaps hz₀ hG
    have e₃ : ∀ᶠ z in 𝓝[mcPts (wP M τ a k₀ ca cb)] z₀, ∀ p k, M.blk p = some k →
        twMinor M F (baseOf M k₀ z) p.2 k (h p.1)⁻¹ (fstPt k₀ z) (stepCols N j p.2) ≠ 0 := by
      refine eventually_all.2 fun p => eventually_all.2 fun k => ?_
      by_cases hp : M.blk p = some k
      · exact ((tw _ (continuous_fstPt k₀) p.2 k (h p.1)⁻¹ (stepCols N j p.2)).tendsto.eventually_ne
          (hm₁ p k hp)).mono fun _ hz _ => hz
      · exact Eventually.of_forall fun _ hp' => absurd hp' hp
    have e₄ := (tw _ (continuous_sndPt k₀) a k₀ (h τ)⁻¹ (stepCols N j a)).tendsto.eventually_ne hm₂
    filter_upwards [self_mem_nhdsWithin, e₁, e₂, e₃, e₄] with z h₀ h₁ h₂ h₃ h₄
    exact ⟨h₀, h₁, h₂, h₃, h₄⟩
  choose! U hU hmem hsub using fun z₀ (hz : z₀ ∈ wO M Rb τ a k₀ ca cb F kb V r h) =>
    mem_nhdsWithin.1 (key z₀ hz)
  refine ⟨⋃ z₀ ∈ wO M Rb τ a k₀ ca cb F kb V r h, U z₀, isOpen_biUnion hU, Set.Subset.antisymm ?_ ?_⟩
  · intro z hz
    exact ⟨Set.mem_biUnion hz (hmem z hz), hz.1⟩
  · rintro z ⟨hz, hzA⟩
    obtain ⟨z₀, h₀, hz₀⟩ := Set.mem_iUnion₂.1 hz
    exact hsub z₀ h₀ ⟨hz₀, hzA⟩

end Flag

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Opn
