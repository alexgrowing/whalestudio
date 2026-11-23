import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBaseChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticSecond
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan

theorem continuousWithinAt_valAt_of_regAt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
    [Field Ω] {x : (Σ k, ι k) → Ω} {zb : (Σ k, ι k) → ℂ} (hz : zb ∈ mcPts (mCoordIdeal x)) {s : Ω}
    (hs : RegAt x (mCoordIdeal zb) s) : ContinuousWithinAt (valAt x s) (mcPts (mCoordIdeal x)) zb := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  have hy := GlobalTheory.CompanionTheory.Ar.PB.ValRing.aeval_ne_zero_of_notMem hz hh hn
  have h0 := GlobalTheory.CompanionTheory.Ar.PB.ValRing.eval_ne_zero_of_notMem hh hn
  have cg : Continuous fun w : (Σ k, ι k) → ℂ => eval w (map (Int.castRingHom ℂ) g) :=
    MvPolynomial.continuous_eval _
  have ch : Continuous fun w : (Σ k, ι k) → ℂ => eval w (map (Int.castRingHom ℂ) h) :=
    MvPolynomial.continuous_eval _
  have hnear : valAt x s =ᶠ[𝓝[mcPts (mCoordIdeal x)] zb]
      fun w => eval w (map (Int.castRingHom ℂ) g) / eval w (map (Int.castRingHom ℂ) h) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ch.continuousAt.eventually_ne h0)] with w hw hw0
    exact valAt_eq hw ⟨d, g, h, hg, hh, hy, heq, hw0, rfl⟩
  have hat : valAt x s zb = eval zb (map (Int.castRingHom ℂ) g) / eval zb (map (Int.castRingHom ℂ) h) :=
    valAt_eq hz ⟨d, g, h, hg, hh, hy, heq, h0, rfl⟩
  exact (cg.continuousAt.div ch.continuousAt h0).continuousWithinAt.congr_of_eventuallyEq hnear hat

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem twMinor_continuousWithinAt (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {Z : Type}
    [TopologicalSpace Z] {S : Set Z} {z₀ : Z} {β : Z → (Σ k, baseIdx ι M.blk k) → ℂ} {P : Z → (Σ k, ι k) → ℂ}
    (hβ : ContinuousWithinAt β S z₀) (hS : Set.MapsTo β S (mcPts (mCoordIdeal M.x)))
    (hz : β z₀ ∈ mcPts (mCoordIdeal M.x)) (hG : M.GoodAt F (mCoordIdeal (β z₀)))
    (hP : ContinuousWithinAt P S z₀) (i : Fin N) (k : K) (g : Matrix (Fin N) (Fin N) ℂ) (J : Finset (Fin N)) :
    ContinuousWithinAt (fun z => twMinor M F (β z) i k g (P z) J) S z₀ := by
  simp only [twMinor, pluck]
  refine tendsto_finset_sum _ fun I _ => Tendsto.const_mul _ (tendsto_finset_sum _ fun m _ => Tendsto.mul ?_ ?_)
  · exact ContinuousWithinAt.comp (g := valAt M.x (F.u' I ⟨k, m⟩))
      (continuousWithinAt_valAt_of_regAt hz (hG.2.1 _ _).2) hβ hS
  · exact ((continuous_apply (⟨k, m⟩ : Σ k, ι k)).continuousAt.comp_continuousWithinAt hP)

theorem wRho_continuousOn : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ContinuousOn (wRho M Rb τ k₀ ca cb F kb r h ε) (wO M Rb τ a k₀ ca cb F kb V r h) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε H
  obtain ⟨hb, hab, hk, hca, hcb, hy, hF, hB, horb, hr, hh⟩ := H
  obtain ⟨hVo, hVt, -, -, hbl⟩ := hB
  have hbase : Set.MapsTo (baseOf M k₀) (wO M Rb τ a k₀ ca cb F kb V r h) (mcPts (mCoordIdeal M.x)) := fun z hz =>
    GlobalTheory.CompanionTheory.Ar.PB.CPts.base_mem M (GlobalTheory.CompanionTheory.Ar.PB.CPts.comp_mem_mcPts (GlobalTheory.CompanionTheory.Ar.PB.WSq.Pts.isBlockMap_v₀ k₀)
      (algebraMap Φ (RatFunc Φ)) (funext fun _ => rfl) hz.1)
  have cB : Continuous (baseOf M k₀) := continuous_pi fun q => continuous_apply _
  have cF : Continuous (fstPt (ι := ι) k₀) := continuous_pi fun q => continuous_apply _
  have cS : Continuous (sndPt (ι := ι) k₀) := continuous_pi fun q => continuous_apply _
  have hgood : ∀ z ∈ wO M Rb τ a k₀ ca cb F kb V r h, M.GoodAt F (mCoordIdeal (baseOf M k₀ z)) := by
    intro z hz
    have h3 := (hbl _ hz.2.2.1).2.2
    rw [(Rb.A.chart kb).left_inv hz.2.1] at h3
    have e := orbit_trans (orbit_symm (horb _ (hbase hz))) h3.2
    rw [GlobalTheory.CompanionTheory.Ar.PB.CovMap.mCoordIdeal_eq_of_sameOrbit e]
    exact h3.1
  have cLow : ∀ (P : ((Σ o : Option K, ι (o.getD k₀)) → ℂ) → (Σ k, ι k) → ℂ), Continuous P → ∀ (τ' : Ψ) (a' b' : Fin N),
      ∀ z ∈ wO M Rb τ a k₀ ca cb F kb V r h, (∀ k, M.blk (τ', stepOf N j b') = some k →
        twMinor M F (baseOf M k₀ z) (stepOf N j b') k (h τ')⁻¹ (P z) (stepCols N j (stepOf N j b')) ≠ 0) →
      ContinuousWithinAt (fun z => lowRead M F (baseOf M k₀ z) h (P z) τ' a' b')
        (wO M Rb τ a k₀ ca cb F kb V r h) z := by
    intro P hP τ' a' b' z hz hne
    have cT := fun (k : K) (J : Finset (Fin N)) => twMinor_continuousWithinAt M F cB.continuousWithinAt hbase (hbase hz)
      (hgood z hz) hP.continuousWithinAt (stepOf N j b') k (h τ')⁻¹ J
    cases e : M.blk (τ', stepOf N j b') with
    | none =>
      simp only [lowRead, e, Option.elim_none]
      exact continuousWithinAt_const
    | some k =>
      simp only [lowRead, e, Option.elim_some]
      exact (cT k _).div (cT k _) (hne k e)
  have hst : stepOf N j ca = a := by
    apply Fin.ext
    have h1 := a.2
    have h2 := ca.2
    have h3 := M.j_le
    simp only [stepOf, lastCol] at hca ⊢
    split_ifs at hca ⊢ <;> omega
  intro z hz
  have hz₄ : ∀ p k, M.blk p = some k →
      twMinor M F (baseOf M k₀ z) p.2 k (h p.1)⁻¹ (fstPt k₀ z) (stepCols N j p.2) ≠ 0 := hz.2.2.2.1
  have hz₅ : twMinor M F (baseOf M k₀ z) a k₀ (h τ)⁻¹ (sndPt k₀ z) (stepCols N j a) ≠ 0 := hz.2.2.2.2
  refine continuousWithinAt_pi.2 fun i => ?_
  rcases e : ε.symm i with l | q | u
  · simp only [wRho, e]
    have c2 : ContinuousWithinAt (r ∘ baseOf M k₀) (wO M Rb τ a k₀ ca cb F kb V r h) z :=
      ContinuousWithinAt.comp (hr _ (hbase hz)) cB.continuousWithinAt hbase
    have c3 : ContinuousAt (fun x => Rb.A.chart kb x l) ((r ∘ baseOf M k₀) z) :=
      (continuous_apply l).continuousAt.comp ((Rb.A.chart kb).continuousAt hz.2.1)
    exact ContinuousAt.comp_continuousWithinAt (g := fun x => Rb.A.chart kb x l) c3 c2
  · simp only [wRho, e]
    exact cLow (fstPt k₀) cF q.1.1 q.1.2.1 q.1.2.2 z hz fun k e' => hz₄ (q.1.1, stepOf N j q.1.2.2) k e'
  · simp only [wRho, e]
    refine (cLow (sndPt k₀) cS τ cb ca z hz fun k e' => ?_).sub (cLow (fstPt k₀) cF τ cb ca z hz fun k e' => ?_)
    · rw [hst] at e' ⊢
      obtain rfl : k₀ = k := Option.some.inj (hk.symm.trans e')
      exact hz₅
    · exact hz₄ (τ, stepOf N j ca) k e'

end Flag

end GlobalTheory.CompanionTheory.Ar.PB.WMan
