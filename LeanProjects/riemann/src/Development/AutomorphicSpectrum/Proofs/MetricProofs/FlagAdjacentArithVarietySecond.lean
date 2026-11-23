import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatementStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseVectorProperties
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem exists_flags_of_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (d : ℕ) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → ∀ (l : Fin BM.q), ∀ b' ∈ BM.O l, ∀ z ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)), SameOrbit (basePart M.blk (fstPt k₀ z)) (BM.Rb.lift b' b') → ∃ (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (t : ℂ), (∀ τ', IsBlockDiag j (h τ') ∧ (h τ').det ≠ 0) ∧ SameOrbit z (FC.wVec M (BM.F l) (FC.bvec BM l b') h τ a k₀ ca cb t) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM d τ a b k₀ ca cb hb hj hblk hca hcb hy l b' hb' z hz ho
  obtain ⟨g1, g2, g3, g4⟩ := FC.bvec_good K ι Φ y Ψ N j M n BM l b' hb'
  set β := FC.bvec BM l b' with hβ
  obtain ⟨c, hc, ec⟩ : SameOrbit (basePart M.blk (fstPt k₀ z)) β := orbit_trans ho (orbit_symm g4)
  let t : Option K → ℂ := fun o => match o with
    | some k => if hk : ∀ p, M.blk p ≠ some k then (c ⟨k, hk⟩)⁻¹ else 1
    | none => 1
  have ht : ∀ o, t o ≠ 0 := fun o => by
    cases o with
    | none => exact one_ne_zero
    | some k =>
      by_cases hk : ∀ p, M.blk p ≠ some k
      · simp only [t, dif_pos hk]
        exact inv_ne_zero (hc _)
      · simp only [t, dif_neg hk]
        exact one_ne_zero
  let z₁ : (Σ o : Option K, ι (o.getD k₀)) → ℂ := fun p => t p.1 * z p
  have o2 : SameOrbit z₁ z := ⟨t, ht, rfl⟩
  have hz₁ : z₁ ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) :=
    mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal _) o2 hz
  have eb : basePart M.blk (fstPt k₀ z₁) = β := by
    funext q
    obtain ⟨⟨k, hk⟩, m⟩ := q
    have e : z ⟨some k, m⟩ = c ⟨k, hk⟩ * β ⟨⟨k, hk⟩, m⟩ := congrFun ec ⟨⟨k, hk⟩, m⟩
    show t (some k) * z ⟨some k, m⟩ = β _
    simp only [t, dif_pos hk]
    rw [e, inv_mul_cancel_left₀ (hc _)]
  have P := GlobalTheory.T.log_period_statement K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hj hblk hca hcb hy (BM.F l) z₁ (BM.isFrame l)
    (by rw [eb]; exact g1) (by rw [eb]; exact g2) (by rw [eb]; exact g3)
  obtain ⟨h, s, f1, f2⟩ := P.1 hz₁
  refine ⟨h, s, f1.2.1, orbit_trans (orbit_symm o2) ?_⟩
  have eb2 : basePart M.blk (sndPt k₀ z₁) = β := by
    funext q
    obtain ⟨⟨k, hk⟩, m⟩ := q
    have hne : k ≠ k₀ := fun e => hk (τ, a) (by rw [hblk, e])
    have e1 : sndPt k₀ z₁ ⟨k, m⟩ = fstPt k₀ z₁ ⟨k, m⟩ := by
      show z₁ (v₁ k₀ ⟨k, m⟩) = z₁ (v₀ k₀ ⟨k, m⟩)
      rw [v₁_ne hne]
      rfl
    exact e1.trans (congrFun eb ⟨⟨k, hk⟩, m⟩)
  have key : ∀ o : Option K, ∃ e : ℂ, e ≠ 0 ∧ ∀ m : ι (o.getD k₀),
      z₁ ⟨o, m⟩ = e * FC.wVec M (BM.F l) β h τ a k₀ ca cb s ⟨o, m⟩ := fun o => by
    cases o with
    | none =>
      obtain ⟨e, he, w⟩ := f2.2.2 (τ, a) k₀ hblk
      refine ⟨e, he, fun m => ?_⟩
      have w' := w m
      rw [eb2] at w'
      simp only [Function.update_self] at w'
      have e1 : sndPt k₀ z₁ ⟨k₀, m⟩ = z₁ ⟨none, m⟩ := by
        show z₁ (v₁ k₀ ⟨k₀, m⟩) = _
        rw [v₁_self]
      rw [← e1, w']
      rfl
    | some k =>
      by_cases hk : ∀ p, M.blk p ≠ some k
      · refine ⟨1, one_ne_zero, fun m => ?_⟩
        have e1 := congrFun eb ⟨⟨k, hk⟩, m⟩
        have e2 := congrFun (FC.basePart_flagPt M (BM.F l) β h) ⟨⟨k, hk⟩, m⟩
        show z₁ ⟨some k, m⟩ = 1 * FC.flagPt M (BM.F l) β h ⟨k, m⟩
        rw [one_mul]
        exact e1.trans e2.symm
      · push_neg at hk
        obtain ⟨p, hp⟩ := hk
        obtain ⟨e, he, w⟩ := f1.2.2 p k hp
        refine ⟨e, he, fun m => ?_⟩
        have w' := w m
        rw [eb] at w'
        show z₁ ⟨some k, m⟩ = e * FC.flagPt M (BM.F l) β h ⟨k, m⟩
        rw [FC.flagPt_step M (BM.F l) β h hp m]
        exact w'
  choose e he hm using key
  exact ⟨e, he, funext fun q => hm q.1 q.2⟩

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
