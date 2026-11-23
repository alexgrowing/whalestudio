import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UpVApply
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMapFrameRestrictionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMapFrameRestrictionRegularStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentArithmeticHeight
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsBaseChartAtGoodPointStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsContinuousOrbitSectionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticSecond
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBlockDiagMapGenBlock
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.Cover

open GlobalTheory.CompanionTheory.Ar.PB.WMan.Cover GlobalTheory.CompanionTheory.Ar.PB.ValRing

section Scale

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)]

theorem upV_smul {κ : Kk → K} {v : (Σ k, ιk k) → (Σ k, ι k)} (hb : IsBlockMap κ v) (c : K → ℂ)
    (z : (Σ k, ιk k) → ℂ) (q : Σ k, ι k) :
    upV v (fun p => c (κ p.1) * z p) q = c q.1 * upV v z q := by
  unfold upV
  by_cases h : ∃ q', v q' = q
  · rw [dif_pos h, dif_pos h]
    have e : κ h.choose.1 = q.1 := by
      rw [← hb.2.2.1, h.choose_spec]
    show c (κ h.choose.1) * z h.choose = _
    rw [e]
  · rw [dif_neg h, dif_neg h, mul_zero]

end Scale

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)), IsBlockMap κ v → (∀ k, k ∈ Set.range κ ↔ ((∀ p, M.blk p ≠ some k) ∨ ∃ p, keep p ∧ M.blk p = some k)) → ∀ z ∈ mcPts (mCoordIdeal (y ∘ v)), ∃ (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ), IsPCtx M Rb keep κ v F kb V bl r h ∧ z ∈ pO M Rb keep v F kb V r h := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n Rb keep Kk _ ιk _ κ v hbm hrange z hz
  obtain ⟨bs, -⟩ := GlobalTheory.T.blockMap_frame_restriction K ι Φ y Ψ N j M keep Kk ιk κ v hbm hrange
  obtain ⟨-, fr, -⟩ := CPts.main K ι Φ y Ψ N j M
  have hzb : pBase M v z ∈ mcPts (mCoordIdeal M.x) := bs z hz
  obtain ⟨F, hF, hG⟩ := fr _ hzb
  have hnon : Nonempty Rb.X := by
    obtain ⟨x, -⟩ := Rb.surj _ hzb fun h => by
      have := h.2 1 Submodule.mem_top
      simp at this
    exact ⟨x⟩
  obtain ⟨r, hr1, hr2⟩ := GlobalTheory.T.exists_continuous_orbit_section _ _ _ n Rb hnon
  have hx0 := hr1 _ hzb
  obtain ⟨kb, V, bl, hsrc, hV, hBC⟩ := GlobalTheory.T.exists_base_chart_at_good_point K ι Φ y Ψ N j M n Rb F (r (pBase M v z))
    (by rw [CovMap.mCoordIdeal_eq_of_sameOrbit hx0]; exact hG)
  obtain ⟨hblm, hblnorm, hblgood, hblorb⟩ := hBC.2.2.2.2 _ hV
  rw [(Rb.A.chart kb).left_inv hsrc] at hblorb
  generalize hzc : bl (Rb.A.chart kb (r (pBase M v z))) = zc at hblm hblnorm hblgood hblorb
  have horb : SameOrbit zc (pBase M v z) := orbit_trans (orbit_symm hblorb) hx0
  have hval : ∀ s, (∃ u, IsValueAt M.x s zc u) → valAt M.x s (pBase M v z) = valAt M.x s zc :=
    fun s hs => valAt_eq_of_orbit hblm hzb (orbit_symm horb) hs
  obtain ⟨c₀, hc₀, he⟩ := horb
  let c : K → ℂ := fun k => if h : ∀ p, M.blk p ≠ some k then c₀ ⟨k, h⟩ else 1
  have hc : ∀ k, c k ≠ 0 := fun k => by
    by_cases h : ∀ p, M.blk p ≠ some k
    · simp only [c, dif_pos h]
      exact hc₀ _
    · simp only [c, dif_neg h]
      exact one_ne_zero
  let z' : (Σ k, ιk k) → ℂ := fun p => c (κ p.1) * z p
  have hz' : z' ∈ mcPts (mCoordIdeal (y ∘ v)) :=
    mcPts_smul (CoordinateConeArithVar.isMultiHomogIdeal _) (fun k => c (κ k)) (fun k => hc _) hz
  have hbp : pBase M v z' = zc := by
    rw [he]
    funext q
    obtain ⟨⟨k, hk⟩, m⟩ := q
    show upV v z' ⟨k, m⟩ = c₀ ⟨k, hk⟩ * upV v z ⟨k, m⟩
    rw [upV_smul hbm c z ⟨k, m⟩]
    simp only [c, dif_pos hk]
  obtain ⟨h, hh, H⟩ := GlobalTheory.T.blockMap_frame_restriction_regular K ι Φ y Ψ N j M keep Kk ιk κ v hbm hrange F z' hF hz'
    (hbp ▸ hblgood) (hbp ▸ hblnorm)
  refine ⟨F, kb, V, bl, r, h, ⟨hbm, hrange, hF, hBC, hr1, hr2, hh⟩, hz, hsrc, ?_, ?_⟩
  · rw [hzc] at *
    exact hV
  · intro p k hkeep hp
    obtain ⟨A, hA0, hA'⟩ := H p k hkeep hp
    have hk : c k = 1 := dif_neg fun e => e p hp
    have hw : ∀ m : ι k, upV v z ⟨k, m⟩ =
        A * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (pBase M v z) * minorIJ (h p.1) I (stepCols N j p.2) := fun m => by
      have e : upV v z' ⟨k, m⟩ = upV v z ⟨k, m⟩ := by
        rw [upV_smul hbm c z ⟨k, m⟩]
        show c k * _ = _
        rw [hk, one_mul]
      rw [← e, hA' m, hbp]
      refine congrArg (fun s => A * s) (Finset.sum_congr rfl fun I _ => ?_)
      rw [hval _ (exists_isValueAt hblm (hblgood.2.1 _ I).1)]
    rw [twMinor_of_flag M hF hzb hG hp (hh p.1).1 hw, Matrix.nonsing_inv_mul _ (hh p.1).2.isUnit, CPts.minorIJ_one,
      mul_one]
    exact hA0

end GlobalTheory.CompanionTheory.Ar.PB.PFl.Cover
