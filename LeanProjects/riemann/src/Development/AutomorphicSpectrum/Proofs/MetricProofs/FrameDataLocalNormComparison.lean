import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UpVApply
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMapFrameRestrictionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartSeventh
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PMatStepColsEntry
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.Orb

section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)]

theorem upV_scale {κ : Kk → K} {v : (Σ k, ιk k) → (Σ k, ι k)} (hb : IsBlockMap κ v) (z : (Σ k, ιk k) → ℂ) (c : Kk → ℂ)
    (k₀ : Kk) (m : ι (κ k₀)) :
    upV v (fun p => c p.1 * z p) ⟨κ k₀, m⟩ = c k₀ * upV v z ⟨κ k₀, m⟩ := by
  obtain ⟨q, hq⟩ := hb.2.2.2 ⟨κ k₀, m⟩ ⟨k₀, rfl⟩
  have hk : q.1 = k₀ := hb.1 (by rw [← hb.2.2.1 q, hq])
  rw [← hq, upV_apply hb.2.1, upV_apply hb.2.1, hk]

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem pRead_scale (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (keep : Ψ × Fin N → Prop)
    {zb zb' : (Σ k, baseIdx ι M.blk k) → ℂ} (hv : ∀ s, valAt M.x s zb' = valAt M.x s zb)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) {u u' : (Σ k, ι k) → ℂ} (τ : Ψ) (a b : Fin N)
    (hu : ∀ k, M.blk (τ, pStep j keep τ b) = some k → ∃ t : ℂ, t ≠ 0 ∧ ∀ m : ι k, u' ⟨k, m⟩ = t * u ⟨k, m⟩) :
    pRead M F keep zb' h u' τ a b = pRead M F keep zb h u τ a b := by
  unfold pRead
  obtain hk | ⟨k, hk⟩ : M.blk (τ, pStep j keep τ b) = none ∨ ∃ k, M.blk (τ, pStep j keep τ b) = some k := by
    cases M.blk (τ, pStep j keep τ b) <;> simp
  · simp only [hk, Option.elim_none]
  · obtain ⟨t, ht, hu⟩ := hu k hk
    simp only [hk, Option.elim_some]
    rw [WMan.Orb.twMinor_scale M F hv _ k _ hu, WMan.Orb.twMinor_scale M F hv _ k _ hu,
      mul_left_comm (pSgn _ _ _) t, mul_div_mul_left _ _ ht]

end

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∀ z ∈ pO M Rb keep v F kb V r h, ∀ z' ∈ mcPts (mCoordIdeal (y ∘ v)), SameOrbit z' z → z' ∈ pO M Rb keep v F kb V r h ∧ pRho M Rb keep v F kb r h ε z' = pRho M Rb keep v F kb r h ε z := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb keep Kk _ ιk _ κ v F kb V bl r h ε ctx z hz z' hz' ho
  obtain ⟨hbm, hrange, -, -, hr, -, -⟩ := ctx
  obtain ⟨hzP, hs, hV, hm⟩ := hz
  have hI := GlobalTheory.T.blockMap_frame_restriction K ι Φ y Ψ N j M keep Kk ιk κ v hbm hrange
  have hb := hI.1 z hzP
  have hb' := hI.1 z' hz'
  have hob : SameOrbit (pBase M v z') (pBase M v z) := hI.2 z' z ho
  have hnot : ∀ x : Rb.X, Rb.lift x x ∉ mcPts (⊤ : Ideal (MRing (baseIdx ι M.blk))) := fun x hx => by
    have := hx.2 1 Submodule.mem_top
    simp at this
  have hrr : r (pBase M v z') = r (pBase M v z) :=
    Rb.inj _ _ (hnot _) (orbit_trans (hr _ hb') (orbit_trans hob (orbit_symm (hr _ hb))))
  have hv : ∀ s, valAt M.x s (pBase M v z') = valAt M.x s (pBase M v z) := fun s => by
    obtain ⟨t, ht, et⟩ := hob
    have := StepW.TorusAct.valAt_torus (x := M.x) t ht hb (et ▸ hb') s
    rw [et]
    exact this
  obtain ⟨c, hc, rfl⟩ := ho

  have hkept : ∀ {p : Ψ × Fin N} {k : K}, keep p → M.blk p = some k →
      ∃ t : ℂ, t ≠ 0 ∧ ∀ m : ι k, upV v (fun p => c p.1 * z p) ⟨k, m⟩ = t * upV v z ⟨k, m⟩ := by
    intro p k hp hk
    obtain ⟨k₀, rfl⟩ := (hrange k).2 (Or.inr ⟨p, hp, hk⟩)
    exact ⟨c k₀, hc k₀, upV_scale hbm z c k₀⟩
  refine ⟨⟨hz', ?_, ?_, fun p k hp hk => ?_⟩, ?_⟩
  · rw [hrr]; exact hs
  · rw [hrr]; exact hV
  · obtain ⟨t, ht, hu⟩ := hkept hp hk
    rw [WMan.Orb.twMinor_scale M F hv _ k _ hu]
    exact mul_ne_zero ht (hm p k hp hk)
  · funext i
    unfold pRho
    rcases ε.symm i with l | q
    · show Rb.A.chart kb (r (pBase M v _)) l = Rb.A.chart kb (r (pBase M v z)) l
      rw [hrr]
    · exact pRead_scale M F keep hv h _ _ _ fun k hk =>
        hkept (SmallStep.pStep_reads Ψ N j keep q M.j_le).1 hk

end GlobalTheory.CompanionTheory.Ar.PB.PFl.Orb
