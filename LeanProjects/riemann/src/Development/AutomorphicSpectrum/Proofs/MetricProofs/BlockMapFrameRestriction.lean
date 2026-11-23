import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UpVApply
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.PtsBase

section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}
  {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)]

theorem exists_section (M : FlagModel y Ψ N j) {κ : Kk → K} {v : (Σ k, ιk k) → (Σ k, ι k)} (hb : IsBlockMap κ v)
    (hr : ∀ k : NonPluckerBlocks M.blk, k.1 ∈ Set.range κ) :
    ∃ (κ' : NonPluckerBlocks M.blk → Kk) (v' : (Σ k, baseIdx ι M.blk k) → (Σ k, ιk k)), IsBlockMap κ' v' ∧
      (∀ q, v (v' q) = ⟨q.1.1, q.2⟩) ∧ ∀ z, pBase M v z = z ∘ v' := by
  choose κ' hκ' using hr
  have hex : ∀ q : Σ k, baseIdx ι M.blk k, ∃ q', v q' = ⟨q.1.1, q.2⟩ := fun q =>
    hb.2.2.2 ⟨q.1.1, q.2⟩ ⟨κ' q.1, hκ' q.1⟩
  choose v' hv' using hex
  have hfst : ∀ p, (v' p).1 = κ' p.1 := fun p => hb.1 (by
    rw [← hb.2.2.1, hv', hκ'])
  refine ⟨κ', v', ⟨fun a b e => Subtype.ext (by rw [← hκ' a, ← hκ' b, e]), fun a b e => ?_, hfst, ?_⟩, hv', fun z => ?_⟩
  · have e' := congrArg v e
    rw [hv', hv'] at e'
    exact (GlobalTheory.CompanionTheory.Ar.PB.CPts.blockMap_base M).2.1 e'
  · rintro q ⟨kb, hq⟩
    have h1 : (v q).1 ∈ Set.range (Subtype.val : NonPluckerBlocks M.blk → K) :=
      ⟨kb, by rw [hb.2.2.1, ← hq, hκ']⟩
    obtain ⟨p, hp⟩ := (GlobalTheory.CompanionTheory.Ar.PB.CPts.blockMap_base M).2.2.2 (v q) h1
    exact ⟨p, hb.2.1 ((hv' p).trans hp)⟩
  · funext q
    show upV v z ⟨q.1.1, q.2⟩ = z (v' q)
    rw [← hv', upV_apply hb.2.1]

end

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)), IsBlockMap κ v → (∀ k, k ∈ Set.range κ ↔ ((∀ p, M.blk p ≠ some k) ∨ ∃ p, keep p ∧ M.blk p = some k)) → (∀ z ∈ mcPts (mCoordIdeal (y ∘ v)), pBase M v z ∈ mcPts (mCoordIdeal M.x)) ∧ ∀ z z' : (Σ k, ιk k) → ℂ, SameOrbit z z' → SameOrbit (pBase M v z) (pBase M v z') := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M keep Kk _ ιk _ κ v hb hk
  obtain ⟨κ', v', hb', hv', hz⟩ := exists_section M hb fun k => (hk k.1).2 (Or.inl k.2)
  refine ⟨fun z hzm => ?_, fun z z' ho => ?_⟩
  · rw [hz]
    refine GlobalTheory.CompanionTheory.Ar.PB.CPts.comp_mem_mcPts hb' (algebraMap M.Ω Φ) (funext fun q => ?_) hzm
    show y (v (v' q)) = algebraMap M.Ω Φ (M.x q)
    rw [hv']
    exact M.y_base q
  · obtain ⟨c, hc, e⟩ := ho
    refine ⟨fun k => c (κ' k), fun k => hc _, ?_⟩
    rw [hz, hz, e]
    funext q
    show c (v' q).1 * z' (v' q) = c (κ' q.1) * z' (v' q)
    rw [hb'.2.2.1]

end GlobalTheory.CompanionTheory.Ar.PB.PFl.PtsBase
