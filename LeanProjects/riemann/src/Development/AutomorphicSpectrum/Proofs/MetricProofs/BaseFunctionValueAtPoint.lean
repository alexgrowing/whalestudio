import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TransPtBase
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBlockDiagMapGenBlock
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

theorem isValueAt_of_base : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) (N j : ℕ) (M : FlagModel y Ψ N j) (z : (Σ k, ι k) → ℂ) (s : M.Ω), z ∈ mcPts (mCoordIdeal y) → basePart M.blk z ∈ mcPts (mCoordIdeal M.x) → RegAt M.x (mCoordIdeal (basePart M.blk z)) s → IsValueAt y (algebraMap M.Ω Φ s) z (valAt M.x s (basePart M.blk z)) := by
  intro K _ ι _ Φ _ y Ψ N j M z s _ hb hs
  obtain ⟨v, hv⟩ := GlobalTheory.CompanionTheory.Ar.PB.ValRing.exists_isValueAt hb hs
  rw [GroundTheory.Heights₂.Heights.LowerBoundFree.valAt_eq hb hv]
  obtain ⟨d, g, h, hg, hh, hy, heq, hz0, rfl⟩ := hv
  let f : (Σ k, baseIdx ι M.blk k) → (Σ k, ι k) := fun q => ⟨q.1.1, q.2⟩
  have ha : ∀ p : MRing (baseIdx ι M.blk), aeval y (rename f p) = algebraMap M.Ω Φ (aeval M.x p) := fun p => by
    have e : y ∘ f = algebraMap M.Ω Φ ∘ M.x := funext M.y_base
    rw [aeval_rename, e, aeval_algebraMap_apply]
  have hev : ∀ p : MRing (baseIdx ι M.blk), eval z (map (Int.castRingHom ℂ) (rename f p)) =
      eval (basePart M.blk z) (map (Int.castRingHom ℂ) p) := fun p => by
    rw [map_rename, eval_rename]
    rfl
  refine ⟨_, rename f g, rename f h, isMultiHomog_rename_base M.blk hg, isMultiHomog_rename_base M.blk hh, ?_, ?_, ?_, ?_⟩
  · rw [ha]
    exact (map_ne_zero _).2 hy
  · rw [ha, ha, heq, map_mul]
  · rw [hev]
    exact hz0
  · rw [hev, hev]

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
