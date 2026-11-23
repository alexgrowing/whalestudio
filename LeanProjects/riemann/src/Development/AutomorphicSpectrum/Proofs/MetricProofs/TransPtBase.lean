import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsImg
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AevalNeZeroOfNotMem
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsValueAtOfTorus
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCoordArithOfFnField
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishingStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPointsStatement

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ} {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ']
  {y' : (Σ k, ι' k) → Φ'}

def pairV {R : Type} (a : (Σ k, ι k) → R) (b : (Σ k, ι' k) → R) : (Σ k, Sum.elim ι ι' k) → R
  | ⟨.inl k, i⟩ => a ⟨k, i⟩
  | ⟨.inr k, i⟩ => b ⟨k, i⟩

theorem pairV_inl {R : Type} (a : (Σ k, ι k) → R) (b : (Σ k, ι' k) → R) (p : Σ k, ι k) :
    pairV a b (inlV p) = a p := rfl

theorem pairV_inr {R : Type} (a : (Σ k, ι k) → R) (b : (Σ k, ι' k) → R) (p : Σ k, ι' k) :
    pairV a b (inrV p) = b p := rfl

def stepOf (M : FlagModel y Ψ N j) (k : K) (h : ¬ ∀ p, M.blk p ≠ some k) : Ψ × Fin N :=
  Classical.choose (not_forall_not.1 (by simpa using h) : ∃ p, M.blk p = some k)

theorem blk_stepOf (M : FlagModel y Ψ N j) (k : K) (h : ¬ ∀ p, M.blk p ≠ some k) :
    M.blk (stepOf M k h) = some k := by
  unfold stepOf
  exact Classical.choose_spec (p := fun p => M.blk p = some k) _

def transPt {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M) : (Σ k, ι k) → Φ' := fun q =>
  if h : ∀ p, M.blk p ≠ some q.1 then algebraMap M'.Ω Φ' (Cv.φ (M.x ⟨⟨q.1, h⟩, q.2⟩))
  else ∑ I, algebraMap M'.Ω Φ' (Cv.φ (M.coef q I)) *
    minorIJ (M'.g (stepOf M q.1 h).1) I (stepCols N j (stepOf M q.1 h).2)

theorem transPt_base {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (q : Σ k, baseIdx ι M.blk k) :
    transPt Cv ⟨q.1.1, q.2⟩ = algebraMap M'.Ω Φ' (Cv.φ (M.x q)) :=
  dif_pos q.1.2

theorem transPt_step {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (p : Ψ × Fin N) (k : K) (hp : M.blk p = some k) (m : ι k) :
    transPt Cv ⟨k, m⟩ = ∑ I, algebraMap M'.Ω Φ' (Cv.φ (M.coef ⟨k, m⟩ I)) * minorIJ (M'.g p.1) I (stepCols N j p.2) := by
  have h : ¬ ∀ p, M.blk p ≠ some k := fun H => H p hp
  have e : stepOf M k h = p := M.blk_inj _ _ k (blk_stepOf M k h) hp
  rw [transPt, dif_neg h, e]

def trMat {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (τ : Ψ) : Matrix (Fin N) (Fin N) M'.Ω :=
  ((F.T τ).map Cv.φ)⁻¹ * F'.T τ

def coE {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (p : Ψ × Fin N)
    (q : Σ k, ι k) (r : Σ k, ι' k) : M'.Ω :=
  ∑ I, ∑ I' ∈ Finset.univ.filter (IsStepRows N j p.2),
    Cv.φ (F.u q I) * minorIJ (trMat Cv F' F p.1) I I' * F'.u' I' r

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
