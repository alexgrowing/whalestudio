import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsImg
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverPt

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ} {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ']
  {y' : (Σ k, ι' k) → Φ'}

def plk (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ) (i : Fin N)
    (q : Σ k, ι k) (h : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  ∑ I, valAt M.x (F.u q I) b * minorIJ h I (stepCols N j i)

def stepCoord {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ k, ι' k) → ℂ)
    (p : Ψ × Fin N) (k' : K') (q : Σ k, ι k) : ℂ :=
  ∑ I, valAt M.x (F.u q I) (basePart M'.blk z ∘ Cv.v) *
    ∑ I', if IsStepRows N j p.2 I' then minorIJ (Cv.trans F' F (basePart M'.blk z) p.1) I I' *
      ∑ m' : ι' k', valAt M'.x (F'.u' I' ⟨k', m'⟩) (basePart M'.blk z) * z ⟨k', m'⟩ else 0

def img {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ k, ι' k) → ℂ) :
    (Σ k, ι k) → ℂ := fun q =>
  if hk : ∀ p, M.blk p ≠ some q.1 then basePart M'.blk z (Cv.v ⟨⟨q.1, hk⟩, q.2⟩)
  else
    have hp : ∃ p, M.blk p = some q.1 := by simpa using hk
    match M'.blk hp.choose with
    | none => 0
    | some k' => stepCoord Cv F' F z hp.choose k' q

theorem img_base {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ k, ι' k) → ℂ) :
    basePart M.blk (img Cv F' F z) = basePart M'.blk z ∘ Cv.v := by
  funext q
  obtain ⟨⟨k, hk⟩, m⟩ := q
  simp only [basePart, img, Function.comp]
  rw [dif_pos hk]

theorem img_step {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ k, ι' k) → ℂ)
    {p : Ψ × Fin N} {k : K} {k' : K'} (hp : M.blk p = some k) (hp' : M'.blk p = some k') (m : ι k) :
    img Cv F' F z ⟨k, m⟩ = stepCoord Cv F' F z p k' ⟨k, m⟩ := by
  have hk : ¬ ∀ p', M.blk p' ≠ some k := fun h => h p hp
  have hex : ∃ p', M.blk p' = some k := ⟨p, hp⟩
  have hch : hex.choose = p := M.blk_inj _ _ k hex.choose_spec hp
  simp only [img, dif_neg hk]
  split
  · next h =>
    rw [hch, hp'] at h
    exact absurd h (by simp)
  · next k'' h =>
    rw [hch, hp'] at h
    cases h
    rw [hch]

theorem exists_blk_cover {M : FlagModel y Ψ N j} (M' : FlagModel y' Ψ N j) {p : Ψ × Fin N} {k : K}
    (hp : M.blk p = some k) : ∃ k', M'.blk p = some k' := by
  have h1 : ¬ (M.blk p = none) := by
    rw [hp]
    simp
  rw [M.blk_none] at h1
  have h2 : M'.blk p ≠ none := by
    rw [Ne, M'.blk_none]
    exact h1
  exact Option.ne_none_iff_exists'.mp h2

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
