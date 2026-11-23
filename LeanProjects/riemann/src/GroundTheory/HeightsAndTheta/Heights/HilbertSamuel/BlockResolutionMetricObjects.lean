import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory

noncomputable section

variable {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

def blockCGram (d : HSMBlockDatum D K ι Ω) (n : ℕ) {r : ℕ} (b : Fin r → MvPolynomial (Σ k, ι k) ℚ) :
    Matrix (Fin r) (Fin r) ℂ :=
  fun k l => ∫ x, pairValH d.A n (b k) (b l) (blockPt d x) ∂d.dV

open Classical in

def blockCChi (d : HSMBlockDatum D K ι Ω) (n : ℕ) : ℝ :=
  if h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Σ k, ι k) ℚ), IsSecBasisM d.y d.k₀ n p.2 then
    -(1 / 2) * Real.log (blockCGram d n h.choose.2).det.re
  else 0

def blockInterpPot (d : HSMBlockDatum D K ι Ω) (A A' : HermLine ι) (t : ℝ) : LocPot d.R.X where
  U := d.R.U
  isOpen_U := d.R.isOpen_U
  mem_U := d.R.mem_U
  φ x y := (1 - t) * Real.log (A.h (d.R.lift x y)) + t * Real.log (A'.h (d.R.lift x y))

def blockMetricInt (d : HSMBlockDatum D K ι Ω) (A' : HermLine ι) : ℝ :=
  ∫ t in (0 : ℝ)..1, mInt d.R.A (fun _ => blockInterpPot d d.A A' t)
    fun x => Real.log (A'.h (blockPt d x) / d.A.h (blockPt d x))

def blockMixPot (A A' : HermLine ι) (D i : ℕ) : Fin D → ((Σ k, ι k) → ℂ) → ℝ :=
  fun j z => if j.val < i then Real.log (A'.h z) else Real.log (A.h z)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
