import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithRes
import GroundTheory.HeightsAndTheta.Heights.FubiniStudy
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory MeasureTheory

noncomputable section

namespace Veronese

abbrev Idx (D : ℕ) : Type := {p : Fin (D + 1) × Fin (D + 1) // p.1 ≤ p.2}

def Fld (D : ℕ) : Type := FractionRing (MvPolynomial (Fin (D + 1)) ℚ)

instance instField (D : ℕ) : Field (Fld D) :=
  inferInstanceAs (Field (FractionRing (MvPolynomial (Fin (D + 1)) ℚ)))

instance instCharZero (D : ℕ) : CharZero (Fld D) :=
  inferInstanceAs (CharZero (FractionRing (MvPolynomial (Fin (D + 1)) ℚ)))

instance instAlgebra (D : ℕ) : Algebra (MvPolynomial (Fin (D + 1)) ℚ) (Fld D) :=
  inferInstanceAs (Algebra (MvPolynomial (Fin (D + 1)) ℚ) (FractionRing (MvPolynomial (Fin (D + 1)) ℚ)))

instance instIsFractionRing (D : ℕ) : IsFractionRing (MvPolynomial (Fin (D + 1)) ℚ) (Fld D) :=
  Localization.isLocalization

def t (D : ℕ) (i : Fin (D + 1)) : Fld D := algebraMap (MvPolynomial (Fin (D + 1)) ℚ) (Fld D) (X i)

def x (D : ℕ) : Ix (Idx D) → Fld D := fun q => t D q.2.1.1 * t D q.2.1.2

def map (D : ℕ) (w : Fin (D + 1) → ℂ) : Ix (Idx D) → ℂ := fun q => w q.2.1.1 * w q.2.1.2

def wt {D : ℕ} (q : Ix (Idx D)) : ℝ := if q.2.1.1 = q.2.1.2 then 1 else 2

def scale (D : ℕ) (z : Ix (Idx D) → ℂ) : Ix (Idx D) → ℂ := fun q => (Real.sqrt (wt q) : ℂ) * z q

theorem wt_pos {D : ℕ} (q : Ix (Idx D)) : 0 < wt q := by
  unfold wt
  split_ifs <;> norm_num

theorem scale_ne_zero {D : ℕ} {z : Ix (Idx D) → ℂ} (hz : z ≠ 0) : scale D z ≠ 0 := by
  intro h
  apply hz
  funext q
  have h1 := congrFun h q
  have h2 : (Real.sqrt (wt q) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (wt_pos q)).ne'
  simpa [scale, h2] using h1

def metric (D : ℕ) : ConeMetric ℂ (Ix (Idx D)) where
  ρ z := (fsMetric (Ix (Idx D))).ρ (scale D z)
  pos z hz := (fsMetric (Ix (Idx D))).pos _ (scale_ne_zero hz)
  smul c z := by
    have : scale D (c • z) = c • scale D z := by
      funext q
      simp only [scale, Pi.smul_apply, smul_eq_mul]
      ring
    rw [this, (fsMetric (Ix (Idx D))).smul]

def gram (D n : ℕ) {r : ℕ} (b : Fin r → MvPolynomial (Ix (Idx D)) ℚ) : Matrix (Fin r) (Fin r) ℝ :=
  fun k l => (1 / 2) *
    ((∫ p : CP D, pairVal (metric D) n (b k) (b l) (map D p.rep) ∂CP.fsMeasure D).re +
      (∫ p : CP D, pairVal (metric D) n (b k) (b l) (conjPt (map D p.rep)) ∂CP.fsMeasure D).re)

open Classical in

def chi (D n : ℕ) : ℝ :=
  if h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Ix (Idx D)) ℚ), IsSecBasis (x D) n p.2 then
    -(1 / 2) * Real.log (gram D n h.choose.2).det
  else 0

end Veronese

open Veronese

def VeroneseArith.Statement : Prop :=
  ∀ D : ℕ, 1 ≤ D → IsArithVar (ι := GlobalTheory (Idx D)) (coordIdeal ℤ (Veronese.x D)) (D + 1)

def VeroneseSemipos.Statement : Prop :=
  ∀ D : ℕ, IsSemipositiveRel (ι := GlobalTheory (Idx D)) ⊥ (coordIdeal ℤ (Veronese.x D))
    (HermLine.ofCone (Veronese.metric D))

def VeroneseResolution.Statement : Prop :=
  ∀ D : ℕ, 1 ≤ D → ∃ (J : Ideal (MRing (GlobalTheory (Idx D))))
    (R : AnRes (ι := GlobalTheory (Idx D)) (coordIdeal ℤ (Veronese.x D)) J D)
    (_ : MeasurableSpace R.X) (_ : BorelSpace R.X) (dV : Measure R.X),
    IsSmoothVolume R.A dV ∧
    ∀ g : (Ix (Idx D) → ℂ) → ℂ, (∀ (c : ℂ) (z : Ix (Idx D) → ℂ), c ≠ 0 → g (c • z) = g z) →
      ∫ y, g (R.lift y y) ∂dV = ∫ p : CP D, g (Veronese.map D p.rep) ∂CP.fsMeasure D

def VeroneseChi.Statement : Prop :=
  ∀ D : ℕ, 1 ≤ D → ∀ n : ℕ, Veronese.chi D n = chiP D (2 * n)

def VeroneseTop.Statement : Prop :=
  ∀ D : ℕ, 1 ≤ D → ∀ I : AllFam, I.IsFamily →
    top I (Veronese.x D) (Veronese.metric D) D = 2 ^ (D + 1) * hhOf I D

def VeroneseGenDeg.Statement : Prop :=
  ∀ D : ℕ, 1 ≤ D → genDeg (ι := GlobalTheory (Idx D)) (coordIdeal ℤ (Veronese.x D)) D 1 = 2 ^ D

example : (1 : ℕ) ≤ 1 := le_rfl

example (D : ℕ) : CharZero (Veronese.Fld D) := inferInstance

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
