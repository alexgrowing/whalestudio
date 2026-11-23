import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.IwasawaVolumeBoundOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.EqSmulOfSub
import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.AlgebraMapIntMemIntAd

noncomputable section

namespace PI.IwaMeasEx.Gauge

open MeasureTheory Topology Filter Set
open scoped ENNReal NNReal Pointwise
open Formalism.MainNotions.S

section Riem

variable {n : ℕ}

abbrev MatR (n : ℕ) : Type := EuclideanSpace ℝ (Fin n × Fin n × Bool)

def realifyM (X : Matrix (Fin n) (Fin n) ℂ) : MatR n :=
  WithLp.toLp 2 (fun p => if p.2.2 then (X p.1 p.2.1).im else (X p.1 p.2.1).re)

def toMat (x : MatR n) : Matrix (Fin n) (Fin n) ℂ := fun i j => ⟨x.ofLp (i, j, false), x.ofLp (i, j, true)⟩

def expU (x : MatR n) : (Matrix (Fin n) (Fin n) ℂ)ˣ := (Matrix.isUnit_exp (toMat x)).unit

variable {ε : Fin n → Bool}

def lieOf (H : Subgroup (Formalism.REAL.UJ ε)) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {X | ∀ t : ℝ, ∃ h ∈ H, uMat h = NormedSpace.exp ((t : ℂ) • X)}

def lieSp (H : Subgroup (Formalism.REAL.UJ ε)) : Submodule ℝ (MatR n) :=
  Submodule.span ℝ (realifyM '' lieOf H)

def conjInv (H : Subgroup (Formalism.REAL.UJ ε)) (y : Formalism.REAL.UJ ε) : Subgroup (Formalism.REAL.UJ ε) :=
  H.map (MulAut.conj y⁻¹).toMonoidHom

def expSetY (H : Subgroup (Formalism.REAL.UJ ε)) (y : Formalism.REAL.UJ ε) (T : Set (lieSp (conjInv H y))) :
    Set (Formalism.REAL.UJ ε) :=
  {g | ∃ x ∈ T, uMat g = uMat y * NormedSpace.exp (toMat (x : MatR n)) * uMat y⁻¹}

structure IsRiem (H : Subgroup (Formalism.REAL.UJ ε)) (y : Formalism.REAL.UJ ε) (R : Measure (Formalism.REAL.UJ ε)) : Prop where
  sfin : SigmaFinite R
  ne : R ≠ 0
  supp : R (H : Set (Formalism.REAL.UJ ε))ᶜ = 0
  cpt : ∀ s : Set (Formalism.REAL.UJ ε), IsCompact s → R s ≠ ⊤
  inv : ∀ h ∈ H, R.map (fun x => h * x) = R
  dens : ∀ S : Set (lieSp (conjInv H y)), MeasurableSet S → Bornology.IsBounded S →
    0 < (volume : Measure (lieSp (conjInv H y))) S → (volume : Measure (lieSp (conjInv H y))) (frontier S) = 0 →
    Tendsto (fun r : ℝ => R (expSetY H y (r • S)) / (volume : Measure (lieSp (conjInv H y))) (r • S)) (𝓝[>] 0) (𝓝 1)

def RiemHaar : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Subgroup (Formalism.REAL.UJ ε)) (y : Formalism.REAL.UJ ε), IsClosed (H : Set (Formalism.REAL.UJ ε)) →
    ∃ R, IsRiem H y R

end Riem

end PI.IwaMeasEx.Gauge

end
