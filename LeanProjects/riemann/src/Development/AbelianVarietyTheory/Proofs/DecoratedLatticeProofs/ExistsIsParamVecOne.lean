import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsParamFunVIffIsSysParamDOfLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfTwoMem

noncomputable section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.TrivCoef

open GlobalTheory.LFun GlobalTheory.PRep
open Formalism.MainNotions.SchurIrreducible (IsSplit)

section Lin

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)

def trivParGL : Fin n → ℂˣ := fun i =>
  Units.mk0 ((Formalism.UG.qV E w : ℂ) ^ (((n : ℂ) - 1 - 2 * (i : ℂ)) / 2))
    (by
      rw [Ne, Complex.cpow_eq_zero_iff]
      exact fun h => qV_ne_zero w (by exact_mod_cast h.1))

theorem chiDelta_trivParGL (b : GL (Fin n) (w.adicCompletion E)) :
    Formalism.UG.chiDelta E w (fun i => (trivParGL w n i : ℂ)) b = 1 := by
  unfold Formalism.UG.chiDelta
  refine Finset.prod_eq_one fun i _ => ?_
  have hq : (Formalism.UG.qV E w : ℂ) ≠ 0 := by exact_mod_cast qV_ne_zero w
  simp only [trivParGL, Units.val_mk0]
  rw [← Complex.cpow_int_mul, ← Complex.cpow_add _ _ hq]
  convert Complex.cpow_zero _ using 2
  ring

theorem isSatVecGL_one :
    IsSatVecGL w (1 : Representation ℂ (GL (Fin n) (w.adicCompletion E)) ℂ) 1
      (Finset.univ.val.map (trivParGL w n)) := by
  have hs : Formalism.UG.IsSpherical E w (fun i => (trivParGL w n i : ℂ))
      (fun _ : GL (Fin n) (w.adicCompletion E) => (1 : ℂ)) := fun b g k _ _ => by
    rw [chiDelta_trivParGL, one_mul]
  have h := isSatVecGL_of_isSpherical hs (fun h0 => one_ne_zero (congrFun h0 1))
  exact IsSatVecGL.of_map (LinearMap.pi fun _ => LinearMap.id) (fun g y => rfl)
    (fun a b hab => congrFun hab 1) h

end Lin

section Unit

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} (q n : ℕ)

def trivParU (hq : q ≠ 0) : Fin (n / 2) → ℂˣ := fun i =>
  Units.mk0 ((q : ℂ) ^ ((n : ℤ) - 1 - 2 * (i.val : ℤ))) (zpow_ne_zero _ (by exact_mod_cast hq))

variable [CompleteSpace L]

end Unit

section Global

variable {D : D7}

end Global

end GlobalTheory.Core.Rk.TrivCoef
