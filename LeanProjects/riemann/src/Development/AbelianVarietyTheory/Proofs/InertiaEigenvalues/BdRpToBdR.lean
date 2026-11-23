import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InclLSmulCoord
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.HatVal

variable {l : ℕ} [Fact l.Prime]

scoped instance algZlBdR : Algebra ℤ_[l] (Per.BdR l) :=
  ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((GlobalTheory.MemLoc.aDp l).comp (algebraMap ℤ_[l] (Ainf l)))).toAlgebra

variable (l) in

def bdRpToBdR : Per.BdRp l →ₐ[ℤ_[l]] Per.BdR l where
  toRingHom := algebraMap (Per.BdRp l) (Per.BdR l)
  commutes' _ := rfl

theorem core_ι_aB (C : GlobalTheory.MemLoc.Core l) (w : Per.Ainf l) :
    C.ι (Per.aB l w) = algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l w) := by
  rw [GlobalTheory.RingIface.aB_eq_alg l w, C.ι_j, GlobalTheory.RingIface.tower l w, C.j_cris.on0, Subalgebra.coe_algebraMap]
  exact congrArg _ (RingHom.comp_apply _ _ _).symm

def iotaZ (C : GlobalTheory.MemLoc.Core l) : Per.Bcris l →ₐ[ℤ_[l]] Per.BdR l where
  toRingHom := C.ι
  commutes' z := core_ι_aB C (algebraMap ℤ_[l] (Ainf l) z)

variable (l) in

abbrev OdR (O : Type) [CommRing O] [Algebra ℤ_[l] O] : Type := O ⊗[ℤ_[l]] Per.BdR l

variable {O : Type} [CommRing O] [Algebra ℤ_[l] O]

variable (l O) in

def dRO : OD l O →ₐ[O] OdR l O := Algebra.TensorProduct.map (AlgHom.id _ _) (bdRpToBdR l)

variable (O) in

def iotaO (C : GlobalTheory.MemLoc.Core l) : OB l O →ₐ[O] OdR l O := Algebra.TensorProduct.map (AlgHom.id _ _) (iotaZ C)

theorem iotaO_toB (C : GlobalTheory.MemLoc.Core l) (x : OA l O) : iotaO O C (toB l O x) = dRO l O (toOD l O x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w =>
    exact congrArg (fun y : Per.BdR l => o ⊗ₜ[ℤ_[l]] y)
      ((congrArg C.ι (GlobalTheory.RingIface.aB_eq_alg l w).symm).trans (core_ι_aB C w))
  | add x y hx hy => simp only [map_add, hx, hy]

end GlobalTheory.BKGal.HatVal
