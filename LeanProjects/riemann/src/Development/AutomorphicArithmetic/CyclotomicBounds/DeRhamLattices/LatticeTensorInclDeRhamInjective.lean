import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanOfPowMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRpToBdR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImageDeRhamEqEisensteinPowMulOfComponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanFiltrationZeroOfIntegralTensorLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

theorem _root_.UpperTheory.KN.latticeTensorIncl_deRham_injective :
    ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K] (T : LocLat (Gl l) ℚ_[l] K O), Function.Injective (TWincl (dRO l O) T) := by
  intro l _ O K _ _ _ _ _ _ _ T
  classical
  have h0 : Function.Injective (bdRpToBdR l) := (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.1
  have h1 : Function.Injective (dRO l O) := by
    intro r s h
    let b := Module.Free.chooseBasis ℤ_[l] O
    apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
    ext k
    apply h0
    rw [← equivFinsuppOfBasisLeft_map_id, ← equivFinsuppOfBasisLeft_map_id]
    exact congrArg (fun y => TensorProduct.equivFinsuppOfBasisLeft b y k) h
  intro w z h
  haveI := T.L.free
  let bT := Module.Free.chooseBasis O ↥T.L.T
  apply (TensorProduct.equivFinsuppOfBasisRight bT).injective
  refine Finsupp.ext (fun j => ?_)
  apply h1
  rw [← equivFinsuppOfBasisRight_map_id, ← equivFinsuppOfBasisRight_map_id]
  exact congrArg (fun y => TensorProduct.equivFinsuppOfBasisRight bT y j) h
