import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.WeakTop

theorem coords_one_tmul_smul {R O W T ι : Type} [CommRing R] [CommRing O] [Algebra R O] [CommRing W] [Algebra R W] [AddCommGroup T] [Module O T] [Module R T] [IsScalarTower R O T] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R T) (w : W) (z : (O ⊗[R] W) ⊗[O] T) (i : ι) :
    GlobalTheory.WeakTop.coords W O b (((1 : O) ⊗ₜ[R] w) • z) i = w * GlobalTheory.WeakTop.coords W O b z i := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add, Pi.add_apply, hx, hy, mul_add]
  | tmul r t =>
    induction r using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [add_tmul, smul_add, map_add, Pi.add_apply, hx, hy, mul_add]
    | tmul a w' =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        coords_tmul, coords_tmul]
      simp only [Algebra.smul_def]
      ring

end GlobalTheory.WeakTop
