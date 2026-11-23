import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatFiniteFree
import Mathlib
import Formalism.WachLatticeTwists.LatticeDualFibres.StatDualFibreLattice
open Formalism.RepresentationBoundsCohomology.LOC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualLat_finite_free_of_isLatticeIn : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {V V' : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V] [AddCommGroup V'] [Module O V'] [Module (FractionRing O) V'] [IsScalarTower O (FractionRing O) V'] (b : V →ₗ[O] V' →ₗ[O] FractionRing O) (T : Submodule O V), IsLatticeIn T → PerfectRight b → Module.Finite O (dualLat b T) ∧ Module.Free O (dualLat b T) := by
  first | exact @GlobalTheory.dualLat_finite_free | exact GlobalTheory.dualLat_finite_free | (intros; apply GlobalTheory.dualLat_finite_free <;> assumption)
