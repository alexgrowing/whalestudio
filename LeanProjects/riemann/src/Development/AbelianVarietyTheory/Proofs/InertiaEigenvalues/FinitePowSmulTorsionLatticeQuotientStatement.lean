import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePowSmulTorsionLatticeQuotient
import Mathlib
import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_pow_smul_torsion_lattice_quotient : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V] (T : Submodule O V), IsTopologicalRing O → CompactSpace O → IsAdic (IsLocalRing.maximalIdeal O) → IsLatticeIn T → ∀ ϖ : O, Irreducible ϖ → ∀ n : ℕ, Finite ↥(LinearMap.ker (LinearMap.lsmul O (V ⧸ T) (ϖ ^ n))) := by
  first | exact @GlobalTheory.LatTorsFinite.finite_ker_pow_smul | exact GlobalTheory.LatTorsFinite.finite_ker_pow_smul | (intros; apply GlobalTheory.LatTorsFinite.finite_ker_pow_smul <;> assumption)
