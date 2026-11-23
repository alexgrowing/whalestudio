import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFGTopPPowInverseLattice
import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFGTop_p_pow_inverse_lattice : ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)],
    PadicCoeff p O → FracTop O → ∀ n : ℕ,
    IsFGTop O ((1 : Submodule O (FractionRing O)).comap (LinearMap.lsmul O _ ((p : O) ^ n))) := by
  first | exact @GlobalTheory.isFGTop_comap_lsmul_one | exact GlobalTheory.isFGTop_comap_lsmul_one | (intros; apply GlobalTheory.isFGTop_comap_lsmul_one <;> assumption)
