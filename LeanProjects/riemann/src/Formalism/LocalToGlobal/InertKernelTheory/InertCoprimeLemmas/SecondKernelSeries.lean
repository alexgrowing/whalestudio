import Formalism.LocalToGlobal.InertKernelTheory.TieSerPin
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelNonzeroUnit

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.SecondKernelSeries

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.KerInert.K2 Formalism.L2.KerInert.SecondKernelInstances

theorem eFac_ne_zero {p : ℕ} [Fact p.Prime] {X : Sys p} (Y : Pend X) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) :
    Y.eS j La * (Y.eT j La')⁻¹ ≠ 0 := by
  refine mul_ne_zero ?_ (inv_ne_zero ?_) <;>
  · refine Finset.prod_ne_zero_iff.mpr fun v _ => zpow_ne_zero _ ?_
    have hs := X.G.P.setting v
    haveI := hs.frac_alt
    have h1 : ((p : ℕ) : X.G.P.W v) ≠ 0 := hs.p_unif.ne_zero
    have h2 : ((p : ℕ) : X.G.P.Qq v) ≠ 0 := by
      rw [← map_natCast (algebraMap (X.G.P.W v) (X.G.P.Qq v))]
      exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr h1
    rw [← map_natCast (X.G.P.ι v)]
    exact (map_ne_zero _).mpr h2

theorem series_compatibility_of : TieSerOf := by
  intro p _ X Y j La _ c' L' _
  unfold srOf
  rw [smul_smul, inv_mul_cancel₀ (eFac_ne_zero Y j La (c', L')), one_smul]

end Formalism.L2.KerInert.SecondKernelSeries
