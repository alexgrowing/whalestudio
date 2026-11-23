import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalPeriodRingsDataUnramifiedLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBcrisBasicTheoremsProofStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowMulEqThetaWittStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalPeriodRingsSectionEqAinfToBdRPlusStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.TeichmullerPowerUnit

theorem exists_pow_mul_u_eq_aB : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (c : ↥(MaximalUnramifiedExtension l)), (c : Om l) ∈ K.1 → ∃ (n : ℕ) (w : Wq l bk.a), (l : Per.Bcris l) ^ n * C.u c = Per.aB l (wA l bk.a w) := by
  intro l _ K bk C c hc
  obtain ⟨n, w, hw⟩ := GlobalTheory.T.exists_prime_pow_mul_eq_theta_witt l K bk (c : Om l) hc c.2
  have ho := GlobalTheory.T.localPeriodRings_section_eq_ainfToBdRPlus l bk.a C w ((l : Om l) ^ n * (c : Om l)) hw
  refine ⟨n, w, ?_⟩
  apply GlobalTheory.Published.FontaineBcris.iotaInj GlobalTheory.T.fontaineBcrisBasicTheorems_proof C
  have hB : C.ι (Per.aB l (wA l bk.a w)) =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (wA l bk.a w)) :=
    GlobalTheory.MemLoc.ULaws.iota_aB C (wA l bk.a w)
  rw [hB, ← ho, map_mul, map_pow, map_natCast, C.ι_u, map_mul, map_pow, map_natCast, map_mul, map_pow, map_natCast]

end GlobalTheory.TeichmullerPowerUnit
