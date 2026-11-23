import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyThetaOnBdRPlusPeriodData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant

namespace GlobalTheory.ExpImage

open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.MemLoc GlobalTheory.ThetaTie
open scoped Formalism.Per

theorem exists_inv_io_pi : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → ∃ u ∈ FilB P 0, io AI AI.π₁ * u = 1 := by
  intro l _ P AI T
  obtain ⟨-, -, hun, hth, -⟩ := thetaD_props l
  have hθ : Per.θ l AI.π₁ ≠ 0 := by
    have h : Per.θ l AI.π₁ = PreTilt.untilt AI.ε1 - 1 := by
      rw [LocAinf.π₁, map_sub, WittVector.fontaineTheta_teichmuller, map_one]
    rw [h]
    exact sub_ne_zero.2 (isEps AI).2
  have hne : Per.θD l (aDp l AI.π₁) ≠ 0 := by
    rw [hth]
    exact fun h0 => hθ (Subtype.ext h0)
  obtain ⟨v, hv⟩ := (hun _ hne).exists_right_inv
  refine ⟨T.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) v),
    (fil_zero T _).2 ⟨v, (T.eD.apply_symm_apply _).symm⟩, T.eD.injective ?_⟩
  rw [map_mul, io_apply, eD_ιA, T.eD.apply_symm_apply, ← map_mul, hv, map_one, map_one]

end GlobalTheory.ExpImage
