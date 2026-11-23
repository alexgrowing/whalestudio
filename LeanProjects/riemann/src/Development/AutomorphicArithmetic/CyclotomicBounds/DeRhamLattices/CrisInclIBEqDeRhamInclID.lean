import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanOfPowMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRpToBdR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImageDeRhamEqEisensteinPowMulOfComponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

theorem _root_.UpperTheory.KN.crisIncl_iB_eq_deRhamIncl_iD :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l) (f : ZMod a → invL l (S O K e)),
    iotaO O C (ϖ.iB t K f) = dRO l O (ϖ.iD t K (fun τ => GlobalTheory.GalStep.hatR O (f τ : K⟦X⟧))) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ _ t ϖ C f
  have hS : ∀ τ, ϖ.iSD O K (f τ) = ϖ.iHat O K (GlobalTheory.GalStep.hatR O (f τ : K⟦X⟧)) := fun τ => by
    have hm : ((f τ : invL l (S O K e)) : K⟦X⟧) ∈ Rpi O K l e := invL_S_le_Rpi l e (f τ).2
    refine GlobalTheory.BKReal.TwoMaps.iSD_eq_iHat_of_hat l a e O K t ϖ (f τ) _ ?_
    rw [GlobalTheory.GalStep.hatR_of_mem (O := O) hm]
    exact hat_coe_Rpi l e ⟨_, hm⟩
  rw [PiSys.iB, PiSys.iD, glue_apply, glue_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hI : iotaO O C (idem (constB t) τ) = dRO l O (idem (constD t) τ) :=
    iotaO_toB C (constA t (Pi.single τ 1))
  rw [map_mul, hI, iotaO_iSl ϖ C (f τ), hS, map_mul]
