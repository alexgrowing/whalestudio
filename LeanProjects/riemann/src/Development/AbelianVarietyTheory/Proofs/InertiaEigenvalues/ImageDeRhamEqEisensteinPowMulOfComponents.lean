import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InclLSmulCoord
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRpToBdR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HatOfInvariantSeries
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

noncomputable section

namespace GlobalTheory.BKGal.HatVal

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]

theorem iotaO_toOB (C : GlobalTheory.MemLoc.Core l) (x : OCr l O) :
    iotaO O C (toOB l O x) = dRO l O (crisToOD l O x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w =>
    exact congrArg (fun y : Per.BdR l => o ⊗ₜ[ℤ_[l]] y)
      ((C.ι_j w).trans (by rw [eq_crisP C.j_cris]; rfl))
  | add x y hx hy => simp only [map_add, hx, hy]

theorem iotaO_iSl {e : ℕ} [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
    {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
    (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l) (g : invL l (S O K e)) :
    iotaO O C (ϖ.iSl O K g) = dRO l O (ϖ.iSD O K g) := by
  have h : (iotaO O C).toRingHom.comp (ϖ.iSl O K).toRingHom = (dRO l O).toRingHom.comp (ϖ.iSD O K) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (l : S O K e)) (RingHom.ext fun s => ?_)
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    have h3 : ϖ.iSl O K (algebraMap (S O K e) (invL l (S O K e)) s) = toOB l O (ϖ.iS O K s) :=
      ϖ.iSl_of_mem O K s.2 _
    have h4 : ϖ.iSD O K (algebraMap (S O K e) (invL l (S O K e)) s) = crisToOD l O (ϖ.iS O K s) :=
      ϖ.iSD_of_mem O K s.2 _
    rw [h3, h4]
    exact iotaO_toOB C _
  exact RingHom.congr_fun h g

end GlobalTheory.BKGal.HatVal

open GlobalTheory.BKGal.HatVal in

theorem GlobalTheory.BKGal.HatVal.iotaO_iB_eq_Epow_mul : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) [CompleteSpace K] (C : GlobalTheory.MemLoc.Core l) (η : ℕ) (f : ZMod a → invL l (S O K e)), (∀ τ, ∃ r ∈ Rpi O K l e, (f τ : K⟦X⟧) = E K l e ^ η * r) → ∃ z : OD l O, iotaO O C (ϖ.iB t K f) = dRO l O (toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ η * z) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ _ C η f hf
  choose r hr hfr using hf
  set P : OD l O := toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) with hP
  have hE : ϖ.iHat O K (Ehat O K l e) = P := by
    rw [Ehat, PiSys.iHat_ofAl]
    exact (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E a O K))
  have hS : ∀ τ, ϖ.iSD O K (f τ) = P ^ η * ϖ.iHat O K (toHat O K l e ⟨r τ, hr τ⟩) := fun τ => by
    have h1 : hat O l e ((f τ : invL l (S O K e)) : K⟦X⟧) =
        algebraMap _ (AhatE O K l e) (Ehat O K l e ^ η * toHat O K l e ⟨r τ, hr τ⟩) := by
      have h2 : E K l e ^ η * r τ = ((EIn l e (Rpi O K l e) ^ η * ⟨r τ, hr τ⟩ : Rpi O K l e) : K⟦X⟧) := by
        simp [EIn]
      rw [hfr τ, h2, hat_coe_Rpi, map_mul, map_pow, toHat_E]
    rw [GlobalTheory.BKReal.TwoMaps.iSD_eq_iHat_of_hat l a e O K t ϖ (f τ) _ h1, map_mul, map_pow, hE]
  refine ⟨∑ τ, idem (constD t) τ * ϖ.iHat O K (toHat O K l e ⟨r τ, hr τ⟩), ?_⟩
  rw [PiSys.iB, glue_apply, map_sum, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hI : iotaO O C (idem (constB t) τ) = dRO l O (idem (constD t) τ) :=
    iotaO_toB C (constA t (Pi.single τ 1))
  rw [map_mul, hI, iotaO_iSl ϖ C (f τ), hS, map_mul, map_mul, map_mul]
  ring
