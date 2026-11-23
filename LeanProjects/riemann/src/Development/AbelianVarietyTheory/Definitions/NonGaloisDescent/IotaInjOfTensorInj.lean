import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyLocalPeriodRingsData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusPeriodRingInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRGaloisInvariantsEqFinExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineTIsUnitBcrisAndUniformizerBdRPlus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisGaloisActionFontaineTEqCyclotomic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFrobeniusFontaineTEqMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalPeriodRingsDataUnramifiedLaws

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.RingsModel

variable {l : ℕ} [Fact l.Prime]

theorem exists_core_facts (l : ℕ) [Fact l.Prime] : ∃ C : Core l, C.PhiInj ∧ C.IotaInj ∧ C.InvdR := by
  obtain ⟨C⟩ := nonempty_core l
  exact ⟨C, phiB_injective l, (ULaws.u_laws l C).2.2.2.1, fun K b hb => InvDR.invariants_BdR l C K b hb⟩

theorem iotaInj_of_tensorInj (C : Core l) (h : C.TensorInj) : C.IotaInj := by
  refine (injective_iff_map_eq_zero C.ι).2 fun b hb => ?_
  refine h 1 (fun _ => 1) ?_ (fun _ => b) (by simp [hb]) 0
  exact linearIndependent_unique_iff.2 one_ne_zero

theorem sigma_tB (C : Core l) (g : GQ l) :
    Per.σB g C.tB = C.qB (((C.χ g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) * C.tB := by
  have h1 : Per.σB g C.tB = algebraMap (Per.Acris l) (Per.Bcris l) (sigA g C.t) := by
    have := plusToB_sig g (algebraMap (Per.Acris l) (BcrisP l) C.t)
    rw [sigP_alg, plusToB_alg, plusToB_alg] at this
    exact this.symm
  rw [h1, TAct.t_act l C g, map_mul]
  congr 1
  apply (ULaws.u_laws l C).2.2.2.1
  rw [C.ι_j, InvDR.j_alg, ← C.o_sec.z]
  exact (C.ι_u (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (((C.χ g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]))).symm

theorem phi_tB (C : Core l) : Per.φB l C.tB = ((l : ℕ) : Per.Bcris l) * C.tB := by
  have := plusToB_phi (algebraMap (Per.Acris l) (BcrisP l) C.t)
  rw [phiP_alg, plusToB_alg, plusToB_alg, TPhi.t_phi l C, map_mul, map_natCast] at this
  exact this.symm

theorem inv_t_not_plus (C : Core l) (x : BcrisP l) : plusToB l x * C.tB ≠ 1 := by
  intro h
  have h2 := congrArg C.ι h
  rw [map_mul, map_one, C.ι_plusToB, Core.tB, C.ι_j, ← map_mul,
    ← map_one (algebraMap (Per.BdRp l) (Per.BdR l))] at h2
  have h3 := congrArg (Per.θD l) ((BdRField.bdR_isField l).2.1 h2)
  have h4 : Per.θD l (C.j C.t) = 0 := by
    have := (core_t_unit_fil l C).2.1
    rw [← (thetaD_onto_ker l).2] at this
    exact this
  rw [map_mul, h4, mul_zero, map_one] at h3
  exact zero_ne_one h3

variable {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l}

theorem qB_of_fits (h : Fits T C) (x : ℚ_[l]) : T.eB (algebraMap ℚ_[l] P.R.B x) = C.qB x := by
  rw [IsScalarTower.algebraMap_apply ℚ_[l] ↥(MaximalUnramifiedExtension l) P.R.B, h.u]
  rfl

theorem fund_of_fits (h : Fits T C) : C.Fund := by
  intro b hφ hF
  obtain ⟨b, rfl⟩ := T.eB.surjective b
  obtain ⟨K⟩ : Nonempty (FinExt l) := ⟨⟨⊥, inferInstance⟩⟩
  obtain ⟨c, hc⟩ := (P.PD K).fund b
    (by rw [P.PD_φ]; apply T.eB.injective; rw [T.frob, hφ])
    (by rw [T.fil, P.PD_ι, h.ι]; exact hF)
  exact ⟨c, by rw [← qB_of_fits h, hc]⟩

theorem invB_of_fits (h : Fits T C) : C.InvB := by
  intro K b hb
  obtain ⟨b, rfl⟩ := T.eB.surjective b
  obtain ⟨c, hc⟩ := (P.PD K).invB b fun g => by
    rw [P.PD_actB]; apply T.eB.injective; rw [T.actB]; exact hb g g.2
  refine ⟨⟨c, c.2.2⟩, c.2.1, ?_⟩
  rw [← h.u, ← hc]
  rfl

theorem isField_of_isStd (h : GlobalTheory.Per.IsStd P AI) : IsField P.R.BdR := by
  obtain ⟨T⟩ := h
  exact T.eD.toMulEquiv.isField (BdRField.bdR_isField l).2.2.1

end GlobalTheory.MemLoc.RingsModel
