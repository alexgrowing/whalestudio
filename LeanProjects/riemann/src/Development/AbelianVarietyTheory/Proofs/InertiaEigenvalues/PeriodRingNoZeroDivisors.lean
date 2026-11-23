import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AwayOfInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyLocalPeriodRingsData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisToBdRPlusInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBcrisToBdR
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.AcrisNZD

theorem eq_zero_of_smul_free {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.Free R M] {a : R} (ha : a ≠ 0) {x : M} (h : a • x = 0) : x = 0 := by
  refine (Module.Free.chooseBasis R M).repr.injective (Finsupp.ext fun i => ?_)
  have h1 := congrArg (fun y => (Module.Free.chooseBasis R M).repr y i) h
  simp only [map_smul, map_zero, Finsupp.smul_apply, smul_eq_mul, Finsupp.zero_apply] at h1 ⊢
  exact (mul_eq_zero.1 h1).resolve_left ha

theorem acris_dom (l : ℕ) [Fact l.Prime] : IsDomain (Per.Acris l) ∧ Function.Injective (aC l) := by
  obtain ⟨C⟩ := GlobalTheory.MemLoc.nonempty_core l
  haveI : IsDomain (Per.BdRp l) := (GlobalTheory.MemLoc.BdRField.bdR_isField l).1
  refine ⟨(GlobalTheory.MemLoc.crisP_injective l C.j C.j_cris).isDomain C.j, fun a b h => ?_⟩
  have h1 : C.j (algebraMap (Per.Ainf l) (Per.Acris l) a) =
      C.j (algebraMap (Per.Ainf l) (Per.Acris l) b) := congrArg C.j h
  rw [C.j_cris.on_ainf, C.j_cris.on_ainf] at h1
  exact (GlobalTheory.MemLoc.ainf_isDomain_and_injective l).2.2 (GlobalTheory.T.algebraMap_ainfInvPrime_bdRPlus_injective l h1)

variable {l : ℕ} [Fact l.Prime] (K : FinExt l)

theorem eq_zero_of_inC_mul {a : Ainf l} (ha : a ≠ 0) {z : CK K} (h : inC K (aC l a) * z = 0) : z = 0 := by
  haveI := (acris_dom l).1
  have ha' : aC l a ≠ 0 := fun h0 => ha ((acris_dom l).2 (h0.trans (map_zero _).symm))
  rw [← Algebra.smul_def] at h
  exact eq_zero_of_smul_free ha' h

theorem exists_dvd_inA {x : AK K} (hx : x ≠ 0) : ∃ N : Ainf l, N ≠ 0 ∧ ∃ w : AK K, inA K N = x * w := by
  obtain ⟨r, hr, w, hw⟩ := (IsIntegral.of_finite (Ainf l) x).isAlgebraic.exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hx)
  exact ⟨r, hr, w, hw⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (x : AK K), x ≠ 0 → ∀ y : GlobalTheory.AcrisK.BK K,
    toB K (ofA K x) * y = 0 → y = 0 := by
  intro l _ K x hx y hy
  obtain ⟨N, hN, w, hw⟩ := exists_dvd_inA K hx
  obtain ⟨D, z, hz⟩ := exists_pow_mul y
  have h1 : toB K (ofA K x * z) = 0 := by
    rw [map_mul, ← hz, mul_left_comm, hy, mul_zero]
  have h2 : ofA K x * z = 0 := toB_injective K (h1.trans (map_zero _).symm)
  have h3 : inC K (aC l N) * z = 0 := by
    rw [← ofA_inA, hw, map_mul, mul_right_comm, h2, zero_mul]
  have h4 : z = 0 := eq_zero_of_inC_mul K hN h3
  rw [h4, map_zero] at hz
  exact ((isUnit_l K).pow D).mul_right_eq_zero.1 hz

end GlobalTheory.AcrisNZD
