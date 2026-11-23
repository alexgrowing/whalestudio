import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictCrystallineDeRhamFiniteExt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeRhamJumpDescent
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.JumpRestrict

open GlobalTheory.DRFil

variable {l : ℕ} [Fact l.Prime]

theorem algebraMap_inclusion (P : LocPrime l) {K K' : FinExt l} (h : K.1 ≤ K'.1) (c : ↥K.1) :
    algebraMap ↥K'.1 P.R.BdR (IntermediateField.inclusion h c) = algebraMap ↥K.1 P.R.BdR c := rfl

theorem idem_restrict_mul (P : LocPrime l) {K K' LL : FinExt l} (h : K.1 ≤ K'.1)
    (τ : ↥K'.1 →ₐ[ℚ_[l]] ↥LL.1) :
    haveI := K.2; haveI := K'.2
    idem (K := ↥K.1) P.R.BdR (τ.comp (IntermediateField.inclusion h)) * idem (K := ↥K'.1) P.R.BdR τ =
      idem (K := ↥K'.1) P.R.BdR τ := by
  haveI := K.2; haveI := K'.2
  obtain ⟨n, a, c, hrep, h1⟩ := idem_repr (K := ↥K.1) P.R.BdR (τ.comp (IntermediateField.inclusion h))
  have e := exists_smul_idem (K := ↥K'.1) (F := P.R.BdR) τ n a (fun i => IntermediateField.inclusion h (c i))
  simp only [algebraMap_inclusion] at e
  rw [hrep, mul_comm, e]
  simp only [AlgHom.comp_apply] at h1
  rw [h1, one_smul]

theorem multV_restrict : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsDR (P.PD K) ρ → ∀ (τ : ↥K'.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), multV (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) τ a = multV (P.PD K) ρ (τ.comp (IntermediateField.inclusion h)) a := by
  intro l _ P AI T K K' LL h V _ _ _ _ _ ρ hdr τ a
  haveI := K.2; haveI := K'.2; haveI := LL.2
  haveI := (GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T K LL V ρ).1
  obtain ⟨m, d, k, hA⟩ := exists_adapted (P.PD K) (isField_dR T) ρ (filSpans T K LL ρ hdr)
    (τ.comp (IntermediateField.inclusion h))
  have hI := idem_restrict_mul P h τ
  have hA' : Adapted (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) τ
      (fun i => sm ℚ_[l] P.R.BdR ↥LL.1 V (idem P.R.BdR τ) (d i)) k := by
    refine ⟨fun i => ?_, fun r hr i => ?_, fun n y hy => ?_⟩
    · have hm := hA.mem i
      refine ⟨sm_idem_mem_DdRE (P.PD K') _ τ
        (GlobalTheory.Per.TiedRestrict.ddR_le h ρ (Submodule.mem_inf.1 (Submodule.mem_inf.1 hm).1).1), ?_⟩
      refine sm_idem_mem_FilV (P.PD K') τ ?_
      rw [GlobalTheory.JumpDescent.FilV_eq P K K']
      exact (Submodule.mem_inf.1 hm).2
    · have := hA.indep (fun i => r i * idem P.R.BdR τ) (by
        simpa only [sm_mul] using hr) i
      rw [mul_left_comm, hI] at this
      rw [mul_comm]; exact this
    · rw [GlobalTheory.JumpDescent.FilV_eq P K K'] at hy
      obtain ⟨r, hr, hy'⟩ := hA.span n y hy
      refine ⟨r, fun i => ?_, ?_⟩
      · rw [GlobalTheory.JumpDescent.FilV_eq P K K']; exact hr i
      · have e : sm ℚ_[l] P.R.BdR ↥LL.1 V (idem P.R.BdR τ) y = sm ℚ_[l] P.R.BdR ↥LL.1 V (idem P.R.BdR τ)
            (sm ℚ_[l] P.R.BdR ↥LL.1 V (idem P.R.BdR (τ.comp (IntermediateField.inclusion h))) y) := by
          rw [← sm_mul, mul_comm, hI]
        rw [e, hy', map_sum]
        exact Finset.sum_congr rfl fun i _ => sm_comm _ _ _
  rw [hA.multV_eq, hA'.multV_eq]

end GlobalTheory.JumpRestrict
