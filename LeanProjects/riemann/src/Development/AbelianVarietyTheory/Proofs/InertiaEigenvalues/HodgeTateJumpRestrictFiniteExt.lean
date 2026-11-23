import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictCrystallineDeRhamFiniteExt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeRhamJumpDescent

open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Per.JumpRestrict

open GlobalTheory.DRFil

theorem jump_restrict : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K K' LL : FinExt l) (hle : K.1 ≤ K'.1) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsCrys (P.PD K) ρ → ∀ (τ' : ↥K'.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), IsJumpV (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le hle))) τ' a → IsJumpV (P.PD K) ρ (τ'.comp (IntermediateField.inclusion hle)) a := by
  intro l _ P AI T K K' LL hle V _ _ _ _ _ ρ hc τ' a hj
  have := K.2
  have := K'.2
  have := LL.2
  set τ := τ'.comp (IntermediateField.inclusion hle) with hτ
  have hF := isField_dR T
  haveI := (GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T K LL V ρ).1
  obtain ⟨m, d, k, hA⟩ := exists_adapted (P.PD K) hF ρ (filSpans T K LL ρ (crys T K LL ρ hc).1) τ
  set e' := idem (K := ↥K'.1) P.R.BdR (LL := ↥LL.1) τ' with he'
  set e := idem (K := ↥K.1) P.R.BdR (LL := ↥LL.1) τ with he
  have hee : e' * e = e' := by
    obtain ⟨n, x, c, hc1, hc2⟩ := idem_repr (K := ↥K.1) P.R.BdR τ
    rw [he, hc1]
    have := exists_smul_idem (K := ↥K'.1) (F := P.R.BdR) τ' n x (fun i => IntermediateField.inclusion hle (c i))
    exact (this.trans (by rw [← hc2]; rfl)).trans (one_smul _ _)
  have hA' : Adapted (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le hle))) τ'
      (fun i => sm ℚ_[l] P.R.BdR ↥LL.1 V e' (d i)) k := by
    refine ⟨fun i => ⟨?_, ?_⟩, fun r hr i => ?_, fun n y hy => ?_⟩
    · exact sm_idem_mem_DdRE (P.PD K') _ τ' (GlobalTheory.Per.TiedRestrict.ddR_le hle ρ (hA.mem i).1.1)
    · refine sm_idem_mem_FilV (P.PD K') τ' ?_
      rw [GlobalTheory.JumpDescent.FilV_eq P K K']
      exact (hA.mem i).2
    · have h1 := hA.indep (fun i => r i * e') (by
        rw [← hr]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [sm_mul])
      calc e' * r i = (e' * e) * r i := by rw [hee]
        _ = e * (r i * e') := by ring
        _ = 0 := h1 i
    · rw [GlobalTheory.JumpDescent.FilV_eq P K K'] at hy
      obtain ⟨r, hr, hy'⟩ := hA.span n y hy
      refine ⟨r, fun i => ?_, ?_⟩
      · rw [GlobalTheory.JumpDescent.FilV_eq P K K']
        exact hr i
      · have h2 : sm ℚ_[l] P.R.BdR ↥LL.1 V e' y =
            sm ℚ_[l] P.R.BdR ↥LL.1 V e' (sm ℚ_[l] P.R.BdR ↥LL.1 V e y) := by
          rw [← sm_mul, hee]
        rw [h2, hy', map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [sm_comm]
  rw [hA'.isJumpV_iff] at hj
  exact hA.isJumpV_iff a |>.2 hj

end GlobalTheory.Per.JumpRestrict
