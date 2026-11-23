import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.ProdShiftEeVOfCapelli
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.Central
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.HcVOfCentralChar

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

theorem scalar_genSub {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M)
    (A : Module.End ℂ M) (hA : ∀ a b, Commute (E a b) A) (c : ℂ) (V : Submodule ℂ M)
    (hV : ∀ y ∈ V, A y = c • y) : ∀ y ∈ genSub E V, A y = c • y := by
  intro y hy
  have hle : genSub E V ≤ LinearMap.ker (A - c • (1 : Module.End ℂ M)) := by
    refine sInf_le ⟨fun v hv => ?_, fun a b v hv => ?_⟩
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hV v hv,
        sub_self]
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hv ⊢
      rw [← Module.End.mul_apply, ← (hA a b).eq, Module.End.mul_apply, sub_eq_zero.1 hv, map_smul,
        sub_self]
  have hy' := hle hy
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    sub_eq_zero] at hy'
  exact hy'

theorem standardKType_of_centralChar (n : ℕ) (hCC : CentralCharStatement n) : LowestKTypeEulerTensorStandard n := by
  intro ε lam h H _ _ _ σ D E V hσ hD hV hcas hVK hint hanti hgap hp hq f hf

  have hcV : ∀ ω : ℂ, ∀ y ∈ V, Capelli.capelliC E ω y = (∏ t, (ω + ((thV lam t : ℝ) : ℂ))) • y :=
    fun ω y hy => hcV_of_centralChar n hCC ε lam h H σ D E V hσ hD hV hcas hVK hint hanti hgap hp hq ω y hy
  exact prodShift_eeV_of_capelli' E hD.glRep (thV lam) (genSub E V)
    (fun ω => scalar_genSub E _ (fun a b => Capelli.capelliC_central E hD.glRep ω a b) _ V (hcV ω)) f hf

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
