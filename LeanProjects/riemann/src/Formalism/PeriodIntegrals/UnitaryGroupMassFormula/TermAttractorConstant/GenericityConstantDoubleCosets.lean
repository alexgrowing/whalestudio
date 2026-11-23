import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermAttractorConstant.GeneratorMemLocalLatticeBackward
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermAttractorConstant.RelevanceConstantDoubleCosets

noncomputable section

open scoped Classical

set_option linter.style.haveILetI false

namespace PI.TermAttrConst.UnitaryGroupMassFormula

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.DCRelEquiv PI.DCRelEquiv.UnitaryGroupMassFormula
  IsDedekindDomain

section GenAll

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem gen_fwd {Λ : Submodule (𝓞 E) S.V} {g : ℕ} {F : LFlag S r T} {x y : LFlag S r T'}
    (hFl : IsLift Λ F) (hFc : IsFixedConv Λ g F) (hxl : IsLift Λ x) (hxc : IsFixedConv Λ g x)
    (hyc : IsFixedConv Λ g y) (hya : IsAdmissible Λ g F y) (hxy : DCRel Λ F x y)
    (hgx : IsGeneric Λ g F x) : IsGeneric Λ g F y := by
  obtain ⟨ξ', hξ'⟩ := hya
  obtain ⟨n, hn, m, hm, hfr, hzt⟩ := hxy
  obtain ⟨ξ, hξ, hgx⟩ := hgx
  refine ⟨ξ', hξ', fun P => ?_⟩
  haveI := P.isPrime
  have hB := locP_BLat_transport hFl hxl hn hm hfr hzt P.asIdeal
  constructor
  · intro hP
    rw [hB, (hgx P).1 hP, ← locP_gmap]
    exact (gp_mplus P hFl hFc hxl hxc hyc hn hm hfr hξ hξ' hP).symm
  · intro hP
    rw [hB, (hgx P).2 hP, ← locP_gmap, UU_transport hFl hxl hn hm hfr hzt]

theorem genFun_gen (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (Pc : LFlag S r T' → Prop) (g : ℕ)
    (hFl : IsLift Λ F) (hFc : IsFixedConv Λ g F)
    (hPc : ∀ x, Pc x → IsLift Λ x ∧ IsAdmissible Λ g F x ∧ IsFixedConv Λ g x) :
    GenFun Λ F Pc g := by
  intro x y hxy
  have hxy' : DCRel Λ F x.1 y.1 := hxy
  obtain ⟨hxl, hxa, hxc⟩ := hPc x.1 x.2
  obtain ⟨hyl, hya, hyc⟩ := hPc y.1 y.2
  have hyx : DCRel Λ F y.1 x.1 := (dCRelEquivAll_holds E S r T T' Λ F).symm hxy'
  exact ⟨gen_fwd hFl hFc hxl hxc hyc hya hxy', gen_fwd hFl hFc hyl hyc hxc hxa hyx⟩

end GenAll

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem genericity_constant_double_cosets : GenericityConstantDoubleCosets := by
  intro D u u' F0 Λ hΛ
  obtain ⟨-, ⟨-, -, hFl, hFc⟩, -⟩ := hΛ
  exact genFun_gen Λ (lf D F0) _ (gS D) hFl hFc fun x hx => ⟨hx.1, hx.2.1, hx.2.2.1⟩

end D7

end PI.TermAttrConst.UnitaryGroupMassFormula
