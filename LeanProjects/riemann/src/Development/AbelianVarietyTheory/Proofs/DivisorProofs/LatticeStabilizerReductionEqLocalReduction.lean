import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCO
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGLintOfEntries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlacesApart
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties

namespace ReductionComponent
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.CompanionTheory.RedComp

variable {D : D7}

theorem val_lt_one_iff (PP : Pl D.host.E) (x : Kw PP) :
    valuation (Kw PP) x < 1 ↔ Valued.v x < 1 := by
  haveI : (Valued.v : Valuation (Kw PP) _).Compatible := Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (valuation (Kw PP)) Valued.v).lt_one_iff_lt_one

theorem cpt_oToS (PP : Pl D.host.E) (a : 𝓞 D.host.E) :
    cpt PP ((oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) =
      algebraMap D.host.E (Kw PP) (a : D.host.E) := by
  have h : toAd D ((algebraMap (𝓞 D.host.E) D.host.E a) ⊗ₜ[D.host.F] (1 : Af D.host.F)) = _ :=
    GlobalTheory.AdeleBaseChange.map_tmul_one (toAd_spec D) _
  show (Formalism.UG.evalV D.host.E PP) (toAd D ((algebraMap (𝓞 D.host.E) D.host.E a) ⊗ₜ[D.host.F] (1 : Af D.host.F))) = _
  rw [h]
  rfl

theorem v_algebraMap_lt_one_iff (PP : Pl D.host.E) (a : 𝓞 D.host.E) :
    Valued.v (algebraMap D.host.E (Kw PP) (a : D.host.E)) < 1 ↔ a ∈ PP.asIdeal := by
  have h : Valued.v (algebraMap D.host.E (Kw PP) (a : D.host.E)) = PP.valuation D.host.E (a : D.host.E) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' PP _
  rw [h]
  exact PP.valuation_lt_one_iff_mem a

def ballIdeal (PP : Pl D.host.E) : Ideal (Formalism.L2.Herm.intAf D.host.F D.host.E) where
  carrier := {s | Valued.v (cpt PP ((s : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D)) < 1}
  add_mem' := by
    intro s t hs ht
    show Valued.v (cpt PP (((s + t : Formalism.L2.Herm.intAf D.host.F D.host.E)) : Lev.EAf D)) < 1
    rw [Subring.coe_add, map_add]
    exact Valuation.map_add_lt _ hs ht
  zero_mem' := by
    show Valued.v (cpt PP (((0 : Formalism.L2.Herm.intAf D.host.F D.host.E)) : Lev.EAf D)) < 1
    simp
  smul_mem' := by
    intro c s hs
    show Valued.v (cpt PP (((c * s : Formalism.L2.Herm.intAf D.host.F D.host.E)) : Lev.EAf D)) < 1
    have hc : Valued.v (cpt PP ((c : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D)) ≤ 1 := (mem_OA_iff _).1 c.2 PP
    rw [Subring.coe_mul, map_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hc) hs

theorem idS_le_ballIdeal (PP : Pl D.host.E) : idS D.host.F PP.asIdeal ≤ ballIdeal PP := by
  refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
  show Valued.v (cpt PP ((oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D)) < 1
  rw [cpt_oToS]
  exact (v_algebraMap_lt_one_iff PP a).2 ha

theorem mem_idS_of_resS_eq_zero (PP : Pl D.host.E) (s : Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h : resS D.host.F PP s = 0) : s ∈ idS D.host.F PP.asIdeal := by
  unfold resS at h
  rw [RingHom.comp_apply] at h
  have h2 : (RingEquiv.ofBijective (cmpS D.host.F PP.asIdeal) (cmpS_bij (F := D.host.F) PP.asIdeal PP.ne_bot)).symm
      (Ideal.Quotient.mk (idS D.host.F PP.asIdeal) s) = 0 := h
  have h3 := (RingEquiv.symm_apply_eq _).1 h2
  rw [map_zero] at h3
  exact Ideal.Quotient.eq_zero_iff_mem.1 h3

theorem resS_eq_mk_iff (PP : Pl D.host.E) (z : Formalism.L2.Herm.intAf D.host.F D.host.E) (a : 𝓞 D.host.E) :
    resS D.host.F PP z = Ideal.Quotient.mk PP.asIdeal a ↔
      Valued.v (cpt PP ((z : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) - algebraMap D.host.E (Kw PP) (a : D.host.E)) < 1 := by
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (resS D.host.F PP z)
  have h0 : resS D.host.F PP (z - oToS D.host.F D.host.E b) = 0 := by
    rw [map_sub, resS_oToS, hb, sub_self]
  have hv : Valued.v (cpt PP ((z : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) - algebraMap D.host.E (Kw PP) (b : D.host.E)) < 1 := by
    have h1 := idS_le_ballIdeal PP (mem_idS_of_resS_eq_zero PP _ h0)
    have h2 : Valued.v (cpt PP (((z - oToS D.host.F D.host.E b : Formalism.L2.Herm.intAf D.host.F D.host.E)) : Lev.EAf D)) < 1 := h1
    rwa [AddSubgroupClass.coe_sub, map_sub, cpt_oToS] at h2
  have hba : Valued.v (algebraMap D.host.E (Kw PP) ((b - a : 𝓞 D.host.E) : D.host.E)) < 1 ↔
      resS D.host.F PP z = Ideal.Quotient.mk PP.asIdeal a := by
    rw [v_algebraMap_lt_one_iff, ← hb, Ideal.Quotient.eq]
  have hsub : algebraMap D.host.E (Kw PP) ((b - a : 𝓞 D.host.E) : D.host.E) =
      algebraMap D.host.E (Kw PP) (b : D.host.E) - algebraMap D.host.E (Kw PP) (a : D.host.E) := by
    rw [← map_sub]; rfl
  rw [← hba, hsub]
  constructor
  · intro h
    have := Valuation.map_add_lt _ hv h
    rwa [sub_add_sub_cancel] at this
  · intro h
    have h3 := Valuation.map_sub_lt (v := Valued.v) h hv
    rwa [sub_sub_sub_cancel_left] at h3

theorem redFn_entry_eq_mk_iff : ∀ {D : D7} {n : ℕ} (β x : GL (Fin n) (Lev.EAf D)) (PP : Pl D.host.E), x ∈ St β → ∀ (i j : Fin n) (a : 𝓞 D.host.E), ((redFn β PP x : GL (Fin n) (kP PP)) : Matrix (Fin n) (Fin n) (kP PP)) i j = Ideal.Quotient.mk PP.asIdeal a ↔ valuation (Kw PP) ((inBasis rfl β PP x).1 i j - algebraMap D.host.E (Kw PP) (a : D.host.E)) < 1 := by
  intro D n β x PP hx i j a
  obtain ⟨y, rfl⟩ := hx
  have e1 : β⁻¹ * Formalism.L2.DIV.frGL β y * β = Formalism.L2.DIV.intGL _ _ n y := by
    simp only [Formalism.L2.DIV.frGL, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply]
    group
  rw [redFn_frGL, inBasis_apply, e1, val_lt_one_iff]
  exact resS_eq_mk_iff PP (y.1 i j) a

end GlobalTheory.CompanionTheory.RedComp

end
end

end ReductionComponent
section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

theorem _root_.GlobalTheory.Adopt.latticeStabilizer_reduction_eq_local_reduction : ∀ {D : D7} {n : ℕ} (β x : GL (Fin n) (Lev.EAf D)) (PP : Pl D.host.E), x ∈ St β → ∀ (i j : Fin n) (a : 𝓞 D.host.E), ((redFn β PP x : GL (Fin n) (kP PP)) : Matrix (Fin n) (Fin n) (kP PP)) i j = Ideal.Quotient.mk PP.asIdeal a ↔ valuation (Kw PP) ((inBasis rfl β PP x).1 i j - algebraMap D.host.E (Kw PP) (a : D.host.E)) < 1 := by
  first | exact @ReductionComponent.GlobalTheory.CompanionTheory.RedComp.redFn_entry_eq_mk_iff | exact ReductionComponent.GlobalTheory.CompanionTheory.RedComp.redFn_entry_eq_mk_iff | (intros; apply ReductionComponent.GlobalTheory.CompanionTheory.RedComp.redFn_entry_eq_mk_iff <;> assumption)

end
end
