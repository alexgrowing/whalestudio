import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.MemLocFrom

noncomputable section

namespace PI.FinKW

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)
open Formalism.L2.SG.AdBridge

theorem psiV_tauF (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) :
    psiV I v (tauF I z) =
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F v) (AlgHom.id I.F I.E) (prF I z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [tauF_tmul]
    simp only [psiV, prF, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, Algebra.TensorProduct.comm_tmul,
      Algebra.TensorProduct.map_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem vecV_mulVec (I : AutInst) (h : HAd I) (v : HeightOneSpectrum (𝓞 I.F))
    (x : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) :
    vecV I v (ofHAFin I h *ᵥ x) =
      ((Formalism.L2.SG.Sub.compV v (Formalism.UG.bc (prF I)
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J h)) :
          GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) : Matrix _ _ _) *ᵥ vecV I v x := by
  funext i
  simp only [vecV]
  have := RingHom.map_mulVec (psiV I v).toRingHom (ofHAFin I h) x i
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
  rw [this]
  congr 1
  ext a b
  simp [ofHAFin, Formalism.L2.SG.Sub.compV, Formalism.UG.bc, psiV_tauF]

theorem finK_of (hT : MemLocTo) (hF : MemLocFrom) (hS : LiftV) : PI.AdBridgeSteps.FinK := by
  intro I h
  have hL : ∀ x, x ∈ I.Lf ↔ ∀ v, vecV I v x ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) :=
    fun x => ⟨hT I x, hF I x⟩
  constructor
  · intro hst v y
    obtain ⟨x, hxv, hxw⟩ := hS I v y
    have ex : x ∈ I.Lf ↔ y ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by
      rw [hL x]
      constructor
      · intro H
        have := H v
        rwa [hxv] at this
      · intro H w
        by_cases hw : w = v
        · subst hw
          rwa [hxv]
        · rw [hxw w hw]
          exact zero_mem _
    have egx : ofHAFin I h *ᵥ x ∈ I.Lf ↔
        ((Formalism.L2.SG.Sub.compV v (Formalism.UG.bc (prF I)
          (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J h)) :
            GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) : Matrix _ _ _) *ᵥ y ∈
          Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by
      rw [hL]
      constructor
      · intro H
        have := H v
        rwa [vecV_mulVec, hxv] at this
      · intro H w
        rw [vecV_mulVec]
        by_cases hw : w = v
        · subst hw
          rwa [hxv]
        · rw [hxw w hw, Matrix.mulVec_zero]
          exact zero_mem _
    exact ex.symm.trans ((hst x).trans egx)
  · intro hK x
    rw [hL x, hL (ofHAFin I h *ᵥ x)]
    refine forall_congr' fun v => ?_
    rw [vecV_mulVec]
    exact hK v (vecV I v x)

end PI.FinKW
