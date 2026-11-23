import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.IdxProd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.HelpSng
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.LocIdxLift

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct Matrix

theorem mem_stabT_of_comp (I : Formalism.MainNotions.S.AutInst) (h : HA (Af I.F) I.cm.sig I.J) {a : ℕ}
    (X0 : Fin a → Fin I.n → I.E)
    (hc : ∀ v, PI.MassDataKppVolLemmas.piV I v h ∈ stabT (Fv I.F v) I.cm.sig I.J X0) :
    h ∈ stabT (Af I.F) I.cm.sig I.J X0 := by
  rw [mem_stabT]
  intro b
  funext i
  rw [← sub_eq_zero]
  apply PI.MassDataKppVolLemmas.LocIdxLift_inj I
  intro v
  have hv := hc v
  rw [mem_stabT] at hv
  have e1 : ratV (F := I.F) (Fv I.F v) (X0 b) =
      (PI.MassDataKppVolLemmas.tV I v) ∘ ratV (F := I.F) (Af I.F) (X0 b) := by
    funext j
    simp [ratV, PI.MassDataKppVolLemmas.tV, tensMap_inclR]
  have h2 := congrFun (hv b) i
  rw [map_sub]
  show PI.MassDataKppVolLemmas.tV I v ((((HA.mat (Af I.F) I.cm.sig I.J h : GL (Fin I.n) (Af I.F ⊗[I.F] I.E)) :
      Matrix (Fin I.n) (Fin I.n) (Af I.F ⊗[I.F] I.E)) *ᵥ ratV (F := I.F) (Af I.F) (X0 b)) i) -
    PI.MassDataKppVolLemmas.tV I v (ratV (F := I.F) (Af I.F) (X0 b) i) = 0
  rw [RingHom.map_mulVec, ← e1]
  have e2 : ((HA.mat (Af I.F) I.cm.sig I.J h : GL (Fin I.n) (Af I.F ⊗[I.F] I.E)) :
      Matrix (Fin I.n) (Fin I.n) (Af I.F ⊗[I.F] I.E)).map (PI.MassDataKppVolLemmas.tV I v) =
      ((HA.mat (Fv I.F v) I.cm.sig I.J (PI.MassDataKppVolLemmas.piV I v h) : GL (Fin I.n) (Fv I.F v ⊗[I.F] I.E)) :
        Matrix (Fin I.n) (Fin I.n) (Fv I.F v ⊗[I.F] I.E)) := rfl
  rw [e2]
  have e3 : PI.MassDataKppVolLemmas.tV I v (ratV (F := I.F) (Af I.F) (X0 b) i) = ratV (F := I.F) (Fv I.F v) (X0 b) i := by
    rw [e1]; rfl
  rw [e3, sub_eq_zero]
  exact h2

variable {D : D7}

theorem level_components_surjective : SurjH := by
  classical
  intro D X hb _hK u _hT _hL f
  have key : ∀ S : Finset (TypX X), ∃ z : Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u),
      z ∈ KHg X u ∧ ∀ p : TypX X, ((piH X u p.1 z : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) :
        HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) =
        if p ∈ S then (((f p : KvH X u p.1) : Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) :
          HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) else 1 := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1, one_mem _, fun p => by simp⟩
    | insert q S hq ih =>
      obtain ⟨z, hzK, hz⟩ := ih
      set k : HA (Fv X.B.I.F q.1) X.B.I.cm.sig X.B.I.J :=
        (((f q : KvH X u q.1) : Hsub (Fv X.B.I.F q.1) X.B.I.cm.sig X.B.I.J (frameOf X u)) :
          HA (Fv X.B.I.F q.1) X.B.I.cm.sig X.B.I.J) with hk
      have hkK : k ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) q.1 := (f q).2
      have hkH : k ∈ Hsub (Fv X.B.I.F q.1) X.B.I.cm.sig X.B.I.J (frameOf X u) := (f q : KvH X u q.1).1.2
      obtain ⟨h, hKf, hq1, hq2⟩ := PI.MassDataKppVolLemmas.single_component_surjective X.B.I q.1 k hkK
      have hH : h ∈ Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) := by
        apply mem_stabT_of_comp X.B.I h
        intro v
        by_cases hv : v = q.1
        · subst hv; rw [hq1]; exact hkH
        · rw [hq2 v hv]; exact one_mem _
      refine ⟨⟨h, hH⟩ * z, ?_, fun p => ?_⟩
      · show (h : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) * (z : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈
          Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))
        exact mul_mem hKf hzK
      · rw [map_mul, Subgroup.coe_mul, hz p]
        show PI.MassDataKppVolLemmas.piV X.B.I p.1 h * _ = _
        by_cases hpq : p = q
        · subst hpq
          rw [if_neg hq, if_pos (Finset.mem_insert_self p S), mul_one, hq1]
        · have hp1 : p.1 ≠ q.1 := fun e => hpq (Subtype.ext e)
          rw [hq2 p.1 hp1, one_mul]
          by_cases hpS : p ∈ S
          · rw [if_pos hpS, if_pos (Finset.mem_insert_of_mem hpS)]
          · rw [if_neg hpS, if_neg]
            intro hm
            rcases Finset.mem_insert.1 hm with e | e
            · exact hpq e
            · exact hpS e
  obtain ⟨z, hzK, hz⟩ := key Finset.univ
  refine ⟨z, hzK, fun p => Subtype.ext (Subtype.ext ?_)⟩
  rw [hz p, if_pos (Finset.mem_univ p)]

end PIW.MassDataColumns
