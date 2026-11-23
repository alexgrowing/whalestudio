import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.OrthLoc

variable {D : D7}

theorem localForm_add_left (Z : LocDat D) (p : PlF D) (x y z : Vp D p) :
    LocFacts₂ Z.M p (x + y) z = LocFacts₂ Z.M p x z + LocFacts₂ Z.M p y z := by
  simp only [LocFacts₂, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem localForm_smul_left (Z : LocDat D) (p : PlF D) (c : (D.s.atP p).Ep) (x z : Vp D p) :
    LocFacts₂ Z.M p (c • x) z = c * LocFacts₂ Z.M p x z := by
  simp only [LocFacts₂, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

def orthP (Z : LocDat D) (p : PlF D) (U : Submodule D.host.E (VS D).V) :
    Submodule (D.s.atP p).Ep (Vp D p) where
  carrier := {v | ∀ u ∈ U, LocFacts₂ Z.M p v (baseChange₂ D p u) = 0}
  zero_mem' := by intro u _; simp [LocFacts₂]
  add_mem' := by intro a b ha hb u hu; rw [localForm_add_left, ha u hu, hb u hu, add_zero]
  smul_mem' := by intro c a ha u hu; rw [localForm_smul_left, ha u hu, mul_zero]

theorem span_orth_le (Z : LocDat D) (p : PlF D) (U : Submodule D.host.E (VS D).V) :
    Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (orth (VS D) U : Set (VS D).V)) ≤ orthP Z p U := by
  rw [Submodule.span_le]
  rintro _ ⟨a, ha, rfl⟩ u hu
  have ha' : (VS D).hT u a = 0 := by
    have ha2 : a ∈ orth (VS D) U := ha
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at ha2
    exact ha2 u hu
  rw [baseChangeAt_form Z.M p (Z.hcj p)]
  simp [brS, ha']

theorem mem_localLattice_inf_orthogonal : ∀ (D : D7) (Z : LocDat D) (U : Submodule D.host.E (VS D).V),
    (∀ x : (VS D).V, ∃ a ∈ orth (VS D) U, ∃ b ∈ U, x = a + b) →
    (∀ (p : PlF D) (v : Vp D p), v ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) →
      (∀ u ∈ U, LocFacts₂ Z.M p v (baseChange₂ D p u) = 0) → v = 0) →
    ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → ∀ (p : PlF D) (t : Vp D p), t ∈ lattice₂ D Z.M p Λ →
      (∀ u ∈ U, LocFacts₂ Z.M p t (baseChange₂ D p u) = 0) → t ∈ lattice₂ D Z.M p (Λ ⊓ toO (VS D) (orth (VS D) U)) := by
  intro D Z U hdec huniq Λ hΛ p t ht horth
  have hsat := Formalism.L2.SG.Pf.locSatC_holds D Z p Λ (orth (VS D) U) hΛ.fg
  have hmem : t ∈ (lattice₂ D Z.M p (Λ ⊓ toO (VS D) (orth (VS D) U)) : Set (Vp D p)) := by
    rw [hsat]
    refine ⟨ht, ?_⟩
    have htop : Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (orth (VS D) U : Set (VS D).V)) ⊔
        Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) = ⊤ := by
      rw [eq_top_iff, ← span_baseChange_eq_top (D := D) p, Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := hdec x
      rw [map_add]
      exact Submodule.add_mem_sup (Submodule.subset_span ⟨a, ha, rfl⟩) (Submodule.subset_span ⟨b, hb, rfl⟩)
    have ht' : t ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (orth (VS D) U : Set (VS D).V)) ⊔
        Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) := htop ▸ Submodule.mem_top
    obtain ⟨α, hα, β, hβ, hαβ⟩ := Submodule.mem_sup.1 ht'
    have hβ0 : β = 0 := by
      apply huniq p β hβ
      have e : β = t - α := by rw [← hαβ]; abel
      have hto : t ∈ orthP Z p U := horth
      have h2 := (orthP Z p U).sub_mem hto (span_orth_le Z p U hα)
      rw [← e] at h2
      exact h2
    rw [← hαβ, hβ0, add_zero]
    exact hα
  exact hmem

end GlobalTheory.Unfold.OrthLoc
