import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DualCountBound.BoundBB

noncomputable section

open scoped Classical
open ValuativeRel

namespace PI.NGStepBBW

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.L2.SG.NGDict

section Mod

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def toO (M : Model F E) : 𝒪[F] →+* M.L.O where
  toFun x := ⟨algebraMap F E (x : F), (M.L.O_def _).2 (isIntegral_algebraMap (x := x))⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

@[simp] lemma toO_coe (M : Model F E) (x : 𝒪[F]) : ((toO M x : M.L.O) : E) = algebraMap F E (x : F) := rfl

variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

def bbMod (t : Term V M r) : Module 𝒪[F] (BB H t) := Module.compHom _ (toO M)

def iSub (t : Term V M r) : @Submodule 𝒪[F] (BB H t) _ _ (bbMod H t) :=
  letI := bbMod H t
  { carrier := Iset H t
    zero_mem' := ⟨0, 0, 0, 0, by simp, Submodule.zero_mem _, Submodule.zero_mem _, Submodule.zero_mem _,
      by simpa using t.abelian₂.zero_mem, by simpa using t.abelian₂.zero_mem, by simp⟩
    add_mem' := by
      rintro _ _ ⟨y₁, w₁, l₁, l₁', rfl, hw₁, hl₁, hl₁', h₁, h₁', e₁⟩ ⟨y₂, w₂, l₂, l₂', rfl, hw₂, hl₂, hl₂', h₂, h₂', e₂⟩
      refine ⟨y₁ + y₂, w₁ + w₂, l₁ + l₂, l₁' + l₂', by simp, Submodule.add_mem _ hw₁ hw₂,
        Submodule.add_mem _ hl₁ hl₂, Submodule.add_mem _ hl₁' hl₂', ?_, ?_, ?_⟩
      · have := t.abelian₂.add_mem h₁ h₂
        convert this using 1; abel
      · have := t.abelian₂.add_mem h₁' h₂'
        convert this using 1; abel
      · simp only [Submodule.coe_add, smul_add, e₁, e₂]; abel
    smul_mem' := by
      rintro a _ ⟨y, w, l, l', rfl, hw, hl, hl', h, h', e⟩
      refine ⟨toO M a • y, algebraMap F E (a : F) • w, algebraMap F E (a : F) • l,
        algebraMap F E (a : F) • l', rfl, Submodule.smul_mem _ _ hw, Submodule.smul_mem _ _ hl,
        Submodule.smul_mem _ _ hl', ?_, ?_, ?_⟩
      · have := t.abelian₂.smul_mem (toO M a) h
        rw [Submonoid.smul_def, toO_coe, smul_add] at this
        exact this
      · have := t.abelian₂.smul_mem (toO M a) h'
        rw [Submonoid.smul_def, toO_coe, smul_add] at this
        exact this
      · rw [Submodule.coe_smul, Submonoid.smul_def, toO_coe, smul_comm, e, smul_sub] }

end Mod

end PI.NGStepBBW
