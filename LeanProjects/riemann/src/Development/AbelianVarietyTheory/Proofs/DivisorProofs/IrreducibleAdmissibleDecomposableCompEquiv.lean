import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.CuspMult

section
variable {H H' : Type} [Group H] [Group H'] {X : Type} [AddCommGroup X] [Module ℂ X]

def subrepCompIso (ρ : Representation ℂ H' X) (φ : H ≃* H') :
    Subrepresentation (ρ.comp φ.toMonoidHom : Representation ℂ H X) ≃o Subrepresentation ρ where
  toFun U := ⟨U.toSubmodule, fun g v hv => by
    have h := U.apply_mem_toSubmodule (φ.symm g) hv
    simpa using h⟩
  invFun U := ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule (φ g) hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_comp_mulEquiv (ρ : Representation ℂ H' X) (φ : H ≃* H') (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp φ.toMonoidHom : Representation ℂ H X) := by
  haveI : IsSimpleOrder (Subrepresentation ρ) := h
  exact (subrepCompIso ρ φ).isSimpleOrder

theorem isAdmissible_comp_equiv [TopologicalSpace H] [TopologicalSpace H'] (ρ : Representation ℂ H' X) (Φ : H ≃ₜ* H')
    (h : GlobalTheory.PRep.IsAdmissible ρ) :
    GlobalTheory.PRep.IsAdmissible (ρ.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ H X) := by
  refine ⟨fun v => (h.1 v).preimage Φ.continuous, fun K hKo hKc => ?_⟩
  have e : GlobalTheory.PRep.fixed (ρ.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ H X) K =
      GlobalTheory.PRep.fixed ρ (K.map Φ.toMulEquiv.toMonoidHom) := by
    ext v
    constructor
    · rintro hv ⟨_, g, hg, rfl⟩
      exact hv ⟨g, hg⟩
    · intro hv g
      exact hv ⟨_, g.1, g.2, rfl⟩
  rw [e]
  exact h.2 _ (Φ.toHomeomorph.isOpenMap _ hKo) (hKc.image Φ.continuous)

end

theorem isDecomp_comp_equiv : ∀ (H H' : Type) [Group H] [TopologicalSpace H] [Group H'] [TopologicalSpace H'] (X : Type)
    [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ H' X) (C : Submodule ℂ X) (Φ : H ≃ₜ* H'),
    IsDecomp ρ C → IsDecomp (ρ.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ H X) C := by
  intro H H' _ _ _ _ X _ _ ρ C Φ h x hx ho
  have ho' : IsOpen {g : H' | ρ g x = x} := by
    have := ho.preimage Φ.symm.continuous
    convert this using 1
    ext g
    show ρ g x = x ↔ ρ (Φ (Φ.symm g)) x = x
    rw [Φ.apply_symm_apply]
  have hm := h x hx ho'
  refine (?_ : irrSum ρ C ≤ irrSum (ρ.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ H X) C) hm
  refine iSup₂_le fun U hU => ?_
  refine le_iSup₂_of_le (f := fun (U : Subrepresentation (ρ.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ H X))
    (_ : U.toSubmodule ≤ C ∧ U.toRepresentation.IsIrreducible ∧ GlobalTheory.PRep.IsAdmissible U.toRepresentation) => U.toSubmodule)
    ((subrepCompIso ρ Φ.toMulEquiv).symm U) ⟨hU.1, ?_, ?_⟩ le_rfl
  · exact isIrreducible_comp_mulEquiv U.toRepresentation Φ.toMulEquiv hU.2.1
  · exact isAdmissible_comp_equiv U.toRepresentation Φ hU.2.2

end GlobalTheory.CuspMult
