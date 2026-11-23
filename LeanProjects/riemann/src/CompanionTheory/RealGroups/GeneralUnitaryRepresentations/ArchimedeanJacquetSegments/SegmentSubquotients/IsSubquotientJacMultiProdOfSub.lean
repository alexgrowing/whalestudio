import Mathlib
import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SegTwo
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ZelevinskyClassification.ZelevinskySegments.SegDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EquivOfMultiplicityOneUniqueFactor
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.GlobalTheory.BernsteinZelevinskyFiniteness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetQuotientEigenvector
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import CompanionTheory.AutomorphicTheory.SegmentRepresentations.IrreducibleSegments.IsIrreduciblePiTensorSegTerm

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace CompanionTheory.Pf1.SegRepC.Lift

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSmooth_multiProd_segTerm {d : ℕ} (σ : IrrRep (GL (Fin d) k)) (l : ℕ) :
    IsSmooth (multiProd (consecBlocks l d) (segTerm σ.ρ l)) :=
  isSmooth_parInd _ _

set_option synthInstance.maxHeartbeats 400000 in

theorem isSubquotient_jac_multiProd_of_sub {d l : ℕ} (σ : IrrRep (GL (Fin d) k))
    (S : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)))
    {X : Type} [AddCommGroup X] [Module ℂ X] {π : Representation ℂ (Levi k fun _ : Fin l => Fin d) X}
    (h : IsSubquotient π (jac (consecBlocks l d) S.toRepresentation)) :
    IsSubquotient π (jac (consecBlocks l d) (multiProd (consecBlocks l d) (segTerm σ.ρ l))) :=
  h.trans (GlobalTheory.JacquetExact.isSubquotient_jac (d := fun _ => d) (consecBlocks l d)
    (isSmooth_multiProd_segTerm σ l)
    (IsSubquotient.of_injective ⟨S.toSubmodule.subtype, fun _ => rfl⟩ Subtype.val_injective))

theorem perm_eq_one_of_lt_succ {l : ℕ} (w : Equiv.Perm (Fin l))
    (h : ∀ (i : ℕ) (hi : i + 1 < l), w.symm ⟨i, by omega⟩ < w.symm ⟨i + 1, hi⟩) : w = 1 := by
  cases l with
  | zero => exact Subsingleton.elim _ _
  | succ n =>
    have hm : StrictMono w.symm := Fin.strictMono_iff_lt_succ.2 fun i => h i.1 (by omega)
    have he : ∀ y, w.symm y = y := fun y => by
      have := congrArg (fun e : Fin (n + 1) ≃o Fin (n + 1) => e y)
        (Subsingleton.elim (hm.orderIsoOfSurjective _ w.symm.surjective) (OrderIso.refl _))
      simpa using this
    ext x
    have hx := he (w x)
    simp only [Equiv.symm_apply_apply] at hx
    simp [← hx]

end CompanionTheory.Pf1.SegRepC.Lift

end
