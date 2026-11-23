import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.OneCoset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLInvolutive

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Bc.ArchbcB.B.M4

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem nrmL_twconj (w : Pl E) (hw : ¬ IsSplitAt w) (a : ℕ) (g δ : GLw a w) :
    nrmL a w (g⁻¹ * δ * thL a w g) = g⁻¹ * nrmL a w δ * g := by
  have ht : ∀ y : GLw a w, nrmL a w y = y * thL a w y := fun y => by
    unfold nrmL thL
    rw [if_neg hw, if_neg hw]
  rw [ht, ht, map_mul, map_mul, map_inv, GlobalTheory.BCT.TwistInvol.thL_involutive]
  group

theorem nrm_twconj_pf (w : Pl E) (hw : ¬ IsSplitAt w) (a : ℕ) (g δ : GLw a w) :
    (nrmL a w (g⁻¹ * δ * thL a w g)).val.charpoly = (nrmL a w δ).val.charpoly := by
  rw [nrmL_twconj w hw a g δ]
  have h := Matrix.charpoly_units_conj g⁻¹ (nrmL a w δ).val
  simpa [Units.val_mul, mul_assoc] using h

end PositivityTheory.Rg.Bc.ArchbcB.B.M4
