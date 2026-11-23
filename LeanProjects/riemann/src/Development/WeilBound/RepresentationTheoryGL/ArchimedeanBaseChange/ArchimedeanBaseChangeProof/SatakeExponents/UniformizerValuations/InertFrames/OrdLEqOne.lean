import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameInert
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmFieldStatement

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Inert

namespace UniformizerValuation

theorem ordL_eq_one {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {x : L}
    (hx : Valued.v x = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    ordL x = 1 := by
  unfold ordL
  have h0 : Valued.v x ≠ 0 := by rw [hx]; exact WithZero.coe_ne_zero
  rw [dif_neg h0]
  have hu : WithZero.unzero h0 = Multiplicative.ofAdd (-1 : ℤ) :=
    WithZero.coe_injective ((WithZero.coe_unzero h0).trans hx)
  rw [hu]
  simp

end UniformizerValuation

theorem unifEx : UnifEx := by
  intro E _ _ _ hU w hw
  obtain ⟨-, -, -, h4, -⟩ := GlobalTheory.T.placeConjugation_properties_cmField E hU w
  obtain ⟨ϖ, q, hI, -⟩ := (h4 hw).2.1
  have hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
    hI.2.2.2.1
  have h0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact WithZero.coe_ne_zero hv.symm
  refine ⟨Units.mk0 ϖ h0, q, ⟨?_, ?_⟩, ?_⟩
  · exact UniformizerValuation.ordL_eq_one hv
  · exact hI.2.2.1
  · exact hI

end PositivityTheory.Rg.BcB.F.Inert

end
