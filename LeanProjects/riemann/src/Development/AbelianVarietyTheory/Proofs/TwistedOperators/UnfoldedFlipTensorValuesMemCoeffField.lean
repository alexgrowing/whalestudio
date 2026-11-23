import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OppositePathLocalTotalTensorMemCoefficientFieldStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedTensorFactorMemCoeffFieldStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompactStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralUnfoldingVariablesMemFieldRangeStatement
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowTest

theorem term_datum_mem_range : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ), HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ (w : locPl ch.G t) X Y, (ch.S.term t Φ β w).datum X Y ∈ Set.range D.what₂.embLL := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F CF b hS hIs hSc hF t Φ hSum β hβ w X Y
  by_cases h0 : (ch.S.term t Φ β w).datum X Y = 0
  · exact ⟨0, by rw [h0, map_zero]⟩
  have hlc := GlobalTheory.T.flatIntegrand_flippedTensor_locallyConstant_compactSupport ch large₂ F CF b hS hIs hSc hF t Φ hSum β hβ w X Y
  have hT := GlobalTheory.T.oppositePathLocalTotalTensor_mem_coefficientField ch large₂ F CF b hS hIs hSc hF t Φ hSum w.1 w.2
  have hM := GlobalTheory.T.movedTensorFactor_mem_coeffField ch large₂ F CF b hS hIs hSc hF t Φ hSum β hβ w _ hT
  show flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) _ X Y ∈ _
  refine GlobalTheory.T.integral_unfolding_variables_mem_fieldRange (unitVol w.1) (isUnitVol_unitVol w.1) D.what₂.embLL _ hlc.1 hlc.2 fun e => ?_
  simp only [flatIntegrand]
  by_cases hm : moved (locGrid ch.G t w) (keepAt ch.G w) ((repsAt ch.G t w).elt (β w)) (Tflip ch.W ch.S.B t Φ w)
      (fill one_le_sLen X Y e) = 0
  · rw [hm, zero_mul]; exact ⟨0, map_zero _⟩
  obtain ⟨a, ha⟩ := hM (fill one_le_sLen X Y e)
  obtain ⟨c, hc⟩ := hF.phases t Φ β hβ w X Y e h0 hm
  refine ⟨a * c⁻¹, ?_⟩
  rw [map_mul, map_inv₀, ha, hc, AddChar.map_neg_eq_inv, Circle.coe_inv]

end GlobalTheory.RowTest
