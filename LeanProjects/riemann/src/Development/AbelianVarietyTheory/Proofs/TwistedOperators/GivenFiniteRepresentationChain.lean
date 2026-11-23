import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsChainPols
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorGiven
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasLocalSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalVectorDownEdgeInteriorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalVectorDownEdgeBoundaryStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalVectorRightEdgeCosineStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem GlobalTheory.FlipStart.startFin : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (f : ∀ j : Fin D.R.m, Sch ch.G (.down t 0 j)), GlobalTheory.FlipStart.ChainVecs ch t f → ∃ z : ℂˣ, z ∈ xiVals R.toLevCh t ∧ ∀ Φ : ch.G.Datum, RepFin ch.S.B ch.rm t (givenPath t D.R.m) (Finsupp.single (GlobalTheory.FlipStart.givenFin ch.W t f Φ) (z : ℂ)) (fun w => (givenStage t w ch.S.B Φ).tensor) := by
  intro hP
  obtain ⟨C, h⟩ := Big.and (Big.and (GlobalTheory.T.local_vector_down_edge_interior hP) (GlobalTheory.T.local_vector_down_edge_boundary hP)) (GlobalTheory.T.local_vector_right_edge_cosine hP)
  refine ⟨C, fun ε CF hC => ?_⟩
  obtain ⟨x₀, h⟩ := h ε CF hC
  refine ⟨x₀, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi ha => ?_⟩
  obtain ⟨⟨hc1, hc2⟩, hr⟩ := h D large₂ he hx Γ Pl0 T A Ks R F s ch hi ha
  intro t f hf
  have hc : ∀ j : Fin D.R.m, ∃ c : ℂˣ, c ∈ xiVals R.toLevCh t ∧ ∀ e : AE D, IsIdemSum e (locPl ch.G t) →
      ∀ Φ : ch.G.Datum, IsLocVec ch.W (.mu t 0 j) e (ch.rm.vT 0 j) ((c : ℂ) • GlobalTheory.FlipStart.givenFn ch.S.B t Φ e (.down t 0 j)) (f j) := by
    intro j
    by_cases hj : (j : ℕ) + 1 < D.R.m
    · exact hc1 t j (f j) hj ((hf j).1 hj)
    · have hj' : (j : ℕ) + 1 = D.R.m := by have := j.2; omega
      exact hc2 t j (f j) hj' ((hf j).2 hj')
  choose c hcx hcv using hc
  obtain ⟨e, he⟩ := GlobalTheory.FunObj.LocTensor.exists_idemSum_locPl s.core.lev ch.G t
  refine ⟨(∏ j, c j)⁻¹, Subgroup.inv_mem _ (Subgroup.prod_mem _ fun j _ => hcx j), fun Φ => ?_⟩
  refine GlobalTheory.FlipStart.repFin_of ch.W ch.S.B ch.rm t f Φ e he (fun j => (c j : ℂ)) _ ?_ (fun j => hcv j e he Φ) (hr t e he Φ)
  rw [← Units.coe_prod, ← Units.val_mul, inv_mul_cancel, Units.val_one]

end
