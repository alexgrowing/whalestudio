import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalLiftsSmoothEverywhereStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalAlongRightGridArrowsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalAlongDownGridArrowsStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipRun

theorem cuspStep_big : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RowClaim.Big fun {_} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (M : Vol ch.G), M.Is t → GlobalTheory.FlipRun.CuspStep ch.W M ch.rm t := by
  intro hLC hP
  have hS := GlobalTheory.T.cuspidal_lifts_smooth_everywhere hLC hP
  refine (GlobalTheory.RowClaim.Big.and (GlobalTheory.T.cuspidal_along_right_grid_arrows hS hP) (GlobalTheory.T.cuspidal_along_down_grid_arrows hS hP)).imp fun CF0 h ε CF hC => ?_
  obtain ⟨x₀, h⟩ := h ε CF hC
  refine ⟨x₀, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch hsc t M hM a ha e' he φ f hf Q F' hF => ?_⟩
  have H := h D large₂ e hx Γ Pl0 T A Ks R F s ch hch hsc
  rcases ha with ⟨i, j, hi, hj, rfl⟩ | ⟨i, j, hi, hj, rfl⟩
  · exact H.1 t M hM _ (Or.inl ⟨i, j, hi, hj, rfl⟩) ⟨i, j, rfl⟩ e' he φ f hf Q F' hF
  · exact H.2 t M hM _ (Or.inr ⟨i, j, hi, hj, rfl⟩) ⟨i, j, rfl⟩ e' he φ f hf Q F' hF

end GlobalTheory.FlipRun

end
