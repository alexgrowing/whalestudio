import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTripleTransportSameRanksConstantsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDefiniteBottomTripleTransferredFramesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTripleConstantsEqOfSameLatticesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BotTransfer

theorem bottom_const_transfer : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
      NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW) (B B' WW₁ : HSp D)
      (Y : Tri T B B' WW₁) (c : T → ℂ), IsBottomTri W i j X → IsBottomTri W i j Y → Y.IsConst W.ψ W.θ c →
      ∃ u : T → D.what₂.LLˣ, X.IsConst W.ψ W.θ fun t => D.what₂.embLL (u t) * c t := by
  intro _ _ _
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hL G => ?_⟩⟩
  intro W S hψ hN i j A A' WW X B B' WW₁ Y c hX hY hc
  obtain ⟨X₁, hX₁, hX₁c⟩ := GlobalTheory.T.definiteBottomTriple_transport_same_ranks_constants W i j A A' WW X B B' WW₁ Y hX hY
  obtain ⟨Y₁, hY₁, e1, e2, e3, hY₁c⟩ := GlobalTheory.T.exists_definiteBottomTriple_transferred_frames W S hψ μ₀ hL hN i j B B' WW₁ X₁ Y hX₁ hY
  obtain ⟨u, hu⟩ := hY₁c c hc
  exact ⟨u, hX₁c _ (GlobalTheory.T.definiteBottomTriple_constants_eq_of_same_lattices W i j B B' WW₁ X₁ Y₁ hX₁ hY₁ e1.symm e2.symm e3.symm _ hu)⟩

end GlobalTheory.BotTransfer
