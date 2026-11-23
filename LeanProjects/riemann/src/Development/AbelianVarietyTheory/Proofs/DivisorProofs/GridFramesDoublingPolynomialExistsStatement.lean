import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridFramesDoublingPolynomialExists
import Development.AbelianVarietyTheory.Definitions.Divisors.RegConst
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grid_frames_doubling_polynomial_exists : GlobalTheory.FunPr.Hypotheses₂ →
  GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (X : TriG G i j), TopGrid W i j X → IsStageC W i j (pp D j) (qq D j) X →
    ∀ (A : Fr (G.V (.grid (i + 1) (j + 1)))) (A₁ : Fr (G.V (.grid i j))) (AV : Fr (G.V (.grid i (j + 1)))) (AV₁ : Fr (G.V (.grid (i + 1) j))), IsGridFr W _ A → IsGridFr W _ A₁ → IsGridFr W _ AV → IsGridFr W _ AV₁ →
    ∃ (σ : PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid (i + 1) (j + 1))).rank ≃ₗ[ℂ] PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid (i + 1) (j + 1))).rank)
      (σ' : PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid i j)).rank ≃ₗ[ℂ] PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid i j)).rank), ∀ t : T,
      IsFinF W.ψ W.θ true A (frSum AV AV₁) (X.f t) ∧ IsFinF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) ∧
      (∀ P g h, X.ker W.ψ W.θ t P h g = thetaKO (X.ω t) g h (fockF W.ψ W.θ true A (frSum AV AV₁) (X.f t) (σ P))) ∧
      ∀ P g h, X.ker' W.ψ W.θ t P h g = thetaKO (X.ω' t) g h (fockF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) (σ' P)) := by
  first | exact @GlobalTheory.TopDict.top_dictionary | exact GlobalTheory.TopDict.top_dictionary | (intros; apply GlobalTheory.TopDict.top_dictionary <;> assumption)
