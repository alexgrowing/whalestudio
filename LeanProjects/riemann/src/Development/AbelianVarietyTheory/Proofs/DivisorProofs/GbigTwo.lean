import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DownRight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SqStepBig

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Geo Chars)

theorem gbig_two {Q1 Q2 Q : GP} (h1 : GBig Q1) (h2 : GBig Q2)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q1 G μ₀ C x b → Q2 G μ₀ C x b → Q G μ₀ C x b) : GBig Q := by
  obtain ⟨a1, h1⟩ := h1
  obtain ⟨a2, h2⟩ := h2
  refine ⟨max a1 a2, fun ε CF hCF => ?_⟩
  obtain ⟨c1, x1, g1⟩ := h1 ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨c2, x2, g2⟩ := h2 ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max c1 c2, max x1 x2, fun C hC D large₂ hε hx hR T Lc μ₀ hμ G => H G μ₀ C _ _ ?_ ?_⟩
  · exact g1 C (le_trans (le_max_left _ _) hC) D large₂ hε (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hμ G
  · exact g2 C (le_trans (le_max_right _ _) hC) D large₂ hε (le_trans (le_max_right _ _) hx) hR T Lc μ₀ hμ G

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

def Carried (G : GridData Lc sc) (W : G.Weil) (i j : Fin D.R.m) {A A' WW : HSp D} (X : Tri T A A' WW)
    (Bs : Base D.host.F D.host.E) (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW)
    (Γ : Geo D.sp.cm.sig A.rank A'.rank) (s : T) : Prop :=
  GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW (X.f s) ∧ GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW (X.f' s) ∧
    (∀ P g h, thetaKO (X.ω s) g h (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW (X.f s) P) = X.ker W.ψ W.θ s P h g) ∧
    (∀ P g h, thetaKO (X.ω' s) g h (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' s) P) = X.ker' W.ψ W.θ s P h g) ∧
    ∀ om om', GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ (GlobalTheory.SqStep.chs G i j s) om om' →
      ∃ e cA cB, GlobalTheory.SquareAgree.IsOver W.ψ W.θ FA FA' FW (GlobalTheory.SqStep.chs G i j s).α (GlobalTheory.SqStep.chs G i j s).β X.m X.fd
        X.m' X.fd' (X.ω s) (X.ω' s) e Bs Γ (GlobalTheory.SqStep.chs G i j s) om om' cA cB

end GlobalTheory.SqStepBig

end
