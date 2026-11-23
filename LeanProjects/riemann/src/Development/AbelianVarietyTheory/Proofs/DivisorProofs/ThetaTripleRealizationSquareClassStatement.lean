import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTripleRealizationSquareClass
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlipAtEq

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_triple_realization_square_class : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t) (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E) (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F _ _) (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F _ _),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ X om om' R Rf → IsTied t i j e Bs Γ X →
    ∀ w ∈ locPl G t, ∀ v (hv : w.under (𝓞 D.host.F) = v) (hP : v ∈ Bs.P) ιA,
      Γ.M.IsLinW Bs.ψ (Bs.τ ⟨v, hP⟩) (Γ.V.bas v) (Γ.W.bas v) ιA →
    ∃ ι, IsLagrModel Γ.M W.ψ v (mixHalf e (atPl w 1)) (mixHalf e (cA D (atPl w 1))) (mixCo B t e w) ι ∧
    ∃ c : ℂ, c ≠ 0 ∧ ∃ g₀ : GL (Fin (spW G i j).rank) (Fv D.host.F v),
    ∃ c₀ : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Fv D.host.F v),
      (∀ n Φ, depthAt G w ≤ n → IsNatDatum (unifAt w) n Φ → ∃ φ ∈ GlobalTheory.WeilM.SB _, ι φ = flipAt W t i j w n Φ ∧
        ∀ Z, ιA φ Z = c * GlobalTheory.SquareFlipReach.sqCore W t i j w n Φ (GlobalTheory.SquareFlipReach.trA t hv e (g₀.1 * Z * c₀.1))) ∧
      ∀ (K₁ : GL (Fin (spV G i j).rank) (Fv D.host.F v)) (K₂ : GL (Fin (spV₁ G i j).rank) (Fv D.host.F v)),
        ∃ g, ∃ c' : ℂ, c' ≠ 0 ∧ ∀ φ ∈ GlobalTheory.WeilM.SB _, ∃ φ₃ ∈ GlobalTheory.WeilM.SB _,
          Acts (evFin D.host.F v) (om (1, blkU _ _ e h.JWW g)) φ φ₃ ∧
          ∀ Z, ιA φ₃ Z = c' * ιA φ (Z * (c₀.1 * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e K₁.1 K₂.1 * (c₀⁻¹).1)) := by
  first | exact @GlobalTheory.MixCompare.mixed_compare | exact GlobalTheory.MixCompare.mixed_compare | (intros; apply GlobalTheory.MixCompare.mixed_compare <;> assumption)
