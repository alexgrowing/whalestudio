import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteUnitarySelfDualLatticeGridDoubling
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteUnitary_selfDual_lattice_grid_doubling : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ i j : Fin D.R.m, ∃ h ∈ GfC (spX G i j), ∃ Λ : Submodule (𝓞 D.host.E) (Fin (spX G i j).rank → D.host.E),
      IsSelfDualC (spX G i j) Λ ∧
      (∀ t, SquareStanding G t → ∀ ε, IsIdemSum ε (locPl G t) → ∀ (S : HSp D) (x : WO S (spX G i j)),
        IsHalf ε x ∨ IsHalf (cA D ε) x → actO S (spX G i j) 1 h x = x) ∧
      (∀ (S : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)), IsSelfDualC S ΛS → ∀ u : WO S (spX G i j),
        u ∈ latO S (spX G i j) ΛS Λ (fun _ => True) ↔
          ∃ u₀ ∈ latO S (spX G i j) ΛS (latX G i j) (fun _ => True), u = actO S (spX G i j) 1 h u₀) ∧
      (latO (GlobalTheory.Grid.neg (spW G i j)) (spX G i j) (G.Λ (.grid (i + 1) (j + 1))) Λ (fun _ => True) : Set _) = orderingsOnSpW G i j ∧
      (latO (spW₁ G i j) (spX G i j) (G.Λ (.grid i j)) Λ (fun _ => True) : Set _) = orderingsOnSpWOne G i j := by
  first | exact @GlobalTheory.TopFlip.exists_twistElt | exact GlobalTheory.TopFlip.exists_twistElt | (intros; apply GlobalTheory.TopFlip.exists_twistElt <;> assumption)
