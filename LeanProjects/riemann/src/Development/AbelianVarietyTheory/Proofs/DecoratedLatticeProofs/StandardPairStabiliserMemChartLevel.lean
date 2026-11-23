import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointsLieOverDistinctPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryClassRepresentativesBijective
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceFrameGLMemCompactRealTrivialStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitFrameGLFiniteMatrixOffPlaceEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardDatumSplitPlacesOverLevelPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceComponentMemBaseLatticeLevelOfFixesPaiStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceComponentKeepsLevelFunctionalStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.StabLev

theorem stab_mem_level : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    GlobalTheory.AdForm.StdT I l Z u p β Q L → ∀ j, j ≤ B.R.m → ∀ b, ∀ i (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k), g • Q j i = Q j i → (β j i).gl g ∈ A.U j b := by
  intro B X I hOk hPins l Z u a Ch A hA k _ _ _ _ ι p β Q L hStd j hj b i g hg
  rw [hA.U j hj b]
  refine ⟨GlobalTheory.T.splitPlaceFrameGL_mem_compactRealTrivial _ _ _ _ _ _ _, ?_⟩
  obtain ⟨x, hx⟩ := GlobalTheory.AdForm.RdVal.finM_mem ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj) (gramN (I.rec7 l Z) j hj) rfl ((β j i).gl g)
  have hmem : x.1 ∈ (A.K j hj b).lev.U := by
    rw [(A.K j hj b).lev.U_eq]
    refine ⟨x.2, fun v => ?_⟩
    by_cases hv : v = (p i).v
    · subst hv
      have hT := GlobalTheory.T.standardDatum_splitPlaces_over_levelPrime I hOk hPins l Z u k ι p β Q L hStd i
      exact GlobalTheory.T.splitPlace_component_keeps_level_functional I hOk hPins l Z u a Ch A hA k ι p β Q L hStd j hj b i g hg x hx hT
        (GlobalTheory.T.splitPlace_component_mem_baseLattice_level_of_fixes_pair I hOk hPins l Z u a Ch A hA k ι p β Q L hStd j hj b i g hg x hx)
    · rw [GlobalTheory.T.splitFrameGL_finiteMatrix_offPlace_eq_one _ _ _ _ _ _ g _ (rankN (I.rec7 l Z) j hj) x.1 hx v hv]
      exact Subgroup.one_mem _
  exact ⟨⟨x.1, hmem⟩, hx⟩

end GlobalTheory.AdForm.StabLev

end
