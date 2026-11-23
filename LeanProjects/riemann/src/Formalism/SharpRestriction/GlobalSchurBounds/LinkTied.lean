import Formalism.SharpRestriction.GlobalSchurBounds.MassRatioUnfoldedOfTheoremTwo
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeUnderScaleOfGeneral
import Formalism.SharpRestriction.GlobalSchurBounds.LinkGLOBAL7Tied4
import Formalism.SharpRestriction.GlobalSchurBounds.LemmaBSecondBranchOfLength
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremThreeHypothesesOfMultiplicity
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.DivisionRationalLattice
import Formalism.LocalToGlobal.GlobalTheory.GL5.LocalEndomorphismContinuous
import Formalism.LocalToGlobal.GlobalTheory.GL4.LowerSlopeInequalityFamily
import Formalism.LocalToGlobal.GlobalTheory.GL4.PStmtFree
import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
import Formalism.LocalToGlobal.GlobalTheory.GL5.PacketStatementOfIndependence
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.SlopeLineRamifiedFormula
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.PowSmulLatticeLeWeightLatticeTop

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT

variable {eps : ℝ}

theorem stabF (Fm : FamP eps) : flipTwoThree.admF3 Fm := by
  obtain ⟨C₅, h59a⟩ := UnusedSlot33.field_lemmas_except_seven
  have h59 : UnusedSlot33.ConclusionOnFamily Fm 100 C₅ := fun x _ i => by
    obtain ⟨p1, p2, p3, p4, p5, p5c, p6, p8⟩ := h59a (Fm.D x i) (Fm.L x i).sc
    exact ⟨p1, p2, p3, p4, p5, p5c, p6, UnusedSlot33.division_rational_lattice _, p8⟩
  exact flipTwoThree.stabiliser_family_of_column_lemma Fm 100 C₅ h59 (fun _ _ _ => GenusMassVolumes.levels_pro_g _ _)

theorem chiFin0_to0S {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (T : Formalism.L2.Forms.FormsTiedSym D u Ch chOf) (h : ChiFin0 T) : LocalLatticeBases.ChiFin0 T.to0 := by
  obtain ⟨n, hn, h⟩ := h
  refine ⟨n, hn, fun i hi h0 x => ?_⟩
  subst h0
  exact h x

theorem freeTT_holds (D : D7) (u : D.what₂.Word) : FreeTT D u := by
  rintro ⟨⟨Ch, chOf, T, -⟩, -⟩
  exact LocalLatticeBases.freeT_0 T.to0

theorem slopeLineT_holds (D : D7) (u : D.what₂.Word) : SlopeLineT D u := by
  rintro hS ⟨⟨Ch, chOf, T, hC⟩, -⟩
  exact LocalLatticeBases.slopeLine_0 hS T.to0 (chiFin0_to0S T hC)

theorem lemmaB_second_branch_of_length_formula (D : D7) (u : D.what₂.Word) (h : product_first_zeroth_parts.HidaSetting D u → ConcreteFormsLevelZero D u → LocalLatticeBases.SeenPlaceLatticeLengthFormula D u) : SecondBranchIntegralityUnderForms D u := by
  rintro hS hT
  obtain ⟨⟨Ch, chOf, T, -⟩, -⟩ := id hT
  exact LocalLatticeBases.second_branch_incl_length_level_zero' T.to0 (h hS hT)

def RealPlaceSecondLayerConditions (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Formalism.L2.Theta.RealTied (Fm.D x i) ∧
    ∃ C : Formalism.L2.Forms.ColsTiedSym (Fm.D x i), ∀ u, ChiFin0 (C.forms u)

theorem family_conditions_of_layer_two (Fm : FamP eps) (h : RealPlaceSecondLayerConditions Fm) : flipTwoThree.fam0 Fm StandardLattice.VolTie ∧ tCVTies Fm ∧ FamU Fm ConcreteFormsLevelZero := by
  obtain ⟨a, h⟩ := h
  obtain ⟨b, hs⟩ := stabF Fm
  refine ⟨⟨a, fun x hx _ i => volTie_of_realTied _ (h x hx i).1⟩,
    ⟨max (max a b) (Fm.x1 + 1), fun x hx i => ?_⟩,
    ⟨max a b, fun x hx hx1 i u _ => ?_⟩⟩
  · have ea : a ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
    have eb : b ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
    have e1 : Fm.x1 < x := by have := le_trans (le_max_right (max a b) (Fm.x1 + 1)) hx; linarith
    obtain ⟨C, -⟩ := (h x ea i).2
    exact ⟨⟨C⟩, hs x eb e1 i⟩
  · obtain ⟨C, hC⟩ := (h x (le_trans (le_max_left _ _) hx) i).2
    exact ⟨⟨_, _, C.forms u, hC u⟩, hs x (le_trans (le_max_right _ _) hx) hx1 i u⟩

end Formalism.MainNotions

end
