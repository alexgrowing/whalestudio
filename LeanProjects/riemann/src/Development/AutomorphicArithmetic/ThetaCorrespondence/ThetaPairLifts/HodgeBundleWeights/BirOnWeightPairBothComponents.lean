import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirationalOnWeightParameters
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringTopologyRefinement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.WeightPrincipalisationBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirationalOnWeightParametersStatement

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSApp
theorem birOn_u₁_u₂_alt : GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → Size → Covers fun Fm x _ ι p i Y PP _ => ∀ Z, BirOn Y.U Z (wtOf (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ 0) ∧ BirOn Y.U Z (wtOf (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₂ 0) := by
  intro hX hG hQ hSi hP2 hS
  have hP := _root_.GlobalTheory.T.covering_topology_refinement hP2
  have hBir : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q →
      ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)),
      (∀ τ (a b : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (b : ℕ) = a + 1 →
        (((CompHt.dimFlag (T.Q.Dw j) + 3) ^ 2 + 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) : ℕ) : ℤ) ≤ u τ a - u τ b) →
      ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) :=
    _root_.GlobalTheory.T.birOn_wtOf_of_consecutive_gap_bound hX hG hQ hSi hP hP2.q15 hP2.q16
  refine Closed.imp (((GlobalTheory.T.size_bounds_for_family hS).and (GlobalTheory.T.weight_parameter_strict_antitone hS)).and wtBig_run) ?_
  rintro eps Fm CH - ⟨⟨⟨C1, -, H1⟩, ⟨C2, -, H2⟩⟩, ⟨C3, -, H3⟩⟩
  refine ⟨0, le_rfl, ?_⟩
  obtain ⟨x0, H⟩ := (H1.and H2).and H3
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨⟨a1, a2⟩, a3⟩ := H x hx hle ι p hp
  have s1 := a1 i hi Y hY
  have s2 := a2 i hi
  have hB := a3 i hi
  intro Z
  have G := gaps_u₁_u₂_of_wtBig _ hB
  exact ⟨hBir (Fm.D x ι) p.T s1.1 ((i : ℕ) + 1) s2.1 s2.2.1 Y _ _ hY.1 _ (fun τ a b h => (G τ a b h).1) Z,
    hBir (Fm.D x ι) p.T s1.1 ((i : ℕ) + 1) s2.1 s2.2.1 Y _ _ hY.1 _ (fun τ a b h => (G τ a b h).2) Z⟩
end GlobalTheory.HSApp
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.birOn_weightPair_both_components : GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → Size → Covers fun Fm x _ ι p i Y PP _ => ∀ Z, BirOn Y.U Z (wtOf (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ 0) ∧ BirOn Y.U Z (wtOf (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₂ 0) := by
  first | exact @_root_.GlobalTheory.HSApp.birOn_u₁_u₂_alt | exact _root_.GlobalTheory.HSApp.birOn_u₁_u₂_alt | (intros; apply _root_.GlobalTheory.HSApp.birOn_u₁_u₂_alt <;> assumption)
end
