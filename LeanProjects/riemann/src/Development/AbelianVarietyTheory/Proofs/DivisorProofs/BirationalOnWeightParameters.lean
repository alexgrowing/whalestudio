import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPrincipalisationBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongerPublishedHypothesesImplyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParameterStrictAntitoneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundsForFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WtBigRun
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

theorem gap_add_vec {N : ℕ} (v w : Fin N → ℤ) (k : ℕ) : gap (v + w) k = gap v k + gap w k := by
  unfold gap
  split_ifs
  · simp only [Pi.add_apply]; ring
  · simp

theorem gaps_u₁_u₂_of_wtBig {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    (P : WtPar Dw) (hB : WtBig P) (τ : Psi H) (a b : Fin (Dw.p + Dw.q)) (hab : (b : ℕ) = a + 1) :
    (((CompHt.dimFlag Dw + 3) ^ 2 + 2 * (Dw.p + Dw.q) : ℕ) : ℤ) ≤ P.u₁ τ a - P.u₁ τ b ∧
    (((CompHt.dimFlag Dw + 3) ^ 2 + 2 * (Dw.p + Dw.q) : ℕ) : ℤ) ≤ P.u₂ τ a - P.u₂ τ b := by
  have hk : (a : ℕ) + 1 < Dw.p + Dw.q := by have := b.2; omega
  have g1 := hB.gaps τ a hk
  have g2 := (P.gap_rem τ a).1
  have e1 : P.u₁ τ a - P.u₁ τ b = gap (P.u₁ τ) a := (gap_eq _ hab).symm
  have e2 : P.u₂ τ a - P.u₂ τ b = gap (P.u₁ τ) a + gap (P.rem τ) a := by
    rw [← gap_eq _ hab]
    exact gap_add_vec (P.u₁ τ) (P.rem τ) a
  have hn : (CompHt.dimFlag Dw + 3) ^ 2 + 2 * (Dw.p + Dw.q) ≤
      (FlagTan.dimFlag Dw + 3) * ((FlagTan.dimFlag Dw + 1).choose 2 + 4 * (Dw.p + Dw.q) + FlagTan.dimFlag Dw + 3) := by
    rw [dimFlag_eq]
    generalize FlagTan.dimFlag Dw = D
    generalize Dw.p + Dw.q = N
    generalize (D + 1).choose 2 = C
    nlinarith [Nat.zero_le (D * C), Nat.zero_le (D * N), Nat.zero_le C]
  have hn' : (((CompHt.dimFlag Dw + 3) ^ 2 + 2 * (Dw.p + Dw.q) : ℕ) : ℤ) ≤
      (((FlagTan.dimFlag Dw + 3) * ((FlagTan.dimFlag Dw + 1).choose 2 + 4 * (Dw.p + Dw.q) + FlagTan.dimFlag Dw + 3) : ℕ) : ℤ) :=
    by exact_mod_cast hn
  rw [e1, e2]
  exact ⟨hn'.trans g1, by linarith⟩

theorem birOn_u₁_u₂ : GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → Hypotheses2 → Size → Covers fun Fm x _ ι p i Y PP _ => ∀ Z, BirOn Y.U Z (wtOf (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ 0) ∧ BirOn Y.U Z (wtOf (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₂ 0) := by
  intro hX hG hQ hSi hP2 hS
  have hP := GlobalTheory.T.stronger_published_hypotheses_imply hP2
  have hBir : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q →
      ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)),
      (∀ τ (a b : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (b : ℕ) = a + 1 →
        (((CompHt.dimFlag (T.Q.Dw j) + 3) ^ 2 + 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) : ℕ) : ℤ) ≤ u τ a - u τ b) →
      ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) :=
    GlobalTheory.T.weight_principalisation_bound hX hG hQ hSi hP hP2.q15 hP2.q16
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
