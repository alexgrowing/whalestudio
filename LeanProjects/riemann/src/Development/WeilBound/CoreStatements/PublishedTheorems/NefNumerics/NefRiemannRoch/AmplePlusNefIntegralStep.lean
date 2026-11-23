import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowVanishingIdealLeAnnihilator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensOfForallIsPsEff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleLineBundleTopSelfIntersectionPosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorNefOfNonzeroSectionPowInductionStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.TopIntersectionGrowthBoundStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefIntersectionNonnegInductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIntersectionNumberAmpleConsNefNonnegStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasNonzeroSecPowOfAmpleSubAmpleStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem isAmpleLB_tens_lbPow_descent_step : ∀ (k : Type) [Field k] [Infinite k] (d : ℕ), (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k Y) → topologicalKrullDim Y ≤ (d : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) → ∀ (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → topologicalKrullDim X = (d + 1 : ℕ) → ∀ (A N M : LB X) (hA : IsAmpleLB A) (hN : IsNef k N) (hM : M.IsLB) (q c : ℕ), 1 ≤ q → cls M hM = cls N hN.isLB + c • cls A hA.isLB → 2 * ((d : ℤ) + 1) * interNum k (GlobalTheory.structureModule X) (Fin.cons A (fun _ : Fin d => M) : Fin (d + 1) → LB X) < q → ∀ b : ℕ, q ≤ b → b + 1 ≤ c * q → IsAmpleLB (tens (lbPow N q) (lbPow A (b + 1))) → IsAmpleLB (tens (lbPow N q) (lbPow A b)) := by
  intro k _ _ d hlow X _ _ hproj hdim A N M hA hN hM q c hq hMcls hbound b hqb hbc hL
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  have hdim' : topologicalKrullDim X ≤ ((d + 1 : ℕ) : WithBot ℕ∞) := hdim.le
  have hKl := GlobalTheory.T.nef_intersection_nonneg_induction k d hlow X hproj
  have hmix := GlobalTheory.T.lineBundleIntersectionNumber_ample_cons_nef_nonneg k X hproj d hdim' hKl A hA
  have hpos := GlobalTheory.T.ample_lineBundle_top_selfIntersection_pos k X hproj (d + 1) hdim A hA
  have hNl := isLB_lbPow hN.isLB q
  have hAl : ∀ n : ℕ, (lbPow A n).IsLB := fun n => isLB_lbPow hA.isLB n
  have hLcls : cls _ hL.isLB = q • cls N hN.isLB + (b' + 1 + 1) • cls A hA.isLB := by
    rw [cls_tens hNl (hAl _), cls_lbPow hN.isLB, cls_lbPow hA.isLB]
  have hnum := GlobalTheory.T.top_intersection_growth_bound k X hproj d hdim' A N _ M hA hN hL hM hmix hpos q (b' + 1 + 1) c hq
    (by omega) hbc hLcls hMcls hbound
  have hB : IsAmpleLB (lbPow A 2) := (isAmpleLB_pow_iff hA.isLB (by norm_num)).2 hA
  have hM'nef : IsNef k (tens (lbPow N q) (lbPow A b')) :=
    (hN.pow hA q).tens ((hA.isNef (k := k)).pow hA b') hA
  have hsplit : cls _ hL.isLB = cls _ hM'nef.isLB + cls _ hB.isLB := by
    rw [hLcls, cls_tens hNl (hAl _), cls_lbPow hN.isLB, cls_lbPow hA.isLB, cls_lbPow hA.isLB]
    simp only [add_smul, one_smul, two_smul]
    abel
  have hsec := GlobalTheory.T.exists_hasNonzeroSec_pow_of_ample_sub_ample' k X hproj d hdim' _ _ _ hL hB hM'nef.isLB hsplit hnum
  have hamp := GlobalTheory.T.isAmple_tensor_nef_of_nonzeroSectionPow_induction k d hlow X hproj hdim' A _ hA hM'nef hsec
  have hT : (tens (lbPow N q) (lbPow A (b' + 1))).IsLB := isLB_tens hNl (hAl _)
  refine hamp.of_lbIso hT ((cls_eq_iff hT hamp.isLB).1 ?_)
  rw [cls_tens hNl (hAl _), cls_tens hA.isLB hM'nef.isLB, cls_tens hNl (hAl _), cls_lbPow hN.isLB,
    cls_lbPow hA.isLB, cls_lbPow hA.isLB]
  simp only [add_smul, one_smul]
  abel
