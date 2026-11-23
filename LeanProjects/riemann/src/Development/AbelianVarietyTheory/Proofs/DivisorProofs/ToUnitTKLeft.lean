import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.BetaAtClosedPoint
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValPsiZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DDataGens

theorem toUnit_TK_left (R : Type) [CommRing R] [IsDomain R] : (toUnit (TK R)).left = jK R := by
  have := Over.w (toUnit (TK R))
  simpa using this

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → (∀ y, PsiUnitOn D y Set.univ) →
    ∃ τ₀ : GlobalTheory.UChart.Gens D, ∀ a b, (τ₀ a b).IsGen ∧ ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι),
      Good D.P.L z J → val (D.tau a b) (𝟙 _) z J = val (τ₀ a b) (toUnit (TK R)).left z J := by
  intro R _ _ D hB hU
  choose t ht hc using fun y => (GlobalTheory.ArcPull.psiUnitOn_univ_iff D y).1 (hU y)
  have key : ∀ a b, ∃ g : LB.Gen (LB.LinComb D.P.L (K := Fin 4)
      ![(D.c (a + b)).left, (D.c a).left, (D.c b).left, (D.c 0).left] ![-1, 1, 1, -1]), g.IsGen ∧
      ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
        val g (toUnit (TK R)).left z J = val (t (a + b)) (toUnit (TK R)).left z J *
          (val (t a) (toUnit (TK R)).left z J)⁻¹ * (val (t b) (toUnit (TK R)).left z J)⁻¹ *
          val (t 0) (toUnit (TK R)).left z J := by
    intro a b
    let T := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (t (a + b))
      (LB.invGen D.P.L _ _ (t a))) (LB.invGen D.P.L _ _ (t b))) (t 0)
    have hT : T.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (ht _) (DVR.invGen_isGen _ _ _ _ (ht _)))
      (DVR.invGen_isGen _ _ _ _ (ht _))) (ht _)
    obtain ⟨g, hg, hv⟩ := exists_gen D.P.isLB
      (φ' := ![(D.c (a + b)).left, (D.c a).left, (D.c b).left, (D.c 0).left]) (ε' := ![-1, 1, 1, -1])
      (by
        intro U _ h
        simp [Fintype.prod_sum_type, Fin.prod_univ_four]) T hT
    refine ⟨g, hg, fun z J hJ => ?_⟩
    rw [hv _ _ z J hJ]
    simp only [T, val_mul hJ, val_inv]
  choose τ₀ hτ hv using key
  refine ⟨τ₀, fun a b => ⟨hτ a b, fun z J hJ => ?_⟩⟩
  have hp : ∀ y, val (t y) (toUnit (TK R)).left z J = val (D.psi y) (𝟙 _) z J := fun y => by
    rw [← val_corr hJ (hc y) (𝟙 _), val_pull hJ, Category.id_comp, toUnit_TK_left]
  have vρ : val D.rigK (𝟙 _) z J = val D.rig (jK R) z J := by
    refine (val_pull hJ _ _ _).trans ?_
    rw [Category.id_comp, toUnit_TK_left]
  rw [hv a b z J hJ, hp, hp, hp, hp, GlobalTheory.PsiZero.val_psi_zero hB hJ]
  simp only [DegPre.tau, val_mul hJ, val_inv, vρ]

end GlobalTheory.DDataGens
