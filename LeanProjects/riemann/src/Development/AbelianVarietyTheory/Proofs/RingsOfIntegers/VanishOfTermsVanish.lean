import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.WeightIndep
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PGAppEqZeroIff

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ClosedFibreTerm

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem vanish_of_terms_vanish {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ)
    (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (h : U.ExpandsAt e k σ f)
    (h0 : ∀ α j, ((U.gt e).pG.left.app _).hom ((f α).f j) = 0) (j) :
    ((fstG I e G).left.app _).hom (σ.f j) = 0 := by
  obtain ⟨S, hS⟩ := expandsAt_val U e k σ f h
  obtain ⟨jL, rfl⟩ : ∃ jL, j = fun _ => jL := ⟨j 0, funext fun i => congrArg j (Subsingleton.elim i 0)⟩
  refine fn_ext fun y hy => ?_
  choose J hJ using fun ψ : (thickObj R I e G).left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ y)
  have hJ : Good D.toPre.P.L y J := hJ
  have H := (hS _ (𝟙 _) y J hJ).2 jL (Set.mem_iInter.1 hy 0)
  have hz : ∀ α, sval (f α) (𝟙 _ ≫ pGl U e) y J = 0 := fun α => by
    have m := hJ.mem (D.toPre.famφB α) (𝟙 _ ≫ pGl U e)
    exact (gs_pull (𝟙 _) _ y _ m _).symm.trans ((congrArg (gs (𝟙 _) y _) (h0 α _)).trans (gs_zero (𝟙 _) y _ m))
  rw [Finset.sum_eq_zero fun α _ => by rw [hz α, zero_mul]] at H
  exact (gs_pull (𝟙 _) _ y _ hy _).trans (((Units.mul_right_eq_zero _).1 H).trans (gs_zero (𝟙 _) y _ hy).symm)

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G) (σ : H0 U.LG.L 1) (g : ∀ α : D.toPre.X, D.toPre.SecB 1 α), U.ExpandsAt 0 1 σ g → (∀ χ, χ ≠ 0 → ∃ g' : D.toPre.SecB 1 χ, SecIsMul D.toPre.P.A.hom ϖ (g χ) g') → ((∃ j, ((fstG (maximalIdeal V) 0 G).left.app _).hom (σ.f j) ≠ 0) ↔ ¬ ∃ g' : D.toPre.SecB 1 0, SecIsMul D.toPre.P.A.hom ϖ (g 0) g') := by
  intro V _ _ _ ϖ hϖ D A G _ _ U σ g hE hχ
  have Q : ∀ α : D.toPre.X, (∀ j, ((U.gt 0).pG.left.app _).hom ((g α).f j) = 0) ↔
      ∃ g' : D.toPre.SecB 1 α, SecIsMul D.toPre.P.A.hom ϖ (g α) g' := fun α => by
    have := GlobalTheory.ExtDiv.main V ϖ hϖ D A G U 0 1 α (g α)
    have hp : ϖ ^ (0 + 1) = ϖ := pow_one ϖ
    rwa [hp] at this
  rw [← not_forall]
  refine not_congr ⟨fun h => (Q 0).1 (WeightPf.weightIndep V _ D A G U 0 1 σ g h hE 0), fun h => ?_⟩
  refine vanish_of_terms_vanish U 0 1 σ g hE fun α => (Q α).2 ?_
  by_cases hα : α = 0
  · subst hα; exact h
  · exact hχ α hα

end GlobalTheory.ClosedFibreTerm
