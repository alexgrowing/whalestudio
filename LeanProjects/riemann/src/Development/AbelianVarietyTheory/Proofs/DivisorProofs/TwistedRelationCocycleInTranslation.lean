import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFunctionalEquationBundleTrivialAbelianParStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFactorExistsUniqueConstMulIntegralGeneratStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedTwistedFactorValueAtLatticePointStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem GlobalTheory.TwFam.trel_cocycle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (n j : ℤ) (ν mu β₀ β₁ β₂ : D.toPre.X) (s₀ : SecT D.toPre a n j β₀) (s₁ : SecT D.toPre a n j β₁) (s₂ : SecT D.toPre a n j β₂), β₁ = β₀ + shift h h' n j ν → β₂ = β₁ + shift h h' n j mu → TRel h ν s₀ s₁ → TRel h (ν + mu) s₀ s₂ → TRel h mu s₁ s₂ := by
  intro R _ _ _ hR D a a' h h' hE n j ν mu β₀ β₁ β₂ s₀ s₁ s₂ h₁ h₂ hν hνμ
  have hL := D.toPre.P.isLB
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.T.twistedFunctionalEquation_bundle_trivial_abelianPart R hR D a a' h h' hE n j ν β₀ β₁ h₁
  obtain ⟨⟨u₁, hu₁⟩, -, -⟩ := GlobalTheory.T.twistedFactor_exists_unique_const_mul_integralGenerator R hR D a h hE.1 hE.2.2.2.1 n j ν β₀ β₁ u₀ hu₀
  intro u hu Z x z J hJ
  have hc : (DegPre.trF D.toPre (FractionRing R) mu).left ≫ (DegPre.trF D.toPre (FractionRing R) ν).left =
      (DegPre.trF D.toPre (FractionRing R) (ν + mu)).left := by
    rw [← Over.comp_left, ReciprocityTheory.ChartRestriction.G.DVR.UUA.trF_add, add_comm]
  have FE : FormEq (Sum.elim (dφ D.toPre a mu β₁ β₂) (fun k => (DegPre.trF D.toPre (FractionRing R) mu).left ≫ dφ D.toPre a ν β₀ β₁ k))
      (Sum.elim (dε n j) (dε n j)) (dφ D.toPre a (ν + mu) β₀ β₂) (dε n j) := by
    intro U _ g
    simp only [dφ, dε, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, ← Category.assoc, hc]
    simp only [zpow_neg, Finset.prod_inv_distrib, Category.assoc]
    group
  obtain ⟨w, hw, hwv⟩ := exists_gen hL FE _ (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ u _ hu.1
    (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ u₁ hu₁.1 _))
  have hwf : IsFac D.toPre a h n j (ν + mu) β₀ β₂ w := by
    refine ⟨hw, fun z' J' hJ' => ?_⟩
    rw [hwv _ _ z' J' hJ', val_mul hJ', val_pull hJ', hu.2 z' J' hJ', GlobalTheory.T.normalisedTwistedFactor_value_at_latticePoint R hR D a a' h h' hE n j ν mu β₀ β₁ h₁ u₁ hu₁ z' J' hJ']
    rw [mul_comm]
    exact inv_mul_cancel_right _ _
  have e1 := hν u₁ hu₁ Z (x ≫ (DegPre.trF D.toPre (FractionRing R) mu).left) z J hJ
  have e2 := hνμ w hwf Z x z J hJ
  rw [hwv _ _ z J hJ, val_mul hJ, val_pull hJ, ← hc] at e2
  simp only [Category.assoc] at e1 e2 ⊢
  rw [e2, e1, Units.val_mul]
  ring
