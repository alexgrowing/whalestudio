import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsNormPull
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijFAndExpandsFLin
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

namespace GlobalTheory.TestFibre

theorem isComb_iff_expandsF_sum : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (J : Type) [Fintype J] (s : J → SecA A F k) (Φ : J → Fam D.toPre F k) (b : J → F) (t : SecA A F k), (∀ i, U.ExpandsF F k w₀ (s i) (Φ i)) → (IsComb A s b t ↔ U.ExpandsF F k w₀ t (∑ i, b i • Φ i)) := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ k hk w₀ hw J _ s Φ b t hs
  obtain ⟨hb, hl⟩ := GlobalTheory.UT.expBijF_and_expandsF_lin hL R I hI D A G hG U
  obtain ⟨h₁, h₂⟩ := hb F k hk w₀ hw
  have h0 : U.ExpandsF F k w₀ (SecOps.secZero : SecA A F k) (0 : Fam D.toPre F k) := by
    obtain ⟨σ, hσ⟩ := (h₁ (SecOps.secZero : SecA A F k)).exists
    have h := hl F k w₀ SecOps.secZero SecOps.secZero SecOps.secZero σ σ (-1) hσ hσ (fun j => ((add_zero _).trans (mul_zero _)).symm)
    rwa [neg_one_smul, neg_add_cancel] at h
  have key : ∀ S : Finset J, ∃ u : SecA A F k,
      (∀ j, u.f j = ∑ l ∈ S, liftFun A.A _ (cF R (b l)) * (s l).f j) ∧
        U.ExpandsF F k w₀ u (∑ i ∈ S, b i • Φ i) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨SecOps.secZero, fun j => by rw [Finset.sum_empty]; rfl, by rw [Finset.sum_empty]; exact h0⟩
    | insert a S ha ih =>
      obtain ⟨u, hu, eu⟩ := ih
      refine ⟨SecOps.secAdd (SecOps.secScale ((fst (TFK (R := R) F) A.A).left.appTop.hom (cF R (b a))) (s a)) u,
        fun j => ?_, ?_⟩
      · rw [Finset.sum_insert ha, ← hu j]; rfl
      · rw [Finset.sum_insert ha]
        exact hl F k w₀ (s a) u _ (Φ a) _ (b a) (hs a) eu (fun j => rfl)
  obtain ⟨u, hu, eu⟩ := key Finset.univ
  constructor
  · intro h
    obtain rfl : t = u := SecOps.sec_ext fun j => (h j).trans (hu j).symm
    exact eu
  · intro h
    obtain rfl : t = u := (h₂ _).unique h eu
    exact hu

end GlobalTheory.TestFibre
