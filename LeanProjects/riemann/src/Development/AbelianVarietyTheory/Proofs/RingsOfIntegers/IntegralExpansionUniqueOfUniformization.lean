import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.WeightIndep
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PGAppEqZeroIff
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsAtSub

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ExpUniq

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem main : lemmaBSt.{0} → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G) (k : ℕ) (σ : H0 U.LG.L k) (f g : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ e, U.ExpandsAt e k σ f) → (∀ e, U.ExpandsAt e k σ g) → f = g := by
  intro hB V _ _ _ D A G _ _ U k σ f g hf hg
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have := D.toPre.P.isAb.smooth
  have := D.toPre.P.isAb.proper
  have := D.toPre.P.isAb.geomConnected
  let d : ∀ α : D.toPre.X, D.toPre.SecB k α := fun α => SecOps.secAdd (f α) (SecOps.secNeg (g α))
  have hd : ∀ α j, (d α).f j = (f α).f j - (g α).f j := fun α j => (sub_eq_add_neg _ _).symm
  have h0 : ∀ e, U.ExpandsAt e k SecOps.secZero d := fun e =>
    GlobalTheory.expandsAt_sub V _ D A G U e k σ σ SecOps.secZero f g d (fun j => (sub_self _).symm) hd (hf e) (hg e)
  funext α
  refine SecOps.sec_ext fun j => sub_eq_zero.1 ((hd α j).symm.trans ?_)
  refine hB V D.toPre.P.A _ (linComb_isLB _ D.toPre.P.isLB _ _) (d α) ϖ hϖ (fun i e => ?_) j
  obtain ⟨τ, hτ⟩ := (GlobalTheory.ExtDiv.main V ϖ hϖ D A G U e k α (d α)).1
    (WeightPf.weightIndep V _ D A G U e k SecOps.secZero d (fun _ => map_zero _) (h0 e) α)
  rw [hτ i, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  refine Dvd.dvd.mul_right ?_ _
  simp only [scal, pow_succ, map_mul, map_pow]
  exact Dvd.dvd.mul_right (dvd_refl _) _

end GlobalTheory.ExpUniq
