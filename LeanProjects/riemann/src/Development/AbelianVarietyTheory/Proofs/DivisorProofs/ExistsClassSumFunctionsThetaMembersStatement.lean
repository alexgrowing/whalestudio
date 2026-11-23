import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassSumFunctionsThetaMembers
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_class_sum_functions_theta_members : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∃ f : X₁.S.Gam → X₁.S.Gam → X₁.Ω₁, (∀ a b, ∀ w : X₁.M.Z, X₁.M.Div X₁.S.th x₀ w → f a b ∈ X₁.M.O w) ∧ (∀ a a' b, a - a' ∈ X₁.S.HH X₁.M z₁ → f a b = f a' b) ∧ ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : X → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C) (a : X₁.S.Gam) (κ : X), 𝔪.YY a κ → ∀ h : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ h = f a (lab c) → SumI (maximalIdeal V) (fun nu : X => T (κ + (X₁.S.r * X₁.S.N) • nu) c) (ev h) := by
  first | exact @GlobalTheory.GSep.ClassSumFun.exists_classSum_fun | exact GlobalTheory.GSep.ClassSumFun.exists_classSum_fun | (intros; apply GlobalTheory.GSep.ClassSumFun.exists_classSum_fun <;> assumption)
