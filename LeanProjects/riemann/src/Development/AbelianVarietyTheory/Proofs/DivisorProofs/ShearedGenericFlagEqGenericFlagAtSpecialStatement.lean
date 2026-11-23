import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShearedGenericFlagEqGenericFlagAtSpecial
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shearedGenericFlag_eq_genericFlag_at_special : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ B ∈ E'.S (genericPoint Y.X), ∀ A ∈ E.S (f (genericPoint Y.X)), ∀ (τ : ι) (a b : Fin (m τ)), a < b → ∀ (K : Type) [Field K] (V : ValuationSubring K) (c : Y.Fn →+* V) (t : V), IsLocalRing.residue V t = 0 → ∀ v₂ : Sp V ⟶ Y.X, v₂ ≫ f = spMap c ≫ (ratOf Y).pt ≫ f → Bears E' φ A (shear τ a b (t : K) * (B * (A.map φ)⁻¹).map ((algebraMap V K).comp c)) (spMap (algebraMap V K) ≫ v₂) → spMap (IsLocalRing.residue V) ≫ spMap c ≫ (ratOf Y).pt = spMap (IsLocalRing.residue V) ≫ v₂ := by
  first | exact @GlobalTheory.FlagPush.Meet.meet | exact GlobalTheory.FlagPush.Meet.meet | (intros; apply GlobalTheory.FlagPush.Meet.meet <;> assumption)
