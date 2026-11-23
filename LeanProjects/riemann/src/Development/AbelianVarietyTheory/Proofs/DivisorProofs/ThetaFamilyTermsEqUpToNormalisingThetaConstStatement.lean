import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFamilyTermsEqUpToNormalisingThetaConst
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
theorem _root_.GlobalTheory.T.thetaFamily_terms_eq_up_to_normalising_thetaConst : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (x x' : X₁.S.Gam) (C C' : Type) (lab : C → X₁.S.Gam) (lab' : C' → X₁.S.Gam) (T : (Fin 8 → X) → C → V) (T' : (Fin 8 → X) → C' → V), 𝔪.Terms x lab T → 𝔪.Terms x' lab' T' → ∀ (c : C) (c' : C'), lab c = lab' c' → ∀ mu, algebraMap V (FractionRing V) (T mu c) * 𝔪.yK ⟨X₁.S.th x, X₁.S.th_mem x⟩ = algebraMap V (FractionRing V) (T' mu c') * 𝔪.yK ⟨X₁.S.th x', X₁.S.th_mem x'⟩ := by
  first | exact @GlobalTheory.Poinc.Sep.TermsCompare.terms_eq | exact GlobalTheory.Poinc.Sep.TermsCompare.terms_eq | (intros; apply GlobalTheory.Poinc.Sep.TermsCompare.terms_eq <;> assumption)
