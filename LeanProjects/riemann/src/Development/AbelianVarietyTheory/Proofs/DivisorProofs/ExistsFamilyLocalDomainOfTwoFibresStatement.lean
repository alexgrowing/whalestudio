import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFamilyLocalDomainOfTwoFibres
import Development.AbelianVarietyTheory.Definitions.Divisors.KeyPBIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_family_localDomain_of_twoFibres : ∀ g n : ℕ, n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [Field o] [CharZero o] (ζ : oˣ) (W : Type) [CommRing W] [IsDomain W] [IsNoetherianRing W] [IsLocalRing W] (β : o →+* W) (v : (Fin (2 * g) → ZMod ((n ^ j) ^ 2)) → W) (K₀ K₁ : Type) [Field K₀] [IsAlgClosed K₀] [Field K₁] [IsAlgClosed K₁] (i₀ : W →+* K₀) (i₁ : W →+* K₁), (∀ q : Ideal W, q.IsPrime → q = RingHom.ker i₀ ∨ q = RingHom.ker i₁) → ∀ (P₀ : PolAV (Sp K₀)) (P₁ : PolAV (Sp K₁)) (h₀ : P₀.g = g) (h₁ : P₁.g = g) (l₀ : Out.Level P₀ ((n ^ j) ^ 2) (unitOn (Units.map (i₀.comp β).toMonoidHom ζ))) (l₁ : Out.Level P₁ ((n ^ j) ^ 2) (unitOn (Units.map (i₁.comp β).toMonoidHom ζ))), (IsThetaPt P₀ (n ^ j) (levelPoint l₀ h₀) fun a => fnOf (i₀ (v a))) → (IsThetaPt P₁ (n ^ j) (levelPoint l₁ h₁) fun a => fnOf (i₁ (v a))) → ∃ (P : PolAV (Sp W)) (pt : (Fin (2 * g) → ZMod ((n ^ j) ^ 2)) → (baseOver (Sp W) ⟶ P.A)) (φ₀ : P₀.A.left ⟶ P.A.left) (φ₁ : P₁.A.left ⟶ P.A.left), P.g = g ∧ (∀ a, pt a ^ ((n ^ j) ^ 2) = 1) ∧ IsGrpPullback P₀.A P.A (spMap i₀) φ₀ ∧ IsGrpPullback P₁.A P.A (spMap i₁) φ₁ ∧ LBIso P₀.L (P.L.pull φ₀) ∧ LBIso P₁.L (P.L.pull φ₁) ∧ (∀ a, (levelPoint l₀ h₀ a).left ≫ φ₀ = spMap i₀ ≫ (pt a).left) ∧ ∀ a, (levelPoint l₁ h₁ a).left ≫ φ₁ = spMap i₁ ≫ (pt a).left := by
  first | exact @GlobalTheory.MBLow.exists_family_of_two_fibres | exact GlobalTheory.MBLow.exists_family_of_two_fibres | (intros; apply GlobalTheory.MBLow.exists_family_of_two_fibres <;> assumption)
