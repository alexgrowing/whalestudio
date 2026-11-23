import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelledLatticeEquivOfCommonFibre
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_labelled_lattice_equiv_of_common_fibre : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (_ : ZHOut X₁.ρ Y U₀ EE) (q : Y.Z ⟶ X₁.M.Z), X₁.S.Over₀ Y U₀ → X₁.S.IsEE Y U₀ EE → IsProper q → Y.pt ≫ q = X₁.M.pt → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z), _root_.IsPreconnected (q.base ⁻¹' {z₁}) → ∀ (c c' : CTrait X₁ p z₁) (y y' : Sp (OO p) ⟶ Y.Z), y ≫ q = c.y → y' ≫ q = c'.y → ∀ (yy : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)) (yy' : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c'.T.D.toPre.X)), IsLab X₁ ε₁ c yy → IsLab X₁ ε₁ c' yy' → ∃ θ : (Fin 8 → c.T.D.toPre.X) ≃+ (Fin 8 → c'.T.D.toPre.X), (∀ a μ, yy a = QuotientAddGroup.mk μ → yy' a = QuotientAddGroup.mk (θ μ)) ∧ ∀ (E : Matrix (Fin 8) (Fin 8) ℤ) (v : Fin 8 → c.T.D.toPre.X), θ (fun a => ∑ b, E a b • v b) = fun a => ∑ b, E a b • θ v b := by
  first | exact @GlobalTheory.Poinc.FibLat.exists_equiv_of_fibre | exact GlobalTheory.Poinc.FibLat.exists_equiv_of_fibre | (intros; apply GlobalTheory.Poinc.FibLat.exists_equiv_of_fibre <;> assumption)
