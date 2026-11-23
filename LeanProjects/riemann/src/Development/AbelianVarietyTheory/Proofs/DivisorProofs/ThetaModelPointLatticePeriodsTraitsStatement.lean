import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModelPointLatticePeriodsTraits
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaModel_point_lattice_periods_traits : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SharpOver F W ρ.P u → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ x : M.Z, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (j : M.Z.presheaf.stalk x →+* R) (Λ : Type) (_ : AddCommGroup Λ) (p : Λ → R) (c : ℕ), GlobalTheory.Mum.Base R ∧ IsCpl j ∧ 1 ≤ c ∧ ∀ (T : Trait F) (ψ : R →+* T.V), IsLocalHom ψ → ThroughU M V v (𝟙 F.X) T (spMap (ψ.comp j) ≫ M.Z.fromSpecStalk x) → ∃ e : Λ ≃+ T.D.toPre.X, ∀ y, ∃ k : ℕ, (k : ℤ) = c * T.β (e y) (e y) ∧ Associated (ψ (p y)) (T.ϖ ^ k) := by
  first | exact @GlobalTheory.Poinc.Periods.main | exact GlobalTheory.Poinc.Periods.main | (intros; apply GlobalTheory.Poinc.Periods.main <;> assumption)
