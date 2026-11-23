import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelIsometryOfPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelIsometry_of_point_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (A : Type) [CommRing A] [IsDomain A] (P : Out.PolAV (Sp A)) (act : 𝓞 E → (P.A ⟶ P.A)) (z : A) (κ : Type) (lam : κ → D.La) (pt : κ → (Out.baseOver (Sp A) ⟶ P.A)) (n m N : ℕ), 0 < n → 0 < N → Nonempty (ℚ →+* A) → z ^ N = 1 → (∀ i, pt i ^ N = 1) → (∀ a, IsMonHom (act a)) → (∃ (K : Type) (_ : Field K) (β : A →+* K) (ζ : Kˣ) (ev : D.La → (Over.mk (spMap β) ⟶ P.A)), IsPrimitiveRoot ζ n ∧ (∀ a c, ev (a + c) = ev a * ev c) ∧ (∀ a, ev a ^ n = 1) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = ev a ≫ act c) ∧ (∀ a c, Out.WeilIs P.A P.L n (ev a) (ev c) (unitOn (ζ ^ D.EF a c))) ∧ (ζ : K) ^ m = β z ∧ ∀ i, ev (lam i) ^ m = (Over.homMk (spMap β) (by simp) : Over.mk (spMap β) ⟶ Out.baseOver (Sp A)) ≫ pt i) → ∀ (K : Type) [Field K] [IsAlgClosed K] (β : A →+* K), ∃ (ζ : Kˣ) (ev : D.La → (Over.mk (spMap β) ⟶ P.A)), IsPrimitiveRoot ζ n ∧ (∀ a c, ev (a + c) = ev a * ev c) ∧ (∀ a, ev a ^ n = 1) ∧ (∀ (c : 𝓞 E) a, ev (c • a) = ev a ≫ act c) ∧ (∀ a c, Out.WeilIs P.A P.L n (ev a) (ev c) (unitOn (ζ ^ D.EF a c))) ∧ (ζ : K) ^ m = β z ∧ ∀ i, ev (lam i) ^ m = (Over.homMk (spMap β) (by simp) : Over.mk (spMap β) ⟶ Out.baseOver (Sp A)) ≫ pt i := by
  first | exact @GlobalTheory.exists_levelIsometry_of_point | exact GlobalTheory.exists_levelIsometry_of_point | (intros; apply GlobalTheory.exists_levelIsometry_of_point <;> assumption)
