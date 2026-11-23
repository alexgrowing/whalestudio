import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeIsometryConjPointSplitUpToIndex
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_isometry_conj_point_split_up_to_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ (C : Curve H) (io : C.P.A.left ⟶ C.P.A.left), IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (i' : Fin F.n) (P' : (F.Di i').La →+ (Fin g → ℂ)) (hP' : IsPeriod (F.Di i') ty P') (N : ℕ), 0 < N → (∀ v : (F.Di i).La, N • v ∈ lat hP H.rt0 ⊔ lat hP (-H.rt0)) → spMap (τ : ℂ →+* ℂ) ≫ F.u i P = F.u i' P' → C.ActsBy τ io N (1, 0) → ∃ Φ : (F.Di i).La ≃ₗ[𝓞 E] (F.Di i').La, (∀ a b, (F.Di i').EF (Φ a) (Φ b) = (F.Di i).EF a b) ∧ (∀ a ∈ lat hP H.rt0, Φ a ∈ lat hP' H.rt0) ∧ (∀ a ∈ lat hP (-H.rt0), Φ a ∈ lat hP' (-H.rt0)) ∧ ∀ n : ℕ, 0 < n → C.ActsBy τ io (N * n) (1, 0) → ∀ v, spMap (τ : ℂ →+* ℂ) ≫ (F.ex i P ((n : ℂ)⁻¹ • P v)).left = (F.ex i' P' ((n : ℂ)⁻¹ • P' (Φ v))).left := by
  first | exact @GlobalTheory.CompRat.exists_isometry_of_conj_split_index | exact GlobalTheory.CompRat.exists_isometry_of_conj_split_index | (intros; apply GlobalTheory.CompRat.exists_isometry_of_conj_split_index <;> assumption)
