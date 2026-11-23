import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsArcGenericFibrePointsBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_arcGenericFibrePoints_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (S : Scheme.{0}) (A : AnArc (𝓞 E)) (t : SAB H S) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A t y) (F : Type) [Field F] (f : ℂ⸨X⸩ →+* F) (φ : ∀ j, (Σ α : A.X, A.Theta j α) → A.V → F), AnFin A → (∀ (j : ℕ) [NeZero j] i v, φ j i v = f (A.FSum j i.1 i.2 v)) → ∃ Θ : FPts (I := fun j => Σ α : A.X, A.Theta j α) (fun e v => A.actV e v) t (spMap f ≫ y) φ, (∀ v, (Θ.x v).left = spMap f ≫ (Φ.x v).left ∧ ∀ j, ⊤ ≤ (Φ.x v).left ⁻¹ᵁ t.PP.L.U j → Θ.τ v j = f (Φ.τ v j)) ∧ ∀ (k : ℕ) [NeZero k] (ξ : 𝟙_ (Over S) ⟶ t.G) (la : A.La) (ψ : (Σ α : A.X, A.Theta k α) → A.V → ℂ⸨X⸩), Φ.LevelPt k (toUnit _ ≫ ξ) la → (∀ i z, IsFShift A k i.1 i.2 la z (ψ i z)) → Θ.Lev k (toUnit _ ≫ ξ) (fun i z => f (ψ i z)) := by
  first | exact @GlobalTheory.ArcBaseChange.exists_fpts_baseChange | exact GlobalTheory.ArcBaseChange.exists_fpts_baseChange | (intros; apply GlobalTheory.ArcBaseChange.exists_fpts_baseChange <;> assumption)
