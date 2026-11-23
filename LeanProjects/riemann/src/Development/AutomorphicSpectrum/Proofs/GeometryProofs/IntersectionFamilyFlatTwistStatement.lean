import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionFamilyFlatTwist
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_family_flat_twist : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (W : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (A : HermLine ι) (S : FlatHerm y φ A) (d : ℕ) (u : ((Σ k, ι k) → ℂ) → ℝ), IsIntersectionFamily I → IsArithVar (mCoordIdeal y) d → OverInt y φ → mCoordIdeal y ≤ W → IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsPlaceWeight y φ (fun σ => Real.log (S.κ σ)) u → I W (n + 1) (Fin.snoc L A) = -ptsIntegral W (pot L) u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FlatHerm.inter_eq_neg_integral | exact GlobalTheory.CompanionTheory.Ar.Flat.FlatHerm.inter_eq_neg_integral | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FlatHerm.inter_eq_neg_integral <;> assumption)
