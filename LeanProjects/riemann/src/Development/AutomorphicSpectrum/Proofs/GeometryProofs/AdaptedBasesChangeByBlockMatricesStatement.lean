import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdaptedBasesChangeByBlockMatrices
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_bases_change_by_block_matrices : ∀ (E : Type) [Field E] [NumberField E] (K W : Type) [Field K] [AddCommGroup W] [Module K W]
    (ρH : 𝓞 E →+* Module.End K (W × Module.Dual K W)) (σ : E →+* K) (p q : ℕ) (v v' : Fin p → W) (w w' : Fin q → W)
    (u u' : Fin (p + q) → W × Module.Dual K W) (P : Matrix (Fin p) (Fin p) K) (Q : Matrix (Fin q) (Fin q) K),
    IsAdapted ρH σ v w u → IsAdapted ρH σ v' w' u' → LinearIndependent K v →
    Submodule.span K (Set.range u) = HT.eigSp ρH σ →
    (∀ i, v' i = ∑ k, P i k • v k) → (∀ i, w' i = ∑ k, Q i k • w k) →
    ∃ B : Matrix (Fin (p + q)) (Fin (p + q)) K, (∀ i, u' i = ∑ k, B i k • u k) ∧ B.det * Q.det = P.det := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.exists_det_mul_eq_of_isAdapted | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.exists_det_mul_eq_of_isAdapted | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.exists_det_mul_eq_of_isAdapted <;> assumption)
