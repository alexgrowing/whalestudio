import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformisedEigenFramesTwo
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformised_eigen_frames_two : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ τ' : E →+* ℂ) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H D.p D.q ty → τ' (H.rt : E) = H.rt0 → (∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E)) → ∀ (e : ∀ i : Fin FU.n, Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : Fin FU.n → ℂ) (Φ : CFn Xo c), (∀ i, LinearIndependent (𝓞 E) (e i)) → (∀ i, IsFlatAn Set.univ τ τ' σ Φ FU i (e i) (ρ i)) → ∀ (R : Type) [CommRing R] (x : Sp R ⟶ Xo.XF c) (vR : Fin D.p → (epsAt (under x) ⟶ Xo.univ.t.G)) (wR : Fin D.q → (epsAt (under x) ⟶ Xo.univ.t.G)) (m : ℕ) (B : Set (Fin m → ℂ)) (ψ : (Fin m → ℂ) → (R →+* ℂ)) (v : ∀ b, Vecs (spMap (ψ b) ≫ x) D.p) (w : ∀ b, Vecs (spMap (ψ b) ≫ x) D.q), IsOpen B → (∀ r, DifferentiableOn ℂ (fun b => ψ b r) B) → (∀ b ∈ B, IsFramed Set.univ τ σ (spMap (ψ b) ≫ x) (v b) (w b) ∧ (∀ a, (v b a).left = spMap (dualMap (ψ b)) ≫ (vR a).left) ∧ ∀ j, (w b j).left = spMap (dualMap (ψ b)) ≫ (wR j).left) → DifferentiableOn ℂ (fun b => Φ (spMap (ψ b) ≫ x) (v b) (w b)) B := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.anHol | exact GlobalTheory.CompanionTheory.Ar.Flat.anHol | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.anHol <;> assumption)
