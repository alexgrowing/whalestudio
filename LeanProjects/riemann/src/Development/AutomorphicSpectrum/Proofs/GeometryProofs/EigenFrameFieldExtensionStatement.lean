import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFrameFieldExtension
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_frame_field_extension : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] (x : Sp F ⟶ S) [Smooth G.hom] (P : Type) [CommRing P] (act : OAct P G) (σ : P →+* F) (F' : Type) [Field F'] (f : F →+* F') (x' : Sp F' ⟶ S), spMap f ≫ x = x' → ∀ (n : ℕ) (v : Fin n → (epsAt x ⟶ G)) (v' : Fin n → (epsAt x' ⟶ G)), (∀ i, (v' i).left = spMap (dualMap f) ≫ (v i).left) → IsEigFrame act x σ v → IsEigFrame act x' (f.comp σ) v' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.EigBase.isEigFrame_base | exact GlobalTheory.CompanionTheory.Ar.EigBase.isEigFrame_base | (intros; apply GlobalTheory.CompanionTheory.Ar.EigBase.isEigFrame_base <;> assumption)
