import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentPointCmEigenFrame
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsValFam
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeVectorBundleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalAtLocalRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
open GlobalTheory.CompanionTheory.Ar.Flat.Rep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.component_point_cm_eigen_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → ∀ (F : Type) [Field F] (βF : c.F →+* F) (y : Sp F ⟶ Xo.XF c), y ≫ pullback.snd _ _ = spMap βF → Set.range y ⊆ U → ∀ (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (σ : E →+* ℂ) (n : ℕ) (b : Fin n → Z.V), (Z.eig σ).IsFrameAt b ⟨_, h⟩ → ∃ v : Vecs y n, IsValFam Z y b v ∧ IsEigFrame Xo.univ.t.act (under y) (βF.comp (tauIn c σ)) v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.Rep.valFam_eigFrame | exact GlobalTheory.CompanionTheory.Ar.Flat.Rep.valFam_eigFrame | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.Rep.valFam_eigFrame <;> assumption)
