import Mathlib
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBareNormDisc
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionAnalyticNorm
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitAnalyticFunction
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexUniformisationHolds
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FrameRatioConstantRational
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

namespace PositivityTheory.Xgn.LineFunctionModelRatio₂

theorem exists_typeFn {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q : ℕ) :
    ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H p q ty := by
  classical
  let m : (E →+* ℂ) → ℕ := fun τ => if τ (H.rt : E) = H.rt0 then p else q
  let e := Fintype.equivFin (Σ τ : E →+* ℂ, Fin (m τ))
  refine ⟨_, fun i => (e.symm i).1, ?_⟩
  have key : ∀ τ : E →+* ℂ, Nat.card {i // (e.symm i).1 = τ} = m τ := by
    intro τ
    have e1 : {i // (e.symm i).1 = τ} ≃ Fin (m τ) :=
      (e.symm.subtypeEquiv (fun _ => Iff.rfl)).trans (Equiv.sigmaSubtype τ)
    rw [Nat.card_congr e1, Nat.card_fin]
  intro τ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [key]; simp [m, h]
  · rw [key]; simp [m, h]

end PositivityTheory.Xgn.LineFunctionModelRatio₂

theorem PositivityTheory.Xgn.line_function_model_ratio : Geo.ResK.ResKStatement → GagaSections → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Y' : Model Xo c β') (U : Set (Xo.XF c)) (Z : CptOver Y U) (Z' : CptOver Y' U) (τ : E →+* ℂ) (φ φ' : FrameFn Xo c), FracBase β → FracBase β' → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → Z.IsGeom → Z'.IsGeom → FlatOnModel Z τ φ → FlatOnModel Z' τ φ' → ∃ x : c.F, x ≠ 0 ∧ ∀ (F : Type) [Field F] (βF : c.F →+* F) y v w, IsFramed U τ βF y v w → φ' F y v w = βF x * φ F y v w := by
  intro hR hG E _ _ _ H D l Xo c O _ β Y O' _ β' Y' U Z Z' τ φ φ' hO hO' hpq hτ hZ hZ' hφ hφ'
  obtain ⟨g, ty, hty⟩ := PositivityTheory.Xgn.LineFunctionModelRatio₂.exists_typeFn H D.p D.q
  obtain ⟨FU⟩ := GlobalTheory.CompanionTheory.Ar.Top.complex_uniformisation_holds E H D l Xo
    ((algebraMap c.F ℂ).comp (IntermediateField.inclusion c.le).toRingHom) g ty hpq rfl hty
  obtain ⟨Φ, hΦ, -⟩ := GlobalTheory.CompanionTheory.Ar.Flat.anUnit E H D l Xo c τ τ (algebraMap c.F ℂ) g ty FU hty hτ (fun _ => rfl)
  obtain ⟨κ, hκ, h₁⟩ := GlobalTheory.CompanionTheory.Ar.Flat.flat_eq_const_mul_unitAn hR hG E H D l Xo c O β Y U Z τ
    (algebraMap c.F ℂ) Φ φ hO hpq hτ hτ hZ hΦ hφ.1 hφ
  obtain ⟨κ', -, h₂⟩ := GlobalTheory.CompanionTheory.Ar.Flat.flat_eq_const_mul_unitAn hR hG E H D l Xo c O' β' Y' U Z' τ
    (algebraMap c.F ℂ) Φ φ' hO' hpq hτ hτ hZ' hΦ hφ'.1 hφ'
  refine PositivityTheory.Xgn.frame_ratio_constant_rational E H D l Xo c U τ φ φ' (κ' / κ) hτ hφ.1 hφ'.1 fun y v w hf => ?_
  rw [h₁ y v w hf, h₂ y v w hf]
  field_simp
