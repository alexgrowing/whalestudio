import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TangentConstantDirectionSpecialisesDeriv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_constant_direction_specialises_deriv : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (Ψ : SpecPts Φ Γ), AnFin A → Φ.Rational → ∀ (z₀ : A.V) (ν : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback o.t.G.hom y), Φ.IsTan z₀ ν → ∃ T' ≥ Ψ.T, ∀ (w : ℂ) (hw : Ψ.T < w.im), T' < w.im → ∃ νt : Sp (DualNumber (Γ.R w)) ⟶ o.t.G.left, νt ≫ o.t.G.hom = spMap (algebraMap (Γ.R w) (DualNumber (Γ.R w))) ≫ spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT ∧ (∀ ρ : DualNumber (Γ.R w) →+* DualNumber ℂ⸨X⸩, (∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (r : ℂ⸨X⸩)) → ρ DualNumber.eps = DualNumber.eps → spMap ρ ≫ νt = ν ≫ pullback.fst _ _) ∧ ∀ ρ : DualNumber (Γ.R w) →+* DualNumber ℂ, (∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (Γ.ev w r)) → ρ DualNumber.eps = DualNumber.eps → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap ρ ≫ νt = (Ψ.pi w 0).left ∧ ∀ (W : o.t.G.left.Opens) (f : Γ(o.t.G.left, W)), ⊤ ≤ (Ψ.pi w 0).left ⁻¹ᵁ W → TrivSqZeroExt.snd (valR (spMap ρ ≫ νt) W f) = fderiv ℂ (fun v => valAt' (Ψ.pi w v).left W f) 0 z₀ := by
  first | exact @GlobalTheory.SpecTangent.spec_tangent | exact GlobalTheory.SpecTangent.spec_tangent | (intros; apply GlobalTheory.SpecTangent.spec_tangent <;> assumption)
