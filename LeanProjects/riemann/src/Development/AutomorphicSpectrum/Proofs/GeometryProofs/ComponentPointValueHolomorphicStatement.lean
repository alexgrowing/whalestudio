import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentPointValueHolomorphic
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.component_point_value_holomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (y₀ : Sp ℂ ⟶ Xo.XF c), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → y₀ ≫ pullback.snd _ _ = spMap σ → Set.range y₀ ⊆ U → ∃ (V₀ : (Xo.XF c).Opens) (hV₀ : IsAffineOpen V₀) (c₁ : Fin D.p → Z.V) (c₂ : Fin D.q → Z.V) (vR : Fin D.p → (epsAt (under hV₀.fromSpec) ⟶ Xo.univ.t.G)) (wR : Fin D.q → (epsAt (under hV₀.fromSpec) ⟶ Xo.univ.t.G)), ⊤ ≤ y₀ ⁻¹ᵁ V₀ ∧ LinearIndependent Z.Ω c₁ ∧ Submodule.span Z.Ω (Set.range c₁) = eigSp Z.ρ (Z.inc.comp (tauIn c τ)) ∧ LinearIndependent Z.Ω c₂ ∧ Submodule.span Z.Ω (Set.range c₂) = eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ))) ∧ ∀ (χ : Γ(Xo.XF c, V₀) →+* ℂ) (v : Vecs (spMap χ ≫ hV₀.fromSpec) D.p) (w : Vecs (spMap χ ≫ hV₀.fromSpec) D.q), (spMap χ ≫ hV₀.fromSpec) ≫ pullback.snd _ _ = spMap σ → Set.range (spMap χ ≫ hV₀.fromSpec) ⊆ U → (∀ a, (v a).left = spMap (dualMap χ) ≫ (vR a).left) → (∀ j, (w j).left = spMap (dualMap χ) ≫ (wR j).left) → IsFramed U τ σ (spMap χ ≫ hV₀.fromSpec) v w ∧ (∀ i, ∃ v', Z.M.ValAt ((spMap χ ≫ hV₀.fromSpec) ≫ Y.j) (c₁ i) v' ∧ SameVec Y (spMap χ ≫ hV₀.fromSpec) (v i) v') ∧ ∀ j, ∃ w', Z.M.ValAt ((spMap χ ≫ hV₀.fromSpec) ≫ Y.j) (c₂ j) w' ∧ SameVec Y (spMap χ ≫ hV₀.fromSpec) (w j) w' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFrames.exists_local_eigenframes | exact GlobalTheory.CompanionTheory.Ar.LocFrames.exists_local_eigenframes | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFrames.exists_local_eigenframes <;> assumption)
