import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLinePAdicFrame
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_line_p_adic_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (ϖ : O) (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (φ : FrameFn Xo c) (𝓗 : HodgeLat Z.M.lat Z.ρ H.bar (D.p + D.q)) (σ : E →+* Z.Ω) (v : Fin D.p → Z.V) (w : Fin D.q → Z.V) (u : Fin (D.p + D.q) → Z.V × Module.Dual Z.Ω Z.V) (α κ' : Z.Ω) (M : ℕ) (a : ℤ), τ (H.rt : E) = H.rt0 → Irreducible ϖ → Function.Injective β → (∀ x : c.F, ‖κ x‖ ≤ 1 ↔ x ∈ β.range) → (∀ b : 𝓞 E, σ (b : E) = Z.inc (tauIn c τ b)) → LinearIndependent Z.Ω v → Submodule.span Z.Ω (Set.range v) = HT.eigSp Z.ρ σ → LinearIndependent Z.Ω w → Submodule.span Z.Ω (Set.range w) = eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ))) → IsAdapted 𝓗.ρH σ v w u → 0 < M → (∀ x, OrderAt (detLat (𝓗.quot σ) u) (α / κ') (Z.inc (β ϖ)) M a x) → κ' ≠ 0 → Represents Y U τ Z.M (α • exteriorPower.ιMulti Z.Ω D.p v) (κ' • exteriorPower.ιMulti Z.Ω D.q w) φ → IsLineFn U τ φ → ∃ t : ℝ, HasFinNorm U τ φ p κ t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.value_at_point | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.value_at_point | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.value_at_point <;> assumption)
