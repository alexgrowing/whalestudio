import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsScalarHeckeTraceThetaGeneratorFamily
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scalar_heckeTrace_thetaGenerator_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i n : ℕ) (T : Type) [CommRing T] [IsReduced T] [Algebra c.F T] (y : FrPt Xo c T) (x' : Sp T ⟶ Xo.X) (Ψ : Gx y.x ⟶ Gx x') (σ : Fin n → (Over.mk y.x ⟶ Xo.univ.t.G)) (s₀ : LB.Sec (PPx x')), admitted l P p → IsHeckeFam P p i Ψ → IsListed Ψ σ → SecGen x' s₀ → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (χ : T →ₐ[c.F] Ω) (y₁ : FrPt Xo c Ω) (x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx y₁.x ⟶ Gx x₁'), FrMap χ y y₁ → IsFib χ.toRingHom Ψ Ψ₁ → ∃ s', IsThGen x₁' s' ∧ IsThetaTrace Xo.univ.t.G Xo.univ.t.PP Ψ₁ p y₁.s s') → ∃ a : T, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (χ : T →ₐ[c.F] Ω) (y₁ : FrPt Xo c Ω) (x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx y₁.x ⟶ Gx x₁') (s' : LB.Sec (PPx x₁')), FrMap χ y y₁ → IsFib χ.toRingHom Ψ Ψ₁ → IsThGen x₁' s' → IsThetaTrace Xo.univ.t.G Xo.univ.t.PP Ψ₁ p y₁.s s' → SecBC χ.toRingHom a x' x₁' s₀ s' := by
  first | exact @GlobalTheory.HeckeScal.exists_scal_of_family | exact GlobalTheory.HeckeScal.exists_scal_of_family | (intros; apply GlobalTheory.HeckeScal.exists_scal_of_family <;> assumption)
