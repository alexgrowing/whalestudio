import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalTorusSectionsBasis
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatMatTransposeMulGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthLetters
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.HtGen GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.HalfGeo
open Formalism.MainNotions.DIV.Cons (intO)
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toroidal_torus_sections_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)
    (K : Type) [Field K] (ξ₀ : Sp K ⟶ Xo.XF c) (ξ : Sp K ⟶ Z.X), ξ₀ ≫ Z.j = ξ → ∀ q : ℕ, q ≠ 0 →
    ∀ (N : ℕ) (b : Module.Basis (Fin N) ℤ Dw.La) (s : Fin N → (Over.mk ξ₀ ⟶ Z.oF.t.G)) (ζ : Kˣ),
    IsGram Z.oF.t q s ζ (GlobalTheory.EqHalf.gram Dw b) → (∀ a : Over.mk ξ₀ ⟶ Z.oF.t.G, a ^ q = 1 → ∃ n : Fin N → ℕ, a = ∏ m, s m ^ n m) →
    (∀ (α : 𝓞 E) (m : Fin N), s m ≫ Z.oF.t.act.act α = ∏ m', s m' ^ GlobalTheory.EqHalf.latMat Dw b α m' m) →
    ∀ χ : Fin N → (TorsK Z.t ξ q →* Kˣ), (∀ m, IsWeilHom Z.oF.t Z.m.φ (s m) (χ m)) →
    ∀ (α : 𝓞 E) (k k' : TorsK Z.t ξ q), k'.1 = k.1 ≫ Z.t.act.act α →
      ∀ m, χ m k' = ∏ m', χ m' k ^ GlobalTheory.EqHalf.chiAct Dw b α m m' := by
  first | exact @GlobalTheory.WeilEquivar.equivar_field | exact GlobalTheory.WeilEquivar.equivar_field | (intros; apply GlobalTheory.WeilEquivar.equivar_field <;> assumption)
