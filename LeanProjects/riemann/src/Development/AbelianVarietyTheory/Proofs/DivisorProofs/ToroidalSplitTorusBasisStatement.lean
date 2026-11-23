import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalSplitTorusBasis
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
theorem _root_.GlobalTheory.T.toroidal_split_torus_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)
    (K : Type) [Field K] [CharZero K] (ξ₀ : Sp K ⟶ Xo.XF c) (q : ℕ), q ≠ 0 → (∃ ζ : K, IsPrimitiveRoot ζ q) →
    SplitK Z.t (ξ₀ ≫ Z.j) q → ∀ (N : ℕ) (b : Module.Basis (Fin N) ℤ Dw.La),
    ∃ (s : Fin N → (Over.mk ξ₀ ⟶ Z.oF.t.G)) (ζ : Kˣ), IsPrimitiveRoot ζ q ∧ IsGram Z.oF.t q s ζ (GlobalTheory.EqHalf.gram Dw b) ∧
      (∀ a : Over.mk ξ₀ ⟶ Z.oF.t.G, a ^ q = 1 → ∃ n : Fin N → ℕ, a = ∏ m, s m ^ n m) ∧
      (∀ (α : 𝓞 E) (m : Fin N), s m ≫ Z.oF.t.act.act α = ∏ m', s m' ^ GlobalTheory.EqHalf.latMat Dw b α m' m) := by
  first | exact @GlobalTheory.HalfGeo.gram_basis | exact GlobalTheory.HalfGeo.gram_basis | (intros; apply GlobalTheory.HalfGeo.gram_basis <;> assumption)
