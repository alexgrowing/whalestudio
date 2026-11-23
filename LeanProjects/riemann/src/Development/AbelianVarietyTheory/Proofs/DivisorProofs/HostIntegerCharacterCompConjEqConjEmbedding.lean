import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

set_option autoImplicit false
namespace GlobalTheory.ConjHostChar

theorem embK_bar {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    {l : Level H} (c : Coeff l) (τ : E →+* ℂ) (a : 𝓞 E) :
    embK c τ (H.bar a) = embK c (conjEmb τ) a := by
  apply Subtype.ext
  rw [embK_coe, embK_coe, H.bar_eq, conjEmb, RingHom.comp_apply]
  rw [← ComplexEmbedding.conjugate_coe_eq, IsCMField.complexEmbedding_complexConj]
  simp

theorem conj_char : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (τ : Psi H) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (t : 𝓞 E →+* 𝓞 K), (∀ a, ((t a : 𝓞 K) : K) = algebraMap c.F K (embK c τ.1 a)) → ∀ a, ((t.comp (H.bar : 𝓞 E →+* 𝓞 E) a : 𝓞 K) : K) = algebraMap c.F K (embK c (conjEmb τ.1) a) := by
  intro E _ _ _ H Dw l Xo c τ K _ _ _ t ht a
  rw [RingHom.comp_apply, ht]
  exact congrArg _ (embK_bar H c τ.1 a)

end GlobalTheory.ConjHostChar
