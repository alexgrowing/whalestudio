import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrTanPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.BoxTuple
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrTanDirAlg

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDir

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.FrTan

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_char {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    (T : CDVR) (io : c.F →+* T.Fr) (σ : E →+* ℂ) :
    ∃ χ : 𝓞 E →+* T.V, ∀ a : 𝓞 E, algebraMap T.V T.Fr (χ a) = io (embK c σ a) := by
  have hint : ∀ a : 𝓞 E, ∃ z : T.V, algebraMap T.V T.Fr z = io (embK c σ a) := by
    intro a
    have h1 : IsIntegral T.V ((io.comp (embK c σ)) a) :=
      IsIntegral.map_of_comp_eq (Int.castRingHom T.V) (io.comp (embK c σ)) (RingHom.ext_int _ _)
        (RingOfIntegers.isIntegral a)
    exact IsIntegrallyClosed.isIntegral_iff.1 h1
  choose χ hχ using hint
  refine ⟨{ toFun := χ, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hχ⟩ <;>
    intros <;> apply IsFractionRing.injective T.V T.Fr <;> simp [hχ]

end Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDir
