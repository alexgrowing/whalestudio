import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ClassSumProbe
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj MvPolynomial
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

set_option autoImplicit false in
open NumberField MvPolynomial in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} in
private theorem mfr_ne_bot : _root_.Formalism.L2.Pj.Mfr l ≠ ⊥ := by
  intro h
  have hM := l.prod
  have h3 := l.three_le
  unfold _root_.Formalism.L2.Pj.Mfr at h
  rw [h, Ideal.mul_bot, eq_comm, Ideal.span_singleton_eq_bot] at hM
  exact absurd (Nat.cast_eq_zero.mp hM) (by omega)

set_option autoImplicit false in
open NumberField MvPolynomial in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} in

theorem _root_.GlobalTheory.ClassSumProbe.finite_conj_half :
    Finite (Dw.La ⧸ (_root_.Formalism.L2.Pj.Mfr l • ⊤ : Submodule (𝓞 E) Dw.La)) := by
  haveI := Dw.fin
  haveI : Finite (𝓞 E ⧸ _root_.Formalism.L2.Pj.Mfr l) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ mfr_ne_bot
  exact Module.finite_of_finite (𝓞 E ⧸ _root_.Formalism.L2.Pj.Mfr l)

end GlobalTheory.ClassSumProbe
