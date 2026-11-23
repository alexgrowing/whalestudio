import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealAlongMonomialFamilyEqSpanMonomial
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealAlong_monomialFamily_eq_span_monomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (φ : InvFun (𝓞 E)), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (d : ℕ) (J : C.Z.IdealSheafData), (∀ x ∈ J.support, x ∉ Set.range C.i) → UValOn Xo c C.i φ J d → ∀ (S : Scheme.{0}) (π : S ⟶ pullback C.z (spMap C.b)), IsNormBl π (J.comap (pullback.fst C.z (spMap C.b))) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V), GlobalTheory.Mum.Base V → ∀ ξ : Sp V ⟶ S, Cm.y ≫ C.iF = jK V ≫ ξ ≫ π → ∃ b : Fin Cm.m → ℕ, (∀ k, (b k : ℝ) = d * φ.evalZ ((l.M' : ℤ) • Cm.δ k)) ∧ idlAlong J (ξ ≫ π ≫ pullback.fst C.z (spMap C.b)) = Ideal.span {∏ k, Cm.s k ^ b k} := by
  first | exact @GlobalTheory.UGZero.idlAlong_eq_span_monomial | exact GlobalTheory.UGZero.idlAlong_eq_span_monomial | (intros; apply GlobalTheory.UGZero.idlAlong_eq_span_monomial <;> assumption)
