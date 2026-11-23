import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPelUnifOfUnifPow
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DescentOneGenerator
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TwistingStatementsOfLaws
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfCoord
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionIsoOfLinearUniformisationTripleStatement

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowDescent

theorem eq_famCast_of_heq {R : Type} [CommRing R] [IsDomain R] {Dp : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k k' : ℕ} (e : k = k') (r : Fam Dp F k') (s : Fam Dp F k) (h : HEq r s) :
    r = famCast e s := by
  subst e
  exact eq_of_heq h

theorem descent_cast (hL : Laws) (hL2 : Laws2) (hL4 : Laws4) (hT : TwistBaseChangeStatement)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V]
    (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (t : SAB H (Sp V))
    (P : PELUnif (maximalIdeal V) t) (hP : P.TorsionIso) :
    letI := H.starRing
    ∀ (a a' : 𝓞 E) (g g' k : ℕ) (e : 1 * g' = k), 1 ≤ g → 1 ≤ g' → Nat.Coprime g g' →
      a * star a = (g : 𝓞 E) → a' * star a' = (g' : 𝓞 E) →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [IsAlgClosed F] (θ : Fam P.D.toPre F 1)
      (θα : Fam P.D.toPre F (1 * g')), PullAl P.D F P.oD a' 1 g' θ θα →
    ∀ (pb : QkPt P.D.toPre F (1 * g'))
      (wb : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F pb.g.b) (DegPre.lineε (1 * g'))))
      (ζb : F) (xb : TFK (R := V) F ⟶ P.A.A) (tb₀ tb : Fam P.D.toPre F (1 * g')),
      P.ToA F (1 * g') pb xb → xb ≫ P.oA.act (star a') = 1 → wb.IsGen → ζb ≠ 0 →
      FinOrd P.D F (1 * g') pb wb ζb → PhiRel P.D.toPre F (1 * g') pb wb θα tb₀ →
      Fam.IsSmul P.D.toPre F ζb tb₀ tb →
    ∀ (p : QkPt P.D.toPre F (k * g))
      (w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p.g.b) (DegPre.lineε (k * g))))
      (ζ : F) (x : TFK (R := V) F ⟶ P.A.A), w.IsGen → ζ ≠ 0 → FinOrd P.D F (k * g) p w ζ →
      P.ToA F (k * g) p x → x ≫ P.oA.act (star a) = 1 →
    ∀ (s₂ t₀ r : Fam P.D.toPre F (k * g)), PullAl P.D F P.oD a k g (famCast (Dp := P.D.toPre) (F := F) e tb) s₂ →
      PhiRel P.D.toPre F (k * g) p w s₂ t₀ → Fam.IsSmul P.D.toPre F ζ t₀ r →
    ∃ (θα₂ : Fam P.D.toPre F (1 * (g' * g))) (p₂ : QkPt P.D.toPre F (1 * (g' * g)))
      (w₂ : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p₂.g.b) (DegPre.lineε (1 * (g' * g)))))
      (ζ₂ : F) (x₂ : TFK (R := V) F ⟶ P.A.A) (r₀ r₂ : Fam P.D.toPre F (1 * (g' * g))),
      PullAl P.D F P.oD (a * a') 1 (g' * g) θ θα₂ ∧ P.ToA F (1 * (g' * g)) p₂ x₂ ∧
      x₂ ≫ P.oA.act (star (a * a')) = 1 ∧ w₂.IsGen ∧ ζ₂ ≠ 0 ∧ FinOrd P.D F (1 * (g' * g)) p₂ w₂ ζ₂ ∧
      PhiRel P.D.toPre F (1 * (g' * g)) p₂ w₂ θα₂ r₀ ∧ Fam.IsSmul P.D.toPre F ζ₂ r₀ r₂ ∧ HEq r r₂ := by
  letI := H.starRing
  intro a a' g g' k e
  subst e
  exact descent_one_generator hL hL2 hL4 hT V E H t P hP a a' g g'

theorem descentIdF_of_laws :
    Laws → Laws2 → Laws3 → Laws4 → Laws5 → TwistBaseChangeStatement → DescentIdF := by
  intro hL hL2 hL3 hL4 hL5 hT E _ _ _ H Dw l Xo c n
  letI := H.starRing
  intro T io y _ C P _ g g' hg hg' hne _ _ π π' hπ hπ' _ _ _ F _ _ _ _ _ _ v ϖ _ _ Q _ D' A' G' gr cm pD pA pG U' PU
    md oD' hx hoD oA' hoA θ θα hθ pb wb ζb xb tb₀ tb hxb hxba hwb hζb hfb hΦb hsb p w ζ x hw hζ hf hpx hxπ
    s₂ t₀ r hs₂ hΦ hr
  obtain ⟨oA'', hoA'', t', P', e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉⟩ :=
    exists_pelUnif_of_unifPow hL hL2 hL4 hT T.V E H C.I.G P n D' A' G' pD pA pG U' PU oD' hx hoD
  have hact : ∀ a, oA'.act a = oA''.act a := fun a =>
    Fan.IsLimit.hom_ext pA.lim _ _ fun i => (hoA a i).trans (hoA'' a i).symm
  have hxa : x ≫ oA''.act (star (star π)) = 1 := by
    refine Fan.IsLimit.hom_ext pA.lim _ _ fun i => ?_
    have := pA.hom i
    change (x ≫ oA''.act (star (star π))) ≫ pA.pr i = 1 ≫ pA.pr i
    rw [star_star, Category.assoc, hoA'', hxπ, MonObj.one_comp]
  have htors : P'.TorsionIso :=
    GlobalTheory.T.torsionIso_of_linear_uniformisation_triple ⟨hL, hL2, hL3, hL4, hL5⟩ (twistBCSpan_of hT) GlobalTheory.RatioVal.main
      (twisting_statements_of_laws hL hT).1 (GlobalTheory.UnitBallFree.main hL.globalFns hT) E H T.V (maximalIdeal T.V)
      ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩ t' P'
  rw [hact] at hxba
  simp only [hact]
  clear hoA hact hoA'' hxπ hx hoD PU pD pA pG
  subst e₁ e₄ e₇
  cases e₂
  cases e₃
  cases e₅
  cases e₆
  cases e₈
  cases e₉
  obtain ⟨θα₂, p₂, w₂, ζ₂, x₂, r₀, r₂, k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈, k₉⟩ :=
    descent_cast hL hL2 hL4 hT T.V E H t' P' htors (star π) (star π') g g' g' (one_mul g') hg.one_le hg'.one_le
      ((Nat.coprime_primes hg hg').2 hne) (by rw [star_star, _root_.mul_comm, hπ])
      (by rw [star_star, _root_.mul_comm, hπ']) F θ θα hθ pb wb ζb xb tb₀ tb hxb hxba hwb hζb hfb hΦb hsb
      p w ζ x hw hζ hf hpx hxa s₂ t₀ r hs₂ hΦ hr
  exact ⟨θα₂, p₂, w₂, ζ₂, x₂, r₀, r₂, k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈, eq_famCast_of_heq _ _ _ k₉⟩

end GlobalTheory.PowDescent
