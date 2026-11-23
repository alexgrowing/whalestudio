import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LocalValuationColumns
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.CanonicalHarmonicGerms
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralChartFormalBiextensionGaugeBound
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ReachedSectionRegularOnIntegralModelStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralChartFormalBiextensionGaugeBoundStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueChainRuleNormalizedPullbackStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RegularSectionIntegralGermUniqueScaleStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MixedTranslatePullbackEqReachedSectionStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueIntegralPointEqValueOnBiextensionCoStatement

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RefSum.TermLoc

theorem harmonic_value_ge_local_depth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), Good3 C → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), 0 < e → ∀ P : MvPolynomial (LtN Dw n) c.F, P ∈ harmA (Dw := Dw) c w n → (∀ k, (ρ : EReal) ≤ nuLocOf C e k (MvPolynomial.map io P)) → ∀ (N : ℕ), Odd N → IsUnit (N : T.V) → ∀ (x₂ : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo (xOf y)))), (∀ b, x₂ b ^ (N ^ 2) = 1 ∧ IsUUOver Xo.univ.t.G Xo.univ.t.PP N (sOf1 y) 1 (x₂ b) (F b)) → letI := io.toAlgebra; (ρ : EReal) ≤ nval T.V e (hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F b)) P) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y C hC nab hnab e ρ w n he P hP hloc N hN hu x₂ F hF
  letI := io.toAlgebra
  have hst : ∀ a : 𝓞 E, star a = H.bar a := fun _ => rfl
  have hone : ∀ {Z : Over Xo.X} (t : Z ⟶ Xo.univ.t.G), t ≫ Xo.univ.t.act.act 1 = t := fun t => by
    rw [Xo.univ.t.act.one, Category.comp_id]
  have hmix := fun b => (GlobalTheory.T.mixed_translate_pullback_eq_reached_section E H Dw l Xo T.Fr (xOf y) N N 1 1 1 1 hN (by simp) (by simp) (by simp)
    (sOf1 y) 1 (x₂ b) (F b) (one_pow _) (hF b).1 (by rw [_root_.mul_one, hone, one_pow]) (by rw [hone, _root_.mul_one]; exact (hF b).1)
    (hF b).2).2
  choose hh hre hpl using hmix
  have hg := fun b => (GlobalTheory.T.regular_section_integral_germ_unique_scale E H Dw l Xo c hst T io y C hC.1 _ (hh b)).1
    (GlobalTheory.T.reachedSection_regular_on_integralModel E H Dw l Xo c hst T io y C hC _ (hh b) (hre b))
  choose f hf using hg
  obtain ⟨B, hB1, -⟩ := GlobalTheory.T.integralChart_formalBiextension_gauge_bound E H Dw l Xo c hst T io y C
  have hHH : P ∈ HH c w n := hP.1
  have hni := GlobalTheory.T.harmonicValue_integralPoint_eq_value_on_biextensionCopies E H Dw l Xo c hst T io y C nab hnab B hB1 _ n hh f hf w P hHH
  have hch := GlobalTheory.T.harmonic_value_chain_rule_normalized_pullback E H Dw l Xo c hst nab hnab T.Fr y.1 1 1 (N ^ 2 * 1) (N ^ 2) (by simp) (by ring) n hh
    (fun b => sqN Xo N (F b)) hpl w P hHH
  have hn1 : nrm Dw c w (1 : 𝓞 E) = 1 := by simp [nrm]
  rw [hch, hn1, map_one, _root_.one_mul, hni]
  obtain ⟨hF', hA', -, -, -, -, -⟩ := C.gen.1
  obtain ⟨e1, e2, -, -, -, -⟩ := hB1
  have eF : B.FK T.Fr = C.ch.B.FK T.Fr := by
    funext i
    change MvPowerSeries.map _ (B.G.F i) = MvPowerSeries.map _ (C.ch.B.G.F i)
    rw [GlobalTheory.ChartBiext.toK_self, hF', e1]
  have eA : ∀ a, B.actK T.Fr a = C.ch.B.actK T.Fr a := by
    intro a
    funext i
    change MvPowerSeries.map _ (B.A.act a i) = MvPowerSeries.map _ (C.ch.B.A.act a i)
    rw [GlobalTheory.ChartBiext.toK_self, hA', e2]
  rw [GlobalTheory.ChartBiext.nabValN_congr B C.ch.B eF eA]
  refine (hloc (N ^ 2 * 1)).trans ?_
  unfold nuLocOf
  refine iInf_le_of_le (FB.toK T.Fr (∏ b, evV (n := n) ![pt T.V (chD C.ch) b] (f b))) (iInf_le_of_le ?_ le_rfl)
  intro m
  exact ⟨_, (MvPowerSeries.coeff_map _ _ _).symm⟩

end GlobalTheory.RefSum.TermLoc
