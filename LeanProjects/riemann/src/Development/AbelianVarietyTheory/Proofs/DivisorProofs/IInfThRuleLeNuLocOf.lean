import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LocalValuationColumns
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IInfThetaGeneratorsLeLocalDepthPrimeToLevel
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueTranslateEqUnitMulNormaliserThetaVa
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValueTranslatePullbackEqGenerator
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsProductDataCopiesTrivialisationValuation
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PointStatementsOnCopiesHold
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueExistsUniqueOfChartIndependence
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
open Limits MonoidalCategory CartesianMonoidalCategory MonObj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open GlobalTheory.ThetaLeast

namespace GlobalTheory.RefSum

theorem iInf_thRule_le_nuLocOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → y.IsAlg → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (r : ℕ) (Φ M0 : ℝ), ShortBasis Q r Φ M0 → ∀ (α : 𝓞 E), α * star α = ((l.M : ℕ) : 𝓞 E) → l.Mb = Ideal.span {star α} → IsUnit ((l.M : ℕ) : T.V) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n e : ℕ), 1 ≤ n → 0 < e → 4 * DF Dw a + 4 ≤ l.M → (DF Dw a : ℝ) * M0 < l.M → ∀ P₁ ∈ harmA (Dw := Dw) c a n, (⨅ (f : Rul Xo c) (_ : ∃ x : Fin n → Dw.La, IsThRule Xo c nab x P₁ f), nval T.V e (evI y f)) ≤ nuLocOf C e l.M (MvPolynomial.map io P₁) + (((DF Dw a : ℝ) ^ 2 * Φ / l.M / e : ℝ) : EReal) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro nab hnab T io y C hTr P hP hy ϖ hϖ Q hQ r Φ M0 hSB α hα hMb hu a n e hn he h4 hM0 P₁ hP₁
  obtain ⟨hΦ, b, hb, hb'⟩ := hSB
  have hth : ThValTot Xo c nab :=
    GlobalTheory.thValTot_of_chartIndep GlobalTheory.firstFiveLaws.1 GlobalTheory.chartIndependence_unconditional E H Dw l Xo c nab hnab
  letI := io.toAlgebra
  obtain ⟨F, _, _, _, _, _, _, v, hv, hvx⟩ : ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F) (_ : CharZero F)
      (_ : Algebra T.Fr F) (_ : Algebra T.V F) (_ : IsScalarTower T.V T.Fr F) (v : AddValuation F (WithTop ℚ)),
      ValOver ϖ F v ∧ ∀ x : T.Fr, x ≠ 0 → v (algebraMap T.Fr F x) = (((vV T.V x : ℤ) : ℚ) : WithTop ℚ) := by
    obtain ⟨v, hv⟩ := GlobalTheory.ValClosure.exists_valuation_closure T.V ϖ hϖ
    exact ⟨AlgebraicClosure T.Fr, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, v, hv⟩
  obtain ⟨TI⟩ := GlobalTheory.T.nonempty_tateIsometry_integralFramedPoint_chart E H Dw l Xo c T io y C P F
  obtain ⟨D', A', G', _, _, pD, pA, pG, U', PU, _, oD', hx, hact, hθ⟩ :=
    (GlobalTheory.T.exists_productData_copies_trivialisation_valuation E H Dw l Xo c T io y C P ϖ hϖ).2 n
  obtain ⟨θ, θα, hθ1, hθ2, hθ3⟩ := hθ F v hv Q hQ α l.M (by have := l.three_le; omega) hα
  have hcop : ∃ u u' : 𝓞 E, u * α + u' * star α = 1 := by
    have h1 := l.coprime
    rw [hMb, Ideal.map_span, Set.image_singleton] at h1
    have h2 : (H.bar : 𝓞 E →+* 𝓞 E) (star α) = α := star_star α
    rw [h2, sup_comm, ← Ideal.span_insert, Ideal.eq_top_iff_one, Ideal.mem_span_pair] at h1
    exact h1
  have hdeg1 : P₁.totalDegree ≤ DF Dw a := by
    have key : ∀ m ∈ P₁.support, (m.sum fun _ e => e) = DF Dw a := by
      intro m hm
      rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma, DF]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun i _ => hP₁.1.2.2 m hm τ i
    exact Finset.sup_le fun m' hm' => (key m' hm').le
  unfold nuLocOf
  refine le_iInf_add_coe fun f => le_iInf_add_coe fun hf => ?_
  set Pp : MvPolynomial (LtN Dw n) T.Fr := MvPolynomial.map io P₁ with hPp
  set x0 := nabValN C.ch.B T.Fr C.ch.h H.w0 l.M f (fun ℓ : LtN Dw n => ℓ.2.2)
    (fun ℓ : LtN Dw n => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) Pp with hx0def
  by_cases hx0 : x0 = 0
  · rw [hx0, nval_zero, EReal.top_add_coe]; exact le_top
  have hmap : (∑ _i : Fin 1, algebraMap T.Fr F (algebraMap T.V T.Fr 1) •
      MvPolynomial.map ((algebraMap T.Fr F).comp io) P₁) = MvPolynomial.map (algebraMap T.Fr F) Pp := by
    rw [Fin.sum_univ_one, map_one, map_one, one_smul, hPp, MvPolynomial.map_map]
  have hdeg : (MvPolynomial.map (algebraMap T.Fr F) Pp).totalDegree ≤ DF Dw a :=
    (Finset.sup_mono (MvPolynomial.support_map_subset _ _)).trans
      ((Finset.sup_mono (MvPolynomial.support_map_subset _ _)).trans hdeg1)
  have hval := nabValN_algebraMap T.Fr F _ _ C.ch.B C.ch.h (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.cc_h C.ch.gauge) H.w0 l.M n f
    (LtN Dw n) (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ : LtN Dw n => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) Pp
  obtain ⟨i, p, w, ζ, x, t₀, t, σ', h, ρ, h1, h2, h3, h4', h5, h6, h7, h8, h9, hρ, hle⟩ :=
    GlobalTheory.T.pointStatements_on_copies_hold.1 E H Dw l Xo c T io y C hTr P hP hy ϖ hϖ Q hQ F v hv TI Φ M0 r b hΦ hb hb' n D' A' G' pD pA pG U' PU
      oD' hx hact hn α l.M (DF Dw a) hα hcop hu h4 hM0 θ θα hθ1 hθ2 hθ3 (Fin 1)
      (fun _ => MvPolynomial.map ((algebraMap T.Fr F).comp io) P₁)
      (fun _ => algebraMap T.Fr F (algebraMap T.V T.Fr 1)) (fun _ => val_algebraMap_nonneg T v hvx _)
      (by rw [hmap]; exact hdeg) f hf ((vV T.V x0 : ℤ) : ℚ)
      (by rw [hmap, Nat.one_mul, hval]; exact hvx x0 hx0)
  obtain ⟨xx, u, hu0, hrel⟩ := GlobalTheory.PtTie.harmonicValue_translate E H Dw l Xo c nab hnab T io y C hTr P hP hy ϖ hϖ Q hQ
    F v hv n D' A' G' pD pA pG U' PU oD' hx hact α l.M rfl hα hMb θ θα hθ2 hθ3 p w ζ x t₀ t (1 * l.M) rfl σ' h
    h1 h2 h3 h4' h6 h7 h8 h9 h5
  obtain ⟨g, hg, -⟩ := existsUnique_thRule Xo c nab hth xx hP₁
  have hgv := hrel a P₁ hP₁ g hg
  rw [hgv, map_mul (algebraMap T.Fr F), ← _root_.mul_assoc] at hρ
  have hint : ∀ τ : E →+* ℂ, ∃ z : T.V, algebraMap T.V T.Fr z = io (embK c τ α) := fun τ => by
    obtain ⟨φ, hφ⟩ := exists_lift_integers E T.V T.Fr (io.comp (embF c τ))
    exact ⟨φ α, hφ α⟩
  choose z hz using hint
  have hε' : 0 ≤ v (u * algebraMap T.Fr F (io (nrm Dw c a α))) := by
    rw [AddValuation.map_mul, hu0, zero_add]
    have := val_algebraMap_nonneg T v hvx (∏ τ : E →+* ℂ, z τ ^ (∑ i : Fin (Dw.mult τ), a (τ, i)))
    simpa only [nrm, map_prod, map_pow, hz] using this
  exact (iInf₂_le g ⟨xx, hg⟩).trans (nval_le_of_val T v hvx hx0 hε' hρ hle e)

end GlobalTheory.RefSum
