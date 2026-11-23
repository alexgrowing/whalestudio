import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetsOnCopiesAny
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicValueIntegralGermFramePowerCharZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicValueTranslateDivisorLevelIntegralChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhiAt
import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaExponentsDominantLastEntryOneDegree
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaRulesExistAndCusp
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIsNabUncond
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionUniformisedChartScale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionDvrFlagLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IInfThRuleLeNuLocOf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueTranslateAny
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueTranslateEqUnitMulNormaliserThetaVa
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PointStatementsOnCopiesHoldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortPeriodLatticeBasisBalancedSlope
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsProductDataCopiesTrivialisationValuation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLocusExponentLeOscillationNonTypePrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightAntitoneBoundary
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.PowGerm GlobalTheory.PtTie GlobalTheory.RefSum
open GlobalTheory.ThetaLeast

namespace GlobalTheory.JetsLevelZero

theorem iInf_thRule_le_nuLocOf_charZero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (IsLocalRing.maximalIdeal T.V) C.I.G), P.TorsionIso → CharZero (IsLocalRing.ResidueField T.V) → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (r : ℕ) (Φ M0 : ℝ), GlobalTheory.PtTie.ShortBasis Q r Φ M0 → ∀ (α : 𝓞 E) (q : ℕ), α * star α = ((q : ℕ) : 𝓞 E) → q ∣ l.M → l.Mb ≤ Ideal.span {star α} → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n e : ℕ), 1 ≤ n → 0 < e → 4 * DF Dw a + 4 ≤ q → (DF Dw a : ℝ) * M0 < q → ∀ P₁ ∈ harmA (Dw := Dw) c a n, (⨅ (f : Rul Xo c) (_ : ∃ x : Fin n → Dw.La, IsThRule Xo c nab x P₁ f), nval T.V e (evI y f)) ≤ GlobalTheory.FactorDepth.nuLocOf C e l.M (MvPolynomial.map io P₁) + (((DF Dw a : ℝ) ^ 2 * Φ / q / e : ℝ) : EReal) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro nab hnab T io y C hTr P hP hchar ϖ hϖ Q hQ r Φ M0 hSB α q hα hqM hMb a n e hn he h4 hM0 P₁ hP₁
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
  have hq0 : 0 < q := by omega
  obtain ⟨θ, θα, hθ1, hθ2, hθ3⟩ := hθ F v hv Q hQ α q hq0 hα
  have hcop : ∃ u u' : 𝓞 E, u * α + u' * star α = 1 := by
    have h1 := l.coprime
    have h2 : l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ Ideal.span {α} := by
      refine (Ideal.map_mono hMb).trans ?_
      rw [Ideal.map_span, Set.image_singleton]
      have h3 : (H.bar : 𝓞 E →+* 𝓞 E) (star α) = α := star_star α
      rw [h3]
    have h4' : Ideal.span {star α} ⊔ Ideal.span {α} = ⊤ := top_le_iff.1 (h1 ▸ sup_le_sup hMb h2)
    rw [sup_comm, ← Ideal.span_insert, Ideal.eq_top_iff_one, Ideal.mem_span_pair] at h4'
    exact h4'
  have hu : IsUnit ((q : ℕ) : T.V) := by
    refine (IsLocalRing.residue_ne_zero_iff_isUnit _).1 ?_
    rw [map_natCast]
    exact Nat.cast_ne_zero.2 hq0.ne'
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
  obtain ⟨f', hf', hff'⟩ := GlobalTheory.T.harmonic_value_integral_germ_frame_power_charZero E H Dw l Xo c T io y C hchar a n l.M q P₁ hP₁ f hf
  set Pp : MvPolynomial (LtN Dw n) T.Fr := MvPolynomial.map io P₁ with hPp
  set x0 := nabValN C.ch.B T.Fr C.ch.h H.w0 l.M f (fun ℓ : LtN Dw n => ℓ.2.2)
    (fun ℓ : LtN Dw n => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) Pp with hx0def
  by_cases hx0 : x0 = 0
  · rw [hx0, nval_zero, EReal.top_add_coe]; exact le_top
  have hx0' : x0 = nabValN C.ch.B T.Fr C.ch.h H.w0 q f' (fun ℓ : LtN Dw n => ℓ.2.2)
      (fun ℓ : LtN Dw n => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) Pp := hff'
  have hmap : (∑ _i : Fin 1, algebraMap T.Fr F (algebraMap T.V T.Fr 1) •
      MvPolynomial.map ((algebraMap T.Fr F).comp io) P₁) = MvPolynomial.map (algebraMap T.Fr F) Pp := by
    rw [Fin.sum_univ_one, map_one, map_one, one_smul, hPp, MvPolynomial.map_map]
  have hdeg : (MvPolynomial.map (algebraMap T.Fr F) Pp).totalDegree ≤ DF Dw a :=
    (Finset.sup_mono (MvPolynomial.support_map_subset _ _)).trans
      ((Finset.sup_mono (MvPolynomial.support_map_subset _ _)).trans hdeg1)
  have hval := nabValN_algebraMap T.Fr F _ _ C.ch.B C.ch.h (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.cc_h C.ch.gauge) H.w0 q n f'
    (LtN Dw n) (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ : LtN Dw n => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) Pp
  obtain ⟨i, p, w, ζ, x, t₀, t, σ', h, ρ, h1, h2, h3, h4', h5, h6, h7, h8, h9, hρ, hle⟩ :=
    GlobalTheory.JetsLevelZero.rPoint_any E H Dw l Xo c T io y C hTr P hP ϖ hϖ Q hQ F v hv TI Φ M0 r b hΦ hb hb' n D' A' G' pD pA pG U' PU
      oD' hx hact hn α q (DF Dw a) hα hcop hu h4 hM0 θ θα hθ1 hθ2 hθ3 (Fin 1)
      (fun _ => MvPolynomial.map ((algebraMap T.Fr F).comp io) P₁)
      (fun _ => algebraMap T.Fr F (algebraMap T.V T.Fr 1)) (fun _ => val_algebraMap_nonneg T v hvx _)
      (by rw [hmap]; exact hdeg) f' hf' ((vV T.V x0 : ℤ) : ℚ)
      (by rw [hmap, Nat.one_mul, hval, ← hx0']; exact hvx x0 hx0)
  obtain ⟨xx, u, hu0, hrel⟩ := GlobalTheory.T.harmonicValue_translate_divisor_level_integral_chart E H Dw l Xo c nab hnab T io y C hTr P hP hchar ϖ hϖ Q hQ
    F v hv n D' A' G' pD pA pG U' PU oD' hx hact α q hqM hα hMb θ θα hθ2 hθ3 p w ζ x t₀ t σ' h
    h1 h2 h3 h4' h6 h7 h8 h9 h5 a P₁ hP₁
  obtain ⟨g, hg, -⟩ := existsUnique_thRule Xo c nab hth xx hP₁
  have hgv := hrel g hg
  rw [hgv] at hρ
  have hε' : 0 ≤ v u := hu0
  exact (iInf₂_le g ⟨xx, hg⟩).trans (nval_le_of_val T v hvx hx0 hε' hρ hle e)

end GlobalTheory.JetsLevelZero
