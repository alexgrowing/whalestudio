import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDatumSectionValueCoeffEqFourierJacobi
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqZeroOfSumSq
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArchBoundFlow
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LetterSquaredLengthLeFlowHeightStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmMetrisedLineLengthsEqSectionLieNormsStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NormalisedTrivialisationNormOneComplexReadingStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsTauCanonicalIffOfIsPullDegTauBimultStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.QuadraticCoefficientForms
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArchCM

theorem herm_sum_le {g m : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) (w : Fin m → (Fin g → ℂ)) {b : ℝ}
    (hw : ∀ k, (hermForm Hm (w k) (w k)).re ≤ b) :
    (hermForm Hm (∑ k, w k) (∑ k, w k)).re ≤ (m : ℝ) ^ 2 * b := by
  have h0 : ∀ z, 0 ≤ (hermForm Hm z z).re := fun z => by
    by_cases hz : z = 0
    · simp [hz, hermForm]
    · exact (hpos z hz).le
  have h1 : ∀ i j, (hermForm Hm (w i) (w j)).re + (hermForm Hm (w j) (w i)).re ≤ 2 * b := fun i j => by
    have := h0 (w i - w j)
    have e1 := hw i
    have e2 := hw j
    simp only [hermForm, star_sub, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, Complex.sub_re] at *
    linarith
  have h2 : (hermForm Hm (∑ k, w k) (∑ k, w k)).re = ∑ i, ∑ j, (hermForm Hm (w i) (w j)).re := by
    simp only [hermForm, star_sum, Matrix.mulVec_sum, sum_dotProduct, dotProduct_sum, Complex.re_sum]
    exact Finset.sum_comm
  have h3 : 2 * (hermForm Hm (∑ k, w k) (∑ k, w k)).re =
      ∑ i, ∑ j, ((hermForm Hm (w i) (w j)).re + (hermForm Hm (w j) (w i)).re) := by
    simp only [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => (hermForm Hm (w j) (w i)).re), ← h2]
    ring
  have h4 : ∑ i, ∑ j, ((hermForm Hm (w i) (w j)).re + (hermForm Hm (w j) (w i)).re) ≤
      ∑ _i : Fin m, ∑ _j : Fin m, 2 * b := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h4
  nlinarith

theorem herm_smul {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a : ℂ) (z : Fin g → ℂ) :
    (hermForm Hm (a • z) (a • z)).re = ‖a‖ ^ 2 * (hermForm Hm z z).re := by
  simp only [hermForm, smul_dotProduct, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul,
    Complex.star_def]
  rw [← _root_.mul_assoc, mul_comm _ a, Complex.mul_conj, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]

theorem herm_single {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (j : Fin g) :
    hermForm Hm (Pi.single j 1) (Pi.single j 1) = Hm j j := by
  simp [hermForm, ← Pi.single_star]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem le_of_invBl {f : (ArcLt Dw → ℂ) → ℝ} (hf : Continuous f) (ρ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℝ)
    (hρ : ∀ τ k, 0 < ρ τ k) {B : ℝ} (h : ∀ x, InvBl x → (∀ v, ‖x v‖ ≤ ρ v.1 v.2.2) → f x ≤ B)
    (x : ArcLt Dw → ℂ) (hx : ∀ v, ‖x v‖ ≤ ρ v.1 v.2.2) : f x ≤ B := by
  classical
  let y : ArcLt Dw → ℂ := fun v => Matrix.diagonal (fun k => (ρ v.1 k : ℂ)) v.2.1 v.2.2
  have hy : ∀ v, ‖y v‖ ≤ ρ v.1 v.2.2 := fun v => by
    simp only [y, Matrix.diagonal_apply]
    split_ifs with hv
    · rw [hv, Complex.norm_real, Real.norm_of_nonneg (hρ _ _).le]
    · simpa using (hρ _ _).le
  let Q : ∀ τ : E →+* ℂ, Polynomial ℂ := fun τ => (Matrix.of fun i k : Fin (Dw.mult τ) =>
    Polynomial.C (x ⟨τ, (i, k)⟩) + Polynomial.X * Polynomial.C (y ⟨τ, (i, k)⟩ - x ⟨τ, (i, k)⟩)).det
  have hQ : ∀ τ (t : ℂ), (Q τ).eval t = (Matrix.of fun i k : Fin (Dw.mult τ) =>
      x ⟨τ, (i, k)⟩ + t * (y ⟨τ, (i, k)⟩ - x ⟨τ, (i, k)⟩)).det := fun τ t => by
    rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i k
    simp [mul_comm]
  have hQ0 : ∀ τ, Q τ ≠ 0 := fun τ h0 => by
    have := hQ τ 1
    rw [h0, Polynomial.eval_zero] at this
    have e : (Matrix.of fun i k : Fin (Dw.mult τ) => x ⟨τ, (i, k)⟩ + 1 * (y ⟨τ, (i, k)⟩ - x ⟨τ, (i, k)⟩)) =
        Matrix.diagonal fun k => (ρ τ k : ℂ) := by
      ext i k
      simp [y]
    rw [e, Matrix.det_diagonal] at this
    exact Finset.prod_ne_zero_iff.2 (fun k _ => Complex.ofReal_ne_zero.2 (hρ τ k).ne') this.symm
  have hc : Continuous fun t : ℝ => f fun v => x v + (t : ℂ) * (y v - x v) := hf.comp (by fun_prop)
  have ht := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at ht
  refine le_of_tendsto ht ?_
  have e1 : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), ∀ τ, (Q τ).eval (t : ℂ) ≠ 0 := by
    refine Filter.eventually_all.2 fun τ => ?_
    have hfin : {t : ℝ | (Q τ).IsRoot (t : ℂ)}.Finite :=
      (Polynomial.finite_setOf_isRoot (hQ0 τ)).preimage Complex.ofReal_injective.injOn
    exact ((nhdsGT_le_nhdsNE 0).trans (nhdsNE_le_cofinite 0)) hfin.compl_mem_cofinite
  filter_upwards [e1, Ioo_mem_nhdsGT (zero_lt_one (α := ℝ))] with t h1 h2
  refine h _ (fun τ => ?_) fun v => ?_
  · rw [← hQ]; exact h1 τ
  · have e : x v + (t : ℂ) * (y v - x v) = ((1 - t : ℝ) : ℂ) * x v + (t : ℂ) * y v := by push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.2 h2.2.le),
      Real.norm_of_nonneg h2.1.le]
    nlinarith [hx v, hy v, h2.1, h2.2]

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem cfOf_le {K₁ : Type} [Field K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (em : K₁ →+* ℂ) (F : Rul Xo c)
    (ρ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℝ) (hρ : ∀ τ k, 0 < ρ τ k) {B : ℝ}
    (h : ∀ x, InvBl x → (∀ v, ‖x v‖ ≤ ρ v.1 v.2.2) → ‖ajAt d em F x‖ ≤ B) :
    ‖em (cfOf d.yF d.μ d.jj F)‖ * ∏ v : ArcLt Dw, ρ v.1 v.2.2 ^ d.μ v ≤ B := by
  classical
  set P := arcNum (evR Xo c F d.yF) with hP
  let G : MvPolynomial (ArcLt Dw) ℂ := ∑ m ∈ P.support, MvPolynomial.monomial m (em ((P.coeff m).coeff d.jj))
  have hG : ∀ x, MvPolynomial.eval x G = ajAt d em F x := fun x => by
    simp only [G, map_sum, MvPolynomial.eval_monomial, ajAt, Finsupp.prod, hP]
  have hc : G.coeff d.μ = em (cfOf d.yF d.μ d.jj F) := by
    simp only [G, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq', cfOf, ← hP]
    split_ifs with hm
    · rfl
    · rw [MvPolynomial.notMem_support_iff.1 hm]; simp
  rw [← hc]
  refine coeff_cauchy_bound _ G (fun v => ρ v.1 v.2.2) B d.μ (fun v => hρ _ _) fun z hz => ?_
  exact le_of_invBl (f := fun x => ‖MvPolynomial.eval x G‖) (MvPolynomial.continuous_eval G).norm ρ hρ
    (fun x h1 h2 => by rw [hG]; exact h x h1 h2) z hz

omit [IsCMField E] in
theorem one_le_rdE : 1 ≤ rdE E := by
  refine Real.one_le_rpow ?_ (by positivity)
  have := Int.one_le_abs (NumberField.discr_ne_zero E)
  unfold dE
  exact_mod_cast this

theorem two_mul_fdeg {r : ℕ} (X : Data E r) : 2 * fdeg E = Module.finrank ℚ E := by
  have h := IsoTime.trace_cm X 1
  have h2 : Algebra.trace ℚ E 1 = Module.finrank ℚ E := by
    simpa using Algebra.trace_algebraMap (R := ℚ) (S := E) (x := 1)
  rw [h2] at h
  simp only [map_one, Complex.one_re, Finset.sum_const, Finset.card_univ, QuadraticCoefficientForms.card_Psi, nsmul_eq_mul] at h
  have : ((2 * fdeg E : ℕ) : ℝ) = (Module.finrank ℚ E : ℕ) := by push_cast at h ⊢; linarith
  exact_mod_cast this

theorem sqrt_discr {r : ℕ} (X : Data E r) : Real.sqrt |((NumberField.discr E : ℤ) : ℝ)| = rdE E ^ fdeg E := by
  have h := two_mul_fdeg X
  have hp : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  rw [rdE, dE, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), Real.sqrt_eq_rpow]
  congr 1
  rw [← h] at hp ⊢
  push_cast at hp ⊢
  have : (fdeg E : ℝ) ≠ 0 := by intro h0; rw [h0] at hp; simp at hp
  field_simp

theorem const_le (r : ℕ) {La c₁ T C : ℝ} (hLa : 1 ≤ La) (hT : 0 < T) (hC : 0 < C) (hCT : C ≤ T ^ 2 * rdE E ^ fdeg E)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (h : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℝ) (h0 : ∀ τ i, 0 ≤ h τ i)
    (hh : ∀ τ i, h τ i ≤ (r * (La * Real.sqrt (max 1 c₁))) ^ 2) :
    (C * (max 1 c₁) ^ fdeg E) ^ ((n : ℝ) / 2) * ∏ τ : E →+* ℂ, ∏ i : Fin (Dw.mult τ), h τ i ^ ((a (τ, (i : ℕ)) : ℝ) / 2) ≤
      T ^ n * Real.exp (archP E r La c₁ * ((absA Dw a : ℝ) + (fdeg E : ℝ) * n)) := by
  have hM : 1 ≤ max 1 c₁ := le_max_left _ _
  have hrd := one_le_rdE (E := E)
  have l1 := Real.log_nonneg hM
  have l2 := Real.log_nonneg hLa
  have l3 := Real.log_nonneg hrd
  have l4 := Real.log_natCast_nonneg r
  set e := Real.exp (archP E r La c₁) with he
  have he0 : 0 < e := Real.exp_pos _
  have hsq : ∀ (u v : ℝ) (k : ℕ), 0 ≤ u → 0 ≤ v → u ≤ v ^ 2 → u ^ ((k : ℝ) / 2) ≤ v ^ k := fun u v k hu hv huv => by
    refine (Real.rpow_le_rpow hu huv (by positivity)).trans (le_of_eq ?_)
    rw [← Real.rpow_natCast v 2, ← Real.rpow_mul hv, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have e1 : r * (La * Real.sqrt (max 1 c₁)) ≤ e := by
    have a1 : Real.sqrt (max 1 c₁) = Real.exp (Real.log (max 1 c₁) / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by linarith)]
      congr 1; ring
    calc r * (La * Real.sqrt (max 1 c₁))
        ≤ Real.exp (Real.log r) * (Real.exp (Real.log La) * Real.exp (Real.log (max 1 c₁) / 2)) := by
          rw [a1]
          gcongr <;> exact Real.le_exp_log _
      _ ≤ e := by
          rw [← Real.exp_add, ← Real.exp_add, he, archP]
          exact Real.exp_le_exp.2 (by linarith)
  have e2 : rdE E * max 1 c₁ ≤ e ^ 2 := by
    calc rdE E * max 1 c₁ ≤ Real.exp (Real.log (rdE E)) * Real.exp (Real.log (max 1 c₁)) := by
          gcongr <;> exact Real.le_exp_log _
      _ ≤ e ^ 2 := by
          rw [← Real.exp_add, he, ← Real.exp_nat_mul, archP]
          exact Real.exp_le_exp.2 (by push_cast; linarith)
  have b1 : (C * (max 1 c₁) ^ fdeg E) ^ ((n : ℝ) / 2) ≤ (T * e ^ fdeg E) ^ n := by
    refine hsq _ _ _ (by positivity) (by positivity) ?_
    calc C * (max 1 c₁) ^ fdeg E ≤ T ^ 2 * rdE E ^ fdeg E * (max 1 c₁) ^ fdeg E := by gcongr
      _ = T ^ 2 * (rdE E * max 1 c₁) ^ fdeg E := by rw [mul_pow, _root_.mul_assoc]
      _ ≤ T ^ 2 * (e ^ 2) ^ fdeg E := by gcongr
      _ = _ := by ring
  have b2 : ∏ τ : E →+* ℂ, ∏ i : Fin (Dw.mult τ), h τ i ^ ((a (τ, (i : ℕ)) : ℝ) / 2) ≤ e ^ absA Dw a := by
    rw [absA, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod (fun τ _ => Finset.prod_nonneg fun i _ => Real.rpow_nonneg (h0 τ i) _) fun τ _ => ?_
    rw [← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod (fun i _ => Real.rpow_nonneg (h0 τ i) _) fun i _ => ?_
    exact hsq _ _ _ (h0 τ i) he0.le ((hh τ i).trans (by gcongr))
  refine (mul_le_mul b1 b2 (Finset.prod_nonneg fun τ _ => Finset.prod_nonneg fun i _ =>
    Real.rpow_nonneg (h0 τ i) _) (by positivity)).trans (le_of_eq ?_)
  have : archP E r La c₁ * ((absA Dw a : ℝ) + (fdeg E : ℝ) * n) =
      ((absA Dw a + fdeg E * n : ℕ) : ℝ) * archP E r La c₁ := by push_cast; ring
  rw [this, Real.exp_nat_mul, ← he]
  ring

theorem num_le {A u K e e' J S Lf N B : ℝ} (hid : A * u = K * (e * u * J)) (hu : u ≠ 0) (hJ : J ≤ S / Lf / N)
    (hK : K / (Lf * N) ≤ B) (he : e ≤ e') (he0 : 0 ≤ e) (hK0 : 0 ≤ K) (hJ0 : 0 ≤ J) (hS : 0 ≤ S) : A ≤ S * e' * B := by
  have h1 : A = K * (e * J) := mul_right_cancel₀ hu (by rw [hid]; ring)
  have he' := he0.trans he
  calc A = K * (e * J) := h1
    _ ≤ K * (e' * (S / Lf / N)) := by gcongr
    _ = S * e' * (K / (Lf * N)) := by rw [div_div]; ring
    _ ≤ _ := by gcongr

theorem line_pos {K₁ : Type} [Field K₁] [NumberField K₁] [Algebra c.F K₁]
    {a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)}
    {e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)} {th : a.D₀.P.L.Sec} {jj : ℤ} {n' : ℕ} {La c₁ : ℝ}
    (s : CMIn a e th jj n' La c₁) (em : K₁ →+* ℂ) :
    0 < s.Tl.n em ∧ ∀ τ k, 0 < (s.line τ k).n em := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h1, h2, h3, -⟩ := s.good
  refine ⟨h3.2 em, fun τ k => ?_⟩
  unfold CMIn.line
  cases s.kind τ k with
  | none => exact zero_lt_one
  | some m =>
    have h := s.L_good.2.2.2 m
    simp only [Option.elim]
    split at h
    · rw [h]; exact (h1 _).1.2 em
    · rw [h]; exact (h2 _).1.2 em

theorem norm_cfOf_le : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (s : CMIn d.a d.e d.th d.jj n' La c₁) (em : K₁ →+* ℂ) (r : ℕ) (U : Unf Xo c (em.comp (algebraMap c.F K₁)) r) (xi S : ℝ) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Std d → 1 ≤ La → GoodEmb c (em.comp (algebraMap c.F K₁)) → IsUnf U → (∀ k (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = xi) → Dom a' n → (∀ k, TransvIn (U.X k) l.M' (laU U a' n k)) → ∀ F ∈ sec Xo c a' n, 0 ≤ S → (∀ k, ∀ y ∈ (U.X k).dom, lieFac Dw xi a' * (U.X k).pnorm (laU U a' n k) (rdU U F k) y ≤ S) → ‖em (cfOf d.yF d.μ d.jj F)‖ * (s.valLine d.μ n).n em ≤ S * Real.exp (4 * Real.pi + GlobalTheory.ArcCM.archP E r La c₁ * ((absA Dw a' : ℝ) + (fdeg E : ℝ) * n)) := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ d n' La c₁ s em r U xi S a' n ⟨hover, ⟨y₀, hy₀, hc⟩, hpush⟩ hLa hgood hunf
    hxi hdom htv F hF hS0 hS
  have h1 := hK.laws
  have h2 := hK.laws2
  have hev := hK.ev E H Dw l Xo c
  letI : Algebra (FractionRing ℂ) ℂ := FractionRing.liftAlgebra ℂ ℂ
  haveI : IsScalarTower ℂ (FractionRing ℂ) ℂ := FractionRing.isScalarTower_liftAlgebra ℂ ℂ
  letI : Algebra c.F ℂ⸨X⸩ := (ArcId.cstL.comp (em.comp (algebraMap c.F K₁))).toAlgebra
  obtain ⟨Uw⟩ := GlobalTheory.T.nonempty_unifWitnessData_of_isUnf E H Dw l Xo c _ r U hunf
  have hth : ThNZ d.th := s.th_nz
  obtain ⟨⟨a₁, p, hp⟩, hbc⟩ := GlobalTheory.ArcQBC.baseChanges h1 h2 hK.ubc hK.laws5 E H Dw l Xo c _ _ d.Y K₁ ℂ _
    (d.a.restrict (c.V d.Wp).subtype) em em.injective ((em.comp (algebraMap c.F K₁)).comp (c.V d.Wp).subtype) rfl
  obtain ⟨hW, hlet, htan, hthx, hnz⟩ := hbc a₁ p hp
  obtain ⟨W₁, hW₁⟩ := hW d.χ d.W
  choose e₁ he₁ using fun τ k => (hlet (d.e τ k)).exists
  obtain ⟨th₁, hth₁⟩ := (hthx d.th).exists
  have hover₁ : (spMap (PowerSeries.map em) ≫ d.χ) ≫ d.Y.s = spMap (PowerSeries.C (R := ℂ)) ≫
      spMap ((em.comp (algebraMap c.F K₁)).comp (c.V d.Wp).subtype) := by
    rw [Category.assoc, hover, ArcId.sp_comp, ArcId.sp_comp, ArcId.sp_comp]
    congr 1
    exact RingHom.ext fun x => PowerSeries.map_C _ _
  obtain ⟨Ha⟩ := hK.n5 E H Dw l Xo c _ _ d.Y (em.comp (algebraMap c.F K₁)) a₁ _ W₁ Uw.g _ Uw.F hgood
    ((GlobalTheory.Relab.relab_good E H l c _ hgood).2.2.2 Dw Uw.g Uw.e) (GlobalTheory.ArcInTest.exists_values c d.Wp) hover₁
    (ArcId.generic_mem d em)
  let f : a₁.D₀.X ≃ₗ[𝓞 E] d.a.D₀.X := { p.xe with map_smul' := hp.2.1 }
  have hrk := f.finrank_eq.trans s.rk
  have hξ : s.ξ.comp (f.toLinearMap.restrictScalars ℤ) ≠ 0 := fun h => s.ξ_ne (LinearMap.ext fun y => by
    obtain ⟨y, rfl⟩ := f.surjective y
    exact LinearMap.congr_fun h y)
  have hβ := ArcId.betaAt_comp f s.ξ hp.2.2.1 s.beta
  have hw : Ha.T < (((Ha.T + 1 : ℝ) : ℂ) * Complex.I).im := by simp
  generalize ((Ha.T + 1 : ℝ) : ℂ) * Complex.I = w at hw
  obtain ⟨k, ξ', sE, C, hiso, hsE, -, -, hC, hCle, hmain⟩ := GlobalTheory.T.laurentCoeff_sectionValue_arc_eq_fourierJacobi h1 h2 E H Dw l Xo c _ r U Uw _ _ d.Y a₁ _ W₁
    Ha th₁ _ s.ν₀ d.jj a' n hev hgood hunf (fun _ => rfl) hover₁ (mono_spMap_subtype _) hpush (hnz _ _ hth₁ hth) hrk hξ hβ
    hdom htv w hw
  obtain ⟨v₁, v₂, -, v₄⟩ := GlobalTheory.T.torusExt_exponential_derivative_bijective_tangent h1.globalFns E H Dw l Xo c _ _ _ d.Y a₁ _ W₁ _ _ Uw.F Ha
  choose z₁ hz₁ using fun τ i => (v₁ (e₁ τ i) (htan _ _ (he₁ τ i) (s.tan τ i))).exists
  have hN : NormOne Ha := GlobalTheory.T.normalisedTrivialisation_normOne_complexReading hK E H Dw l Xo c _ _ _ d.Y a₁ _ W₁ _ _ Uw.F Ha n' s.n_pos
    ((GlobalTheory.T.isTauCanonical_iff_of_isPullDeg_tauBimult hK K₁ ℂ em _ _ p n' em.injective d.a.bimult a₁.bimult).1 s.tau)
  have hCT := hCle _ (((GlobalTheory.T.cm_metrised_line_lengths_eq_section_lie_norms hK E H Dw l c K₁ d.a d.e d.th d.jj n' La c₁ s em).2.2.2 _ p).1 th₁ hth₁)
  rw [sqrt_discr (U.X k)] at hCT
  obtain ⟨hT, hl⟩ := line_pos s em
  have hL := lieFac_pos Dw xi a'
  have hM : 0 < max 1 c₁ := lt_max_of_lt_left zero_lt_one
  have hep : 0 < (max 1 c₁)⁻¹ := inv_pos.2 hM
  have hS' : ∀ y ∈ (U.X k).dom, (U.X k).pnorm (laU U a' n k) (rdU U F k) y ≤ S / lieFac Dw xi a' := fun y hy =>
    (le_div_iff₀' hL).2 (hS k y hy)
  have hb : (U.X k).IsBddSec (laU U a' n k) (rdU U F k) := ⟨hunf.2.2.2.2.1 a' n hdom F hF k, _, hS'⟩
  have htr : (max 1 c₁)⁻¹ * ∑ τ : (U.X k).Ψ, (τ.1 s.ν₀).re ≤ 1 := by
    have e1 := IsoTime.trace_cm (U.X k) s.ν₀
    have e2 := s.tr
    rw [← Finset.mul_sum] at e1
    rw [inv_mul_le_iff₀ hM]
    have := le_max_right 1 c₁
    linarith
  have hjj : 2 * ∑ τ : (U.X k).Ψ, (τ.1 s.ν₀).re * (τ.1 sE).re = d.jj := by
    rw [ArcCoeff.two_sum_eq_trace (U.X k) hβ.1 hsE.1, (hβ.2 sE hsE).1, Rat.cast_intCast]
  have key := cfOf_le d em F (fun τ i => ((s.line τ i).n em)⁻¹) (fun τ i => inv_pos.2 (hl τ i))
    (B := S * Real.exp (4 * Real.pi) * (s.Tl.n em ^ n *
      Real.exp (archP E r La c₁ * ((absA Dw a' : ℝ) + (fdeg E : ℝ) * n)))) fun x hx hxρ => by
    choose e₂ he₂ using fun (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) => (v₂ (∑ j, x ⟨τ, (i, j)⟩ • z₁ τ j)).exists
    obtain ⟨-, y, hy, hval⟩ := ArcId.exists_frPt_at h1 h2 hev d em (fun _ => rfl) hy₀ hc hth hp hW₁ he₁ hth₁
      (hnz _ _ hth₁ hth) hx (fun τ i => (v₄ _ _ _ _ _ (hz₁ τ)).2 (he₂ τ i)) a' n
    obtain ⟨fr, κ, L, gm, hLgm, hEgm, hLz, ht, hκ, hFj⟩ := hmain e₂ _ y hy he₂
    have htt := IsoTime.tt_eq_im_mul E H Dw l Xo c _ r U Uw _ _ d.Y a₁ _ W₁ Ha k _ ξ' sE w fr L gm hgood hunf hN hw hrk hξ
      hsE hLgm hEgm ht
    obtain ⟨hx'', htep, hfl, hbd⟩ := arch_bound_flow E H Dw l Xo c _ r U Uw k ξ' fr C _ xi κ a' n hgood hunf hiso hC hep
      hdom.2 (hxi k) hκ
    obtain ⟨-, -, -, -, Hm, hH⟩ := Uw.period k ⟨_, hx''⟩
    have hH' : IsRiem Uw.F (Uw.ik k) (Uw.Pm k ⟨_, hx''⟩) Hm := hH
    have hlen := fun τ i => GlobalTheory.T.letter_squaredLength_le_flow_height hK E H Dw l Xo c K₁ d.a d.e d.th d.jj n' La c₁ s em _ r U Uw _ _ d.Y a₁ p _ W₁
      Ha k ξ' fr ⟨_, hx''⟩ _ w L gm _ Hm rfl hgood hunf hp hLa hep hiso hw hLgm hEgm ht rfl htep hH' τ i _ _ (he₁ τ i)
      (hz₁ τ i)
    rw [inv_inv, max_eq_right (le_max_left 1 c₁)] at hlen
    have hdiag : ∀ τ (i : Fin (Dw.mult τ)), Real.pi * (Hm (Uw.e.symm ⟨τ, i⟩) (Uw.e.symm ⟨τ, i⟩)).re ≤
        (r * (La * Real.sqrt (max 1 c₁))) ^ 2 := fun τ i => by
      have hm : (Dw.mult τ : ℝ) ≤ r := by
        have : Dw.mult τ ≤ r := by
          rw [hunf.1]
          unfold Datum.mult
          split_ifs <;> omega
        exact_mod_cast this
      rw [← herm_single Hm, ← hLz, map_sum]
      have := herm_sum_le hH'.2.1 (fun j => L (x ⟨τ, (i, j)⟩ • z₁ τ j))
        (b := (La * Real.sqrt (max 1 c₁)) ^ 2 / Real.pi) fun j => by
          rw [le_div_iff₀' Real.pi_pos, map_smul, herm_smul, mul_left_comm]
          have e1 : ‖x ⟨τ, (i, j)⟩‖ ≤ ((s.line τ j).n em)⁻¹ := hxρ ⟨τ, (i, j)⟩
          have e2 := (hl τ j).ne'
          calc _ ≤ ‖x ⟨τ, (i, j)⟩‖ ^ 2 * (La * Real.sqrt (max 1 c₁) * (s.line τ j).n em) ^ 2 :=
                mul_le_mul_of_nonneg_left (hlen τ j) (by positivity)
            _ ≤ (((s.line τ j).n em)⁻¹) ^ 2 * (La * Real.sqrt (max 1 c₁) * (s.line τ j).n em) ^ 2 := by gcongr
            _ = _ := by field_simp
      rw [← mul_div_assoc, le_div_iff₀' Real.pi_pos] at this
      refine this.trans ?_
      rw [mul_pow (r : ℝ)]
      gcongr
    have hκb := hbd Hm hH'
    rw [inv_inv, ← Fintype.card_coe, QuadraticCoefficientForms.card_Psi] at hκb
    replace hκb := hκb.trans (const_le r hLa hT hC hCT a' n _ (fun τ i => mul_nonneg Real.pi_pos.le (by
      rw [← herm_single Hm]
      exact (hH'.2.1 _ (by simp)).le)) hdiag)
    have hcau := FlowCoefficientBounds.fj_bound (U.X k) _ _ _ hS' hiso (fun τ => (τ.1 s.ν₀).re) hx''
    have hnf := FlowCoefficientBounds.nfac_pos (U.X k) hx'' (laU U a' n k)
    have hid := congrArg norm (hFj F hF hb)
    rw [norm_mul, norm_mul, hfl _ _ hb] at hid
    have hexp : Real.exp (4 * Real.pi * ∑ τ : (U.X k).Ψ, (τ.1 s.ν₀).re * ((max 1 c₁)⁻¹ - (U.X k).tt ξ' fr.1 τ)) =
        Real.exp (4 * Real.pi * ((max 1 c₁)⁻¹ * ∑ τ : (U.X k).Ψ, (τ.1 s.ν₀).re)) * ‖eTwoPi w ^ d.jj‖ := by
      rw [norm_zpow, eTwoPi, Complex.norm_exp, ← Real.rpow_intCast, ← Real.exp_mul, ← Real.exp_add, ← hjj]
      congr 1
      simp only [htt, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Complex.mul_re, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, ← Finset.sum_add_distrib,
        ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun τ _ => by ring
    have hne : ‖eTwoPi w ^ d.jj‖ ≠ 0 := norm_ne_zero_iff.2 (zpow_ne_zero _ (Complex.exp_ne_zero _))
    have hE : Real.exp (4 * Real.pi * ((max 1 c₁)⁻¹ * ∑ τ : (U.X k).Ψ, (τ.1 s.ν₀).re)) ≤ Real.exp (4 * Real.pi) :=
      Real.exp_le_exp.2 (mul_le_of_le_one_right (by positivity) htr)
    rw [hval F hF, map_one, one_pow, _root_.one_mul]
    rw [hexp] at hid
    exact num_le hid hne ((le_div_iff₀ hnf).2 hcau) hκb hE (Real.exp_pos _).le (norm_nonneg _) (norm_nonneg _) hS0
  refine le_of_eq_of_le ?_ ((div_le_div_of_nonneg_right key (pow_pos hT n).le).trans (le_of_eq ?_))
  · simp only [CMIn.valLine, MLine.tensor, MLine.dual, MLine.pow, MLine.prodPow, inv_pow, Finset.prod_inv_distrib]
    ring
  · rw [Real.exp_add]
    field_simp

end GlobalTheory.ArchCM
