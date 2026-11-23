import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapRAevalIsHomogeneousFiveVars
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcMeasUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensDetWeightEqNegLeviLog
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConstantOneMemNonvanishing

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CovTest.SwapLine
open GlobalTheory.LineForm

namespace GlobalTheory.LineFormModel

theorem pm_one : pm 1 = C (1 / 6) * X 0 ^ 2 + C (1 / 3) * X 1 := by
  apply MvPolynomial.funext; intro x
  simp [pm, Finset.sum_range_succ, Nat.factorial]; ring

theorem pm_two : pm 2 = C (1 / 30) * X 0 ^ 4 + C (1 / 15) * X 0 ^ 2 * X 1 + C (1 / 5) * X 1 ^ 2 := by
  apply MvPolynomial.funext; intro x
  simp [pm, Finset.sum_range_succ, Nat.factorial, Nat.choose]; ring

theorem pm_three : pm 3 = C (1 / 140) * X 0 ^ 6 + C (1 / 70) * X 0 ^ 4 * X 1 + C (3 / 70) * X 0 ^ 2 * X 1 ^ 2 +
    C (1 / 7) * X 1 ^ 3 := by
  apply MvPolynomial.funext; intro x
  simp [pm, Finset.sum_range_succ, Nat.factorial, Nat.choose]; ring

theorem hs_small (a b : ℝ) : aeval ![a + b, a * b] (hs 0) = 1 ∧ aeval ![a + b, a * b] (hs 1) = a + b ∧
    aeval ![a + b, a * b] (hs 3) = a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3 ∧
    aeval ![a + b, a * b] (hs 4) = a ^ 4 + a ^ 3 * b + a ^ 2 * b ^ 2 + a * b ^ 3 + b ^ 4 ∧
    aeval ![a + b, a * b] (hs 5) = a ^ 5 + a ^ 4 * b + a ^ 3 * b ^ 2 + a ^ 2 * b ^ 3 + a * b ^ 4 + b ^ 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [hs, Finset.sum_range_succ, Nat.choose] <;> ring

theorem sum_idx {S : Type} [AddCommMonoid S] (d : ℕ) (f : ℕ × ℕ → S) :
    ∑ x ∈ idx d, f x = ∑ i ∈ Finset.range (d + 3), ∑ j ∈ Finset.range i, f (i, j) := by
  rw [idx, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
  omega

theorem polynomialOfCoeffs_eq_swapPolynomial (d : ℕ) (a b : ℤ) : upperParabolic (idx d) expo (coefW (swapR d a b)) = swapP d a b := by
  rw [upperParabolic, sum_idx, swapP]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : (aeval ![X 2, X 3, X 4] (aeval ![X 1 + X 2, X 0] (swapR d a b i) : MvPolynomial (Fin 3) ℝ) :
      MvPolynomial (Fin 5) ℝ) = aeval ![X 3 + X 4, X 2] (swapR d a b i) := by
    rw [← AlgHom.comp_apply, comp_aeval]
    congr 2
    funext l; fin_cases l <;> simp
  simp only [coefW, expo, map_mul, map_pow, e, aeval_X]
  simp
  ring

theorem beta (j : ℕ) : ∫ t in (0 : ℝ)..1, (t * (1 - t)) ^ j = (j.factorial * j.factorial : ℝ) / (2 * j + 1).factorial := by
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := j + 1) (t := j + 1) (by simp; positivity) (by simp; positivity)
  rw [show (j + 1 + (j + 1) : ℂ) = ((2 * j + 1 : ℕ) : ℂ) + 1 by push_cast; ring, Complex.Gamma_nat_eq_factorial,
    Complex.Gamma_nat_eq_factorial, Complex.betaIntegral] at h
  simp only [add_sub_cancel_right, Complex.cpow_natCast] at h
  have h2 : ((∫ t in (0 : ℝ)..1, (t * (1 - t)) ^ j : ℝ) : ℂ) = ∫ x : ℝ in (0 : ℝ)..1, (x : ℂ) ^ j * (1 - x) ^ j := by
    rw [← intervalIntegral.integral_ofReal]
    simp [mul_pow]
  rw [← h2] at h
  rw [eq_div_iff (by positivity), mul_comm]
  exact_mod_cast h.symm

theorem aeval_pm (m : ℕ) (a b : ℝ) :
    aeval ![a + b, a * b] (pm m) = ∫ t in (0 : ℝ)..1, ((a * t + b * (1 - t)) * (a * (1 - t) + b * t)) ^ m := by
  have hI : ∀ t : ℝ, ((a * t + b * (1 - t)) * (a * (1 - t) + b * t)) ^ m = ∑ j ∈ Finset.range (m + 1),
      (m.choose j : ℝ) * (a * b) ^ (m - j) * ((a + b) ^ 2 - 4 * (a * b)) ^ j * (t * (1 - t)) ^ j := by
    intro t
    rw [show (a * t + b * (1 - t)) * (a * (1 - t) + b * t) =
      t * (1 - t) * ((a + b) ^ 2 - 4 * (a * b)) + a * b by ring, add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow]
    ring
  simp_rw [hI]
  rw [intervalIntegral.integral_finsetSum fun j _ => by apply Continuous.intervalIntegrable; fun_prop]
  simp only [pm, map_sum, map_mul, map_pow, map_sub, map_ofNat, aeval_C, aeval_X, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Algebra.algebraMap_self, RingHom.id_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_const_mul, beta]
  ring

theorem pm_eq_fibPoly_val (m : ℕ) (a b : ℝ) : aeval ![a + b, a * b] (pm m) = aeval ![a + b, a * b] (fibPoly m) :=
  (aeval_pm m a b).trans (aeval_fibPoly m a b).symm

theorem downP_eq_baseT (d : ℕ) (R : ℕ → MvPolynomial (Fin 2) ℝ) (A a b : ℝ) :
    aeval ![A, a, b, a * b] (downP (idx d) expo (coefW R)) = aeval ![a + b, a * b, A] (baseT d R) := by
  simp only [downP, baseT, coefW, map_sum, map_mul, map_pow]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [← AlgHom.comp_apply, comp_aeval]
  have e₁ : (fun i => (aeval ![A, a, b, a * b]) ((![X 1 + X 2, X 3] : Fin 2 → MvPolynomial (Fin 4) ℝ) i)) = ![a + b, a * b] := by
    funext i; fin_cases i <;> simp
  have e₂ : (fun i => (aeval ![a + b, a * b, A]) ((![X 0, X 1] : Fin 2 → MvPolynomial (Fin 3) ℝ) i)) = ![a + b, a * b] := by
    funext i; fin_cases i <;> simp
  have e₃ : (fun i => (aeval ![a + b, a * b, A]) ((![X 0, X 2] : Fin 2 → MvPolynomial (Fin 3) ℝ) i)) = ![a + b, A] := by
    funext i; fin_cases i <;> simp
  have e₄ : (fun i => (aeval ![A, a, b, a * b]) ((![X 0, X 1, X 2] : Fin 3 → MvPolynomial (Fin 4) ℝ) i)) = ![A, a, b] := by
    funext i; fin_cases i <;> simp
  have e₅ : (fun i => (aeval ![A, a, b]) ((![X 1 + X 2, X 0] : Fin 2 → MvPolynomial (Fin 3) ℝ) i)) = ![a + b, A] := by
    funext i; fin_cases i <;> simp
  simp only [e₁, e₂, e₃, e₄, e₅]
  simp
  ring

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (h : IsRegVar p D) (σ : k →+* ℂ)

theorem omF_eq {E : X.Modules} {m : VMetric p E 2} (H : m.IsCInf) (fl : Vert.Flag E 2) (x : (h.atlas σ).Pt)
    (a : VBExt.AdaptedChart (lineSC fl) 1 1) (ha : x.pt ∈ ptsIn p σ a.U) :
    omF h σ m fl x = ofValues (extTrace (fun v => (m.met σ).gram a.frame (x.ch.symm v)) x.crd) :=
  congrArg ofValues (Met.bcForm_eq (S := lineSC fl) (r := 1) (s := 1) (h := m.met σ) (lineSC_shortExact fl) a
    (frameAt fl x.pt) x.1.1 (H σ) x.2 ha (mem_frameAt fl x.pt))

theorem dens_ofValues (α : ReciprocityTheory.L2DbarEstimates.V 1 → ReciprocityTheory.L2DbarEstimates.V 1 → ℂ) :
    (dens ((ofValues α : Ev 1) : Alt 1)).re = 2 * diagVal α (EuclideanSpace.single 0 1) := by
  have e : (ofValues α : Ev 1) = (2 * (-Complex.I * α (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1))) • vol 1 := by
    simp only [ofValues, vol, Fin.sum_univ_one, Fin.prod_univ_one, smul_smul]
    congr 1
    linear_combination (α (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1)) * Complex.I_mul_I
  have e' (c : ℂ) : dens ((c • vol 1 : Ev 1) : Alt 1) = c * dens (vol 1 : Alt 1) := by
    simp [dens, mul_div_assoc]
  rw [e, e', dens_vol, mul_one, diagVal]
  simp

theorem glue_congr {M ι : Type} [TopologicalSpace M] [MeasurableSpace M] {n : ℕ}
    (e : ι → OpenPartialHomeomorph M (ReciprocityTheory.L2DbarEstimates.V n)) {ρ ρ' : ι → M → ENNReal}
    (H : ∀ i, ∀ y ∈ (e i).source, ρ i y = ρ' i y) : ChartGlue.glueMeas e ρ = ChartGlue.glueMeas e ρ' := by
  refine iSup_congr fun i => congrArg (Measure.map _) (withDensity_congr_ae ?_)
  filter_upwards [ae_restrict_mem (e i).open_target.measurableSet] with v hv
  exact H i _ ((e i).map_target hv)

theorem part_omF (h : IsRegVar p 1) {E : X.Modules} {m : VMetric p E 2} (H : m.IsCInf) (fl : Vert.Flag E 2) :
    (h.atlas σ).part (fld _ (omF h σ m fl)) 1 =
      Met.bcMeas (S := lineSC fl) (r := 1) (s := 1) (m.met σ) (lineSC_shortExact fl) (fl.isVB 1) (fl.isVB_cokernel 1) ∧
    (h.atlas σ).part (fld _ (omF h σ m fl)) (-1) = 0 := by
  have key (c : AlgChart p σ 1) (y) (hy : y ∈ c.e.source) :
      (dens ((h.atlas σ).loc (fld _ (omF h σ m fl)) c (c.e y))).re =
        Met.bcDens (S := lineSC fl) (r := 1) (s := 1) (m.met σ) (lineSC_shortExact fl) (fl.isVB 1)
          (fl.isVB_cokernel 1) c y :=
    (congrArg (fun t => (dens t).re) ((h.atlas σ).loc_crd _ ⟨(c, y), hy⟩)).trans (dens_ofValues _)
  refine ⟨glue_congr _ fun c y hy => congrArg ENNReal.ofReal ?_, ?_⟩
  · exact (by simp : ∀ t : ℝ, (((1 : ℤˣ) : ℤ) : ℝ) * t = t) _ |>.trans (key c y hy)
  · refine (glue_congr (ρ' := fun _ _ => 0) _ fun c y hy => ENNReal.ofReal_eq_zero.2 ?_).trans ?_
    · refine le_of_eq_of_le (congrArg (_ * ·) (key c y hy)) ?_
      simpa using Met.bcDens_nonneg (S := lineSC fl) (r := 1) (s := 1) (lineSC_shortExact fl) (fl.isVB 1)
        (fl.isVB_cokernel 1) c (H σ) hy
    · refine le_antisymm (iSup_le fun c => le_of_eq ?_) bot_le
      simp [ChartGlue.chartMeas, Function.comp_def]

theorem integral_omF_line (σ : ℤ →+* ℂ) :
    ((isRegVar_proj 1).atlas σ).integral (fld _ (omF (isRegVar_proj 1) σ TautFlag.stdH.h TautFlag.flag)) = 1 := by
  obtain ⟨h₁, h₂⟩ := part_omF σ (isRegVar_proj 1) TautFlag.stdH.cInf TautFlag.flag
  have h₃ : Met.bcMeas (S := lineSC TautFlag.flag) (r := 1) (s := 1) (TautFlag.stdH.h.met σ)
      (lineSC_shortExact TautFlag.flag) (TautFlag.flag.isVB 1) (TautFlag.flag.isVB_cokernel 1) =
      ((TautFlag.stdH.h.stepMet TautFlag.flag 1).met σ).bcMeas (r := 1) (s := 1)
        (VMetric.stepSeq_shortExact TautFlag.flag 1) (TautFlag.flag.isVB (Fin.castSucc 1)) (TautFlag.flag.isVB_gr 1) := by
    congr 1
    refine Met.ext_of_exists fun y => ⟨TautFlag.cE, mem_ptsIn_top, ?_⟩
    ext i j
    exact ((TautFlag.stdH.h.met σ).form_frame TautFlag.cE mem_ptsIn_top i j).symm
  rw [HolAtlas.integral, h₁, h₂, h₃, Measure.real, TautFlag.bcMeas_univ]
  simp

theorem wInt_c1F (h : IsRegVar p 1) (L : HermLB p) (g : CxPts p σ → ℝ) :
    wInt (h.atlas σ) g (fld _ (c1F h σ L)) = (L.φ σ).chernInt 1 Set.univ g := by
  have key (c : AlgChart p σ 1) (y) (hy : y ∈ c.e.source) :
      (dens ((h.atlas σ).loc (fld _ (c1F h σ L)) c (c.e y))).re = c.chernDens (L.φ σ) y := by
    refine (congrArg (fun t => (dens t).re) ((h.atlas σ).loc_crd _ ⟨(c, y), hy⟩)).trans ((dens_ofValues _).trans ?_)
    have hd := (L.cInf σ).contDiffAt c hy (mem_pick (L.φ σ).isLB y)
    have e : -Complex.I * kappa = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
      rw [kappa, ← mul_div_assoc, neg_mul, Complex.I_mul_I]; simp
    rw [AlgChart.chernDens, AlgChart.hess, Matrix.det_unique,
      CurveDens.cHess_apply_eq_ddbar (contDiffAt_ofReal_comp hd), diagVal, ddc, ← mul_assoc (-Complex.I), e,
      Complex.re_ofReal_mul, ← mul_assoc]
    congr 1
    simp only [Nat.factorial_one, Nat.cast_one, pow_one]
    have := Real.pi_pos
    field_simp
  have e (ε : ℤˣ) : (h.atlas σ).part (fld _ (c1F h σ L)) ε = (L.φ σ).chernPart 1 ε :=
    glue_congr _ fun c y hy => congrArg (fun t => ENNReal.ofReal (_ * t)) (key c y hy)
  rw [wInt, e, e, Weight.chernInt, Measure.restrict_univ, Measure.restrict_univ]

theorem chernForm_firstChernClass {B : BottChern} (R : ArRing B h) (L : HermLB p) : R.om (R.c1 L) σ = c1F h σ L :=
  funext fun x => R.chernForm_firstChernClass L σ x _ (mem_pick (L.φ σ).isLB x.pt)

theorem evalF_X {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {ι : Type} (w : ι → A.Pt → Ev n) (i : ι)
    (P Q : MvPolynomial ι ℝ) : evalF A w (MvPolynomial.X i) = fld A (w i) ∧ evalF A w (P * Q) = evalF A w P * evalF A w Q ∧
      evalF A w 1 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> funext x <;> simp [evalF, fld]

theorem chernAt_submatrix {n : ℕ} {r r' : Type} [Fintype r] [DecidableEq r] [Fintype r'] [DecidableEq r'] (e : r' ≃ r)
    {G : ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ} {G' : ReciprocityTheory.L2DbarEstimates.V n → Matrix r' r' ℂ} {v : ReciprocityTheory.L2DbarEstimates.V n}
    (he : G' =ᶠ[nhds v] fun u => (G u).submatrix e e) (j : ℕ) : chernAt G v j = chernAt G' v j := by
  have e₁ : GoodMetric.curvPoly G' v = (GoodMetric.curvPoly G v).submatrix e e := by
    ext1 i j
    simp only [GoodMetric.curvPoly, Matrix.of_apply, Matrix.submatrix_apply, curv_congr he, curv_submatrix_equiv]
  have e₂ (M : Matrix r r (MvPolynomial (Fin n × Fin n) ℂ)) :
      Matrix.charpolyRev (-M.submatrix e e) = Matrix.charpolyRev (-M) := by
    rw [Matrix.charpolyRev, Matrix.charpolyRev, ← Matrix.det_submatrix_equiv_self e (1 - _)]
    congr 1
    ext1 i j
    simp [Matrix.one_apply]
  rw [chernAt, chernAt, GoodMetric.chernPoly, GoodMetric.chernPoly, e₁, e₂]

theorem chernForm_secondChernClass {B : BottChern} (R : ArRing B h) (E : HermVB p 2) (fl : Vert.Flag E.E 2) :
    R.om (R.cl E 2) σ = c2F h σ E.h fl := by
  funext x
  have hS := lineSC_shortExact fl
  have ha := mem_frameAt fl x.pt
  refine (R.om_cl E 2 σ x ((frameAt fl x.pt).mid hS) ha).trans
    (chernAt_submatrix (r := Fin 2) (finSumFinEquiv (m := 1) (n := 1)) ?_ 2)
  filter_upwards [(ChartGlue.isOpen_over x.ch (isOpen_ptsIn _)).mem_nhds (ChartGlue.mem_over x.ch x.2 ha)] with v hv
  exact Met.gram_frame (S := lineSC fl) (r := 1) (s := 1) (E.h.met σ) hS _ hv.2

end GlobalTheory.LineFormModel
