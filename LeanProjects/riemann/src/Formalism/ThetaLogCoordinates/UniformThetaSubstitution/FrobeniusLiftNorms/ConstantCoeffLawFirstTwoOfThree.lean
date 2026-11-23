import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FirstDeriv
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TopsChoicePartA
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.LogarithmEquivalence

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp)

namespace GramFrameCompositionLinFacts

open MvPowerSeries in

theorem continuous_pderiv {R τ : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalSemiring R]
    (e : τ) :
    let := WithPiTopology.instTopologicalSpace (σ := τ) (R := R)
    Continuous (fun f : MvPowerSeries τ R => pderiv R e f) := by
  let := WithPiTopology.instTopologicalSpace (σ := τ) (R := R)
  refine continuous_pi fun n => ?_
  have : (fun f : MvPowerSeries τ R => (pderiv R e f) n) =
      fun f => coeff (n + Finsupp.single e 1) f * ((n e : R) + 1) := by
    funext f
    exact coeff_pderiv f n
  rw [this]
  exact (WithPiTopology.continuous_coeff R _).mul continuous_const

open MvPowerSeries in

theorem pderiv_subst {R σ τ : Type} [CommRing R] [Fintype σ] {a : σ → MvPowerSeries τ R}
    (ha : HasSubst a) (e : τ) (H : MvPowerSeries σ R) :
    pderiv R e (subst a H) = ∑ i, subst a (pderiv R i H) * pderiv R e (a i) := by
  classical
  let : UniformSpace R := ⊥
  have : DiscreteUniformity R := ⟨rfl⟩
  let := WithPiTopology.instTopologicalSpace (σ := τ) (R := R)
  let := WithPiTopology.instTopologicalSpace (σ := σ) (R := R)
  have := WithPiTopology.instIsTopologicalSemiring τ R
  have := WithPiTopology.instT2Space (σ := τ) (R := R)
  have hc1 : Continuous fun H : MvPowerSeries σ R => pderiv R e (subst a H) :=
    (continuous_pderiv e).comp (continuous_subst ha)
  have hc2 : Continuous fun H : MvPowerSeries σ R =>
      ∑ i, subst a (pderiv R i H) * pderiv R e (a i) :=
    continuous_finsetSum _ fun i _ =>
      ((continuous_subst ha).comp (continuous_pderiv i)).mul continuous_const
  have main : ∀ P : MvPolynomial σ R, pderiv R e (subst a (P : MvPowerSeries σ R)) =
      ∑ i, subst a (pderiv R i (P : MvPowerSeries σ R)) * pderiv R e (a i) := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C r =>
      have h0 : subst a (0 : MvPowerSeries σ R) = 0 := by
        rw [← coe_substAlgHom ha, map_zero]
      simp only [MvPolynomial.coe_C, subst_C, pderiv_C, h0, zero_mul, Finset.sum_const_zero]
    | add p q hp hq =>
      simp only [MvPolynomial.coe_add, subst_add ha, map_add, add_mul, Finset.sum_add_distrib]
      rw [hp, hq]
    | mul_X p j hp =>
      simp only [MvPolynomial.coe_mul, MvPolynomial.coe_X, subst_mul ha, subst_X ha,
        Derivation.leibniz, smul_eq_mul, subst_add ha, add_mul, Finset.sum_add_distrib]
      rw [hp, Finset.mul_sum]
      congr 1
      · rw [Finset.sum_eq_single j]
        · rw [pderiv_X_self, ← coe_substAlgHom ha, map_one, mul_one]
        · intro i _ hij
          rw [pderiv_X_of_ne hij.symm, ← coe_substAlgHom ha, map_zero, mul_zero, zero_mul]
        · intro h
          exact absurd (Finset.mem_univ j) h
      · exact Finset.sum_congr rfl fun i _ => by ring
  have key := WithPiTopology.denseRange_toMvPowerSeries (σ := σ) (R := R).equalizer hc1 hc2
    (funext main)
  exact congrFun key H

section Alg

open MvPowerSeries

variable {K : Type} [Field K]

theorem hs2 {τ : Type} {u v : MvPowerSeries τ K} (hu : constantCoeff u = 0)
    (hv : constantCoeff v = 0) : HasSubst ![u, v] :=
  hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> simpa

theorem hs3 {τ : Type} {u v w : MvPowerSeries τ K} (hu : constantCoeff u = 0)
    (hv : constantCoeff v = 0) (hw : constantCoeff w = 0) : HasSubst ![u, v, w] :=
  hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> simpa

theorem subst_subst2 {τ κ : Type} {b : τ → MvPowerSeries κ K} (hb : HasSubst b)
    {u v : MvPowerSeries τ K} (h : HasSubst ![u, v]) (H : MvPowerSeries (Fin 2) K) :
    subst b (subst ![u, v] H) = subst ![subst b u, subst b v] H := by
  rw [subst_comp_subst_apply h hb]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem subst_psubst {τ κ : Type} {b : τ → MvPowerSeries κ K} (hb : HasSubst b)
    {u : MvPowerSeries τ K} (hu : PowerSeries.HasSubst u) (f : PowerSeries K) :
    subst b (PowerSeries.subst u f) = PowerSeries.subst (subst b u) f :=
  subst_comp_subst_apply hu.const hb f

theorem subst_single_variable {τ κ : Type} {b : τ → MvPowerSeries κ K} (hb : HasSubst b) (x : τ)
    (f : PowerSeries K) : subst b (at1 x f) = PowerSeries.subst (b x) f := by
  unfold at1
  rw [subst_psubst hb (PowerSeries.HasSubst.X x), subst_X hb]

theorem subst_identity_two_vars (H : MvPowerSeries (Fin 2) K) :
    subst ![(X 0 : MvPowerSeries (Fin 2) K), X 1] H = H := by
  have : ![(X 0 : MvPowerSeries (Fin 2) K), X 1] = X := by
    funext i
    fin_cases i <;> rfl
  rw [this, subst_self]
  rfl

theorem pderiv_subst2 {τ : Type} {u v : MvPowerSeries τ K} (h : HasSubst ![u, v]) (e : τ)
    (H : MvPowerSeries (Fin 2) K) :
    pderiv K e (subst ![u, v] H) =
      subst ![u, v] (pderiv K 0 H) * pderiv K e u + subst ![u, v] (pderiv K 1 H) * pderiv K e v := by
  rw [pderiv_subst h, Fin.sum_univ_two]
  rfl

theorem pderiv_psubst {τ : Type} {w : MvPowerSeries τ K} (hw : PowerSeries.HasSubst w) (e : τ)
    (f : PowerSeries K) :
    pderiv K e (PowerSeries.subst w f) =
      PowerSeries.subst w (PowerSeries.derivative K f) * pderiv K e w := by
  rw [PowerSeries.subst_def, pderiv_subst hw.const, Fintype.sum_unique]
  rfl

theorem pderiv_single_self {τ : Type} (x : τ) (f : PowerSeries K) :
    pderiv K x (at1 x f) = at1 x (PowerSeries.derivative K f) := by
  unfold at1
  rw [pderiv_psubst (PowerSeries.HasSubst.X x), pderiv_X_self, mul_one]

theorem pderiv_single_of_ne {τ : Type} {x e : τ} (h : x ≠ e) (f : PowerSeries K) :
    pderiv K e (at1 x f) = 0 := by
  unfold at1
  rw [pderiv_psubst (PowerSeries.HasSubst.X x), pderiv_X_of_ne h, mul_zero]

theorem subst_zero_left {τ : Type} {G : MvPowerSeries (Fin 2) K} (hG : DivAB G)
    {w : MvPowerSeries τ K} (hw : constantCoeff w = 0) : subst ![0, w] G = 0 := by
  have hd : (X 0 : MvPowerSeries (Fin 2) K) ∣ G := X_dvd_iff.2 fun m hm => hG m (Or.inl hm)
  obtain ⟨Q, rfl⟩ := hd
  have h := hs2 (map_zero _) hw
  rw [subst_mul h, subst_X h]
  simp

theorem subst_zero_pderiv {τ : Type} (G : MvPowerSeries (Fin 2) K)
    {w : MvPowerSeries τ K} (hw : constantCoeff w = 0) :
    subst ![0, w] (pderiv K 0 G) = PowerSeries.subst w (fLin G) := by
  have hd : (X 0 : MvPowerSeries (Fin 2) K) ∣ pderiv K 0 G - at1 1 (fLin G) := by
    refine X_dvd_iff.2 fun m hm => ?_
    have hm1 : m = Finsupp.single 1 (m 1) := by
      ext i
      fin_cases i <;> simp [hm]
    rw [map_sub, coeff_pderiv, coeff_single_variable_series, if_pos hm1, hm, fLin, PowerSeries.coeff_mk,
      add_comm (Finsupp.single 0 1), ← hm1]
    simp
  obtain ⟨Q, hQ⟩ := hd
  have e : pderiv K 0 G = at1 1 (fLin G) + X 0 * Q := by rw [← hQ]; ring
  have h := hs2 (map_zero _) hw
  rw [e, subst_add h, subst_mul h, subst_X h, subst_single_variable h]
  simp

theorem subst_swap2 {τ : Type} {u v : MvPowerSeries τ K} (h : HasSubst ![u, v])
    (H : MvPowerSeries (Fin 2) K) : subst ![u, v] (swap2 H) = subst ![v, u] H := by
  unfold swap2
  rw [subst_subst2 h HasSubst.X_X, subst_X h, subst_X h]
  rfl

theorem pderiv_swap2 (H : MvPowerSeries (Fin 2) K) :
    pderiv K 1 (swap2 H) = swap2 (pderiv K 0 H) := by
  unfold swap2
  rw [pderiv_subst2 HasSubst.X_X, pderiv_X_self, pderiv_X_of_ne (by decide), mul_one, mul_zero,
    add_zero]

theorem constantCoeff_law_first_two_of_three {F : MvPowerSeries (Fin 2) K} (hF : constantCoeff F = 0) :
    constantCoeff (in3 F) = 0 :=
  constantCoeff_subst_eq_zero HasSubst.X_X (fun i => by fin_cases i <;> simp) hF

end Alg

section Norm

open MvPowerSeries

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem integral_X {τ : Type} (x : τ) : Integral (X x : MvPowerSeries τ K) := by
  classical
  intro n
  rw [coeff_X]
  split_ifs <;> simp

theorem integral_zero {τ : Type} : Integral (0 : MvPowerSeries τ K) := by
  intro n
  simp

theorem integral_pderiv {τ : Type} {f : MvPowerSeries τ K} (hf : Integral f) (e : τ) :
    Integral (pderiv K e f) := by
  intro n
  rw [coeff_pderiv, norm_mul]
  have h : ‖((n e : K) + 1)‖ ≤ 1 := by
    exact_mod_cast IsUltrametricDist.norm_natCast_le_one K (n e + 1)
  exact mul_le_one₀ (hf _) (norm_nonneg _) h

theorem integral_lin [CharZero K] {τ κ : Type} [Finite τ] {D : MvPowerSeries τ K}
    (hD0 : constantCoeff D = 0) (hDi : Integral (mvExp D)) {b : τ → MvPowerSeries κ K}
    (hb0 : ∀ i, constantCoeff (b i) = 0) (hbi : ∀ i, Integral (b i)) (hbD : subst b D = 0)
    (e : τ) : Integral (subst b (pderiv K e D)) := by
  have hb := hasSubst_of_constantCoeff_zero hb0
  have h1 : pderiv K e (mvExp D) = mvExp D * pderiv K e D := by
    unfold mvExp
    rw [pderiv_psubst (PowerSeries.HasSubst.of_constantCoeff_zero hD0),
      PowerSeries.derivative_exp]
  have h2 : subst b (pderiv K e D) = subst b (pderiv K e (mvExp D)) := by
    rw [h1, subst_mul hb, LogarithmEquivalence.subst_mvExp' hb hD0, hbD, LogarithmEquivalence.mvExp_zero', one_mul]
  rw [h2]
  exact LogarithmEquivalence.integral_subst' hb0 hbi (integral_pderiv hDi e)

theorem norm_coeff_dlgF {p : ℕ} (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) (N : ℕ) :
    ‖PowerSeries.coeff N (PowerSeries.derivative K (lgF K p))‖ ≤ 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpK : (p : K) ≠ 0 := by
    rw [← norm_pos_iff, hnp]
    positivity
  rw [PowerSeries.coeff_derivative]
  by_cases h : PowerSeries.coeff (N + 1) (lgF K p) = 0
  · simp [h]
  obtain ⟨j, hj⟩ := coeff_lgF_ne_zero h
  have e : PowerSeries.coeff (N + 1) (lgF K p) * ((N : K) + 1) = (p : K) ^ j := by
    have hc : ((N : K) + 1) = (((p ^ 2) ^ j : ℕ) : K) := by
      rw [← hj]
      push_cast
      ring
    rw [hc, hj, coeff_lgF_pow K hp.two_le]
    push_cast
    field_simp
    ring
  rw [e, norm_pow, hnp]
  exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast hp.one_lt.le))

theorem integral_single_log_derivative {τ : Type} {p : ℕ} (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) (x : τ) :
    Integral (at1 x (PowerSeries.derivative K (lgF K p))) := by
  classical
  intro n
  rw [coeff_single_variable_series]
  split_ifs
  · exact norm_coeff_dlgF hp hnp _
  · simp

theorem constantCoeff_dlgF {p : ℕ} (hp : 2 ≤ p) :
    PowerSeries.constantCoeff (PowerSeries.derivative K (lgF K p)) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
  have := coeff_lgF_pow K hp 0
  simp only [pow_zero, inv_one] at this
  simp [this]

end Norm

end GramFrameCompositionLinFacts

open GramFrameCompositionLinFacts MvPowerSeries in
theorem FirstDeriv_of (hL : LawSymm) : FirstDeriv := by
  intro K _ _ _ p hp hnp F hF G hG hS
  obtain ⟨-, -, -, hF4⟩ := hL K p hp hnp F hF
  obtain ⟨hF0, hFi, hFc⟩ := hF
  obtain ⟨hD0, hDi⟩ := hS
  rw [sub_zero] at hD0 hDi
  have hX : ∀ {τ : Type} (x : τ), constantCoeff (X x : MvPowerSeries τ K) = 0 := fun x => by simp
  have he0 : HasSubst ![(X 0 : MvPowerSeries (Fin 2) K), 0, X 1] :=
    hs3 (hX 0) (map_zero _) (hX 1)
  have hin : HasSubst ![in3 F, (X 2 : MvPowerSeries (Fin 3) K)] :=
    hs2 (constantCoeff_law_first_two_of_three hF0) (hX 2)

  have hE : subst ![(X 0 : MvPowerSeries (Fin 2) K), 0, X 1] (in3 F) = X 0 := by
    unfold in3
    rw [subst_subst2 he0 HasSubst.X_X, subst_X he0, subst_X he0]
    exact hF4
  have hx0 : subst ![(X 0 : MvPowerSeries (Fin 2) K), 0, X 1] (X 0 : MvPowerSeries (Fin 3) K) = X 0 :=
    subst_X he0 0
  have hx1 : subst ![(X 0 : MvPowerSeries (Fin 2) K), 0, X 1] (X 1 : MvPowerSeries (Fin 3) K) = 0 :=
    subst_X he0 1
  have hx2 : subst ![(X 0 : MvPowerSeries (Fin 2) K), 0, X 1] (X 2 : MvPowerSeries (Fin 3) K) = X 1 :=
    subst_X he0 2
  have hA : subst ![(X 0 : MvPowerSeries (Fin 2) K), 0, X 1] (d1 F G) = 0 := by
    unfold d1
    rw [subst_sub he0, subst_sub he0, subst_subst2 he0 hin, subst_subst2 he0 HasSubst.X_X,
      subst_subst2 he0 HasSubst.X_X, hE, hx0, hx1, hx2, subst_zero_left hG (hX 1)]
    simp
  have hI := integral_lin hD0 hDi (b := ![(X 0 : MvPowerSeries (Fin 2) K), 0, X 1])
    (fun i => by fin_cases i <;> simp)
    (fun i => by
      fin_cases i
      · exact integral_X 0
      · exact integral_zero
      · exact integral_X 1) hA 1

  set φ : MvPowerSeries (Fin 2) K :=
    subst ![(X 0 : MvPowerSeries (Fin 2) K), 0, X 1] (pderiv K 1 (in3 F)) with hφ
  have hφ' : φ = subst ![(X 0 : MvPowerSeries (Fin 2) K), 0] (pderiv K 1 F) := by
    rw [hφ]
    unfold in3
    rw [pderiv_subst2 HasSubst.X_X, pderiv_X_self, pderiv_X_of_ne (by decide), mul_zero, mul_one,
      zero_add, subst_subst2 he0 HasSubst.X_X, hx0, hx1]
  have hC : subst ![(X 0 : MvPowerSeries (Fin 2) K), 0, X 1] (pderiv K 1 (d1 F G)) =
      pderiv K 0 G * φ - at1 1 (fLin G) := by
    unfold d1
    rw [map_sub, map_sub, pderiv_subst2 hin, pderiv_subst2 HasSubst.X_X,
      pderiv_subst2 HasSubst.X_X, pderiv_X_self, pderiv_X_of_ne (show (2 : Fin 3) ≠ 1 by decide),
      pderiv_X_of_ne (show (0 : Fin 3) ≠ 1 by decide)]
    simp only [mul_zero, add_zero, sub_zero, mul_one]
    rw [subst_sub he0, subst_mul he0, subst_subst2 he0 hin, subst_subst2 he0 HasSubst.X_X, hE, hx1,
      hx2, subst_identity_two_vars, subst_zero_pderiv G (hX 1)]
    rfl
  have hs0 : HasSubst ![(X 0 : MvPowerSeries (Fin 2) K), 0] := HasSubst.X_zero
  have hlφ : at1 0 (PowerSeries.derivative K (lgF K p)) * φ = 1 := by
    have h1 := congrArg (pderiv K 1) hFc
    unfold cob at h1
    rw [map_sub, map_sub, map_zero, pderiv_single_self, pderiv_single_of_ne (by decide), sub_zero,
      pderiv_psubst (PowerSeries.HasSubst.of_constantCoeff_zero hF0), sub_eq_zero] at h1
    have h2 := congrArg (subst ![(X 0 : MvPowerSeries (Fin 2) K), 0]) h1
    rw [subst_mul hs0, subst_psubst hs0 (PowerSeries.HasSubst.of_constantCoeff_zero hF0), hF4,
      ← hφ', subst_single_variable hs0] at h2
    rw [at1, h2]
    change PowerSeries.subst (0 : MvPowerSeries (Fin 2) K) _ = 1
    rw [PowerSeries.subst_zero_eq_C_constantCoeff, constantCoeff_dlgF hp.two_le]
    simp
  have hfin : pderiv K 0 G - at1 0 (PowerSeries.derivative K (lgF K p)) * at1 1 (fLin G) =
      at1 0 (PowerSeries.derivative K (lgF K p)) * (pderiv K 0 G * φ - at1 1 (fLin G)) := by
    linear_combination (-(pderiv K 0 G)) * hlφ
  rw [hfin, ← hC]
  exact LogarithmEquivalence.integral_mul' (integral_single_log_derivative hp hnp 0) hI

open GramFrameCompositionLinFacts MvPowerSeries in
theorem CobLin_of (_hL : LawSymm) : CobLin := by
  intro K _ _ _ p _ _ F hF G hG hS
  obtain ⟨hF0, -, -⟩ := hF
  obtain ⟨hD0, hDi⟩ := hS
  rw [sub_zero] at hD0 hDi
  have hX : ∀ {τ : Type} (x : τ), constantCoeff (X x : MvPowerSeries τ K) = 0 := fun x => by simp
  have he : HasSubst ![(X 0 : MvPowerSeries (Fin 2) K), X 1, 0] :=
    hs3 (hX 0) (hX 1) (map_zero _)
  have hx2 : subst ![(X 0 : MvPowerSeries (Fin 2) K), X 1, 0] (X 2 : MvPowerSeries (Fin 3) K) = 0 :=
    subst_X he 2

  have term : ∀ w : MvPowerSeries (Fin 3) K, constantCoeff w = 0 → pderiv K 2 w = 0 →
      subst ![(X 0 : MvPowerSeries (Fin 2) K), X 1, 0] (subst ![w, X 2] (swap2 G)) = 0 ∧
      subst ![(X 0 : MvPowerSeries (Fin 2) K), X 1, 0] (pderiv K 2 (subst ![w, X 2] (swap2 G))) =
        PowerSeries.subst (subst ![(X 0 : MvPowerSeries (Fin 2) K), X 1, 0] w) (fLin G) := by
    intro w hw hdw
    have hs := hs2 hw (hX (2 : Fin 3))
    have hw' : constantCoeff (subst ![(X 0 : MvPowerSeries (Fin 2) K), X 1, 0] w) = 0 :=
      constantCoeff_subst_eq_zero he (fun i => by fin_cases i <;> simp) hw
    have hs' := hs2 hw' (map_zero (constantCoeff (σ := Fin 2) (R := K)))
    constructor
    · rw [subst_subst2 he hs, hx2, subst_swap2 hs', subst_zero_left hG hw']
    · rw [pderiv_subst2 hs, hdw, pderiv_X_self, mul_zero, mul_one, zero_add, subst_subst2 he hs,
        hx2, pderiv_swap2, subst_swap2 hs', subst_zero_pderiv G hw']
  have hdF : pderiv K 2 (in3 F) = 0 := by
    unfold in3
    rw [pderiv_subst2 HasSubst.X_X, pderiv_X_of_ne (by decide), pderiv_X_of_ne (by decide),
      mul_zero, mul_zero, add_zero]
  obtain ⟨a1, b1⟩ := term (in3 F) (constantCoeff_law_first_two_of_three hF0) hdF
  obtain ⟨a2, b2⟩ := term (X 0) (hX 0) (pderiv_X_of_ne (by decide))
  obtain ⟨a3, b3⟩ := term (X 1) (hX 1) (pderiv_X_of_ne (by decide))
  have hA : subst ![(X 0 : MvPowerSeries (Fin 2) K), X 1, 0] (d1 F (swap2 G)) = 0 := by
    unfold d1
    rw [subst_sub he, subst_sub he, a1, a2, a3]
    simp
  have hI := integral_lin hD0 hDi (b := ![(X 0 : MvPowerSeries (Fin 2) K), X 1, 0])
    (fun i => by fin_cases i <;> simp)
    (fun i => by
      fin_cases i
      · exact integral_X 0
      · exact integral_X 1
      · exact integral_zero) hA 2
  have hE : subst ![(X 0 : MvPowerSeries (Fin 2) K), X 1, 0] (in3 F) = F := by
    unfold in3
    rw [subst_subst2 he HasSubst.X_X, subst_X he, subst_X he]
    exact subst_identity_two_vars F
  have hC : subst ![(X 0 : MvPowerSeries (Fin 2) K), X 1, 0] (pderiv K 2 (d1 F (swap2 G))) =
      cob F (fLin G) := by
    unfold d1 cob
    rw [map_sub, map_sub, subst_sub he, subst_sub he, b1, b2, b3, hE, subst_X he, subst_X he]
    rfl
  rw [← hC]
  exact hI

namespace GramFrameCompositionLinFacts

theorem sq_modEq_one {p : ℕ} (hp : 2 ≤ p) : p ^ 2 ≡ 1 [MOD p ^ 2 - 1] :=
  ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).2 dvd_rfl).symm

theorem powq_modEq_one {p : ℕ} (hp : 2 ≤ p) (i : ℕ) : (p ^ 2) ^ i ≡ 1 [MOD p ^ 2 - 1] := by
  simpa using (sq_modEq_one hp).pow i

theorem not_one_modEq {p : ℕ} (hp : 2 ≤ p) : ¬ 1 ≡ p [MOD p ^ 2 - 1] := by
  intro h
  have h1 : p ^ 2 - 1 ∣ p - 1 := (Nat.modEq_iff_dvd' (by omega)).1 h
  have h2 := Nat.le_of_dvd (by omega) h1
  have h3 : p * 2 ≤ p ^ 2 := by
    rw [sq]
    exact Nat.mul_le_mul_left p hp
  omega

end GramFrameCompositionLinFacts

open GramFrameCompositionLinFacts MvPowerSeries in
theorem StepI_of (h1 : LemmaOne) (hF : FirstDeriv) (hC : CobLin) : StepI := by
  intro K _ _ _ _ p σ hU F hLaw G hS hd1 hd2
  have hp : p.Prime := hU.1
  have hnp : ‖(p : K)‖ = (p : ℝ)⁻¹ := hU.2.2.1
  have hp2 : 2 ≤ p := hp.two_le
  have hDiv : DivAB G := by
    intro n hn
    by_contra h
    obtain ⟨a, b, -⟩ := hS n h
    omega
  have hFD := hF K p hp hnp F hLaw G hDiv hd1
  have hCL := hC K p hp hnp F hLaw G hDiv hd2
  have hf0 : PowerSeries.constantCoeff (fLin G) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, fLin, PowerSeries.coeff_mk]
    exact hDiv _ (Or.inr (by simp))
  obtain ⟨α, β, R, hα, hR, hf⟩ := h1 K p σ hU F hLaw (fLin G) hf0 hCL
  have key : ∀ j, ‖PowerSeries.coeff j (fLin G) - α * PowerSeries.coeff j (g0F K p)‖ ≤ 1 := by
    intro j
    by_cases hj : j ≡ p [MOD p ^ 2 - 1]
    · have hl : PowerSeries.coeff j (lgF K p) = 0 := by
        by_contra h
        obtain ⟨i, rfl⟩ := coeff_lgF_ne_zero h
        exact not_one_modEq hp2 ((powq_modEq_one hp2 i).symm.trans hj)
      have e : PowerSeries.coeff j (fLin G) - α * PowerSeries.coeff j (g0F K p) =
          PowerSeries.coeff j R := by
        rw [hf]
        simp only [map_add, PowerSeries.coeff_C_mul, hl]
        ring
      rw [e]
      exact hR j
    · have hfj : PowerSeries.coeff j (fLin G) = 0 := by
        by_contra h
        rw [fLin, PowerSeries.coeff_mk] at h
        obtain ⟨-, -, hc⟩ := hS _ h
        simp only [Finsupp.add_apply, Finsupp.single_apply] at hc
        simp only [if_true, Fin.isValue, one_ne_zero, zero_ne_one, if_false, add_zero,
          zero_add] at hc
        apply hj
        have h3 : p * 1 ≡ p * (p * j) [MOD p ^ 2 - 1] := hc.mul_left p
        have h4 : p * (p * j) ≡ 1 * j [MOD p ^ 2 - 1] := by
          rw [← mul_assoc, ← sq]
          exact (sq_modEq_one hp2).mul_right j
        simpa using (h3.trans h4).symm
      have hgj : PowerSeries.coeff j (g0F K p) = 0 := by
        by_contra h
        obtain ⟨i, rfl⟩ := coeff_g0F_ne_zero h
        apply hj
        simpa using (powq_modEq_one hp2 i).mul_left p
      rw [hfj, hgj]
      simp
  refine ⟨α, hα, ?_⟩
  intro n
  have e : coeff n (pderiv K 0 G -
        C α * (at1 0 (PowerSeries.derivative K (lgF K p)) * at1 1 (g0F K p))) =
      coeff n (pderiv K 0 G - at1 0 (PowerSeries.derivative K (lgF K p)) * at1 1 (fLin G)) +
        PowerSeries.coeff (n 0) (PowerSeries.derivative K (lgF K p)) *
          (PowerSeries.coeff (n 1) (fLin G) - α * PowerSeries.coeff (n 1) (g0F K p)) := by
    rw [map_sub, map_sub, coeff_C_mul, coeff_product_single_variables (by decide) (by decide),
      coeff_product_single_variables (by decide) (by decide)]
    ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hFD n) ?_)
  rw [norm_mul]
  exact mul_le_one₀ (norm_coeff_dlgF hp hnp _) (norm_nonneg _) (key _)

end Formalism.InvariantFactorPaths.G7
