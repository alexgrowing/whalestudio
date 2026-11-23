import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan

open Filter Topology
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)

namespace GlobalTheory.GaussGauge

section Pairing

variable {σ : Type*} [Fintype σ]

noncomputable def apolar : MvPolynomial σ ℂ →ₗ[ℂ] MvPowerSeries σ ℂ →ₗ[ℂ] ℂ :=
  (MvPolynomial.basisMonomials σ ℂ).constr ℂ fun m =>
    ((∏ i, (m i).factorial : ℕ) : ℂ) • MvPowerSeries.coeff m

theorem apolar_monomial (m : σ →₀ ℕ) (c : ℂ) (F : MvPowerSeries σ ℂ) :
    apolar (MvPolynomial.monomial m c) F =
      c * ((∏ i, (m i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff m F := by
  have h : (MvPolynomial.monomial m c : MvPolynomial σ ℂ) =
      c • MvPolynomial.basisMonomials σ ℂ m := by
    simp [MvPolynomial.smul_monomial]
  rw [h, map_smul, apolar, Module.Basis.constr_basis]
  simp [mul_assoc]

theorem apolar_apply (P : MvPolynomial σ ℂ) (F : MvPowerSeries σ ℂ) :
    apolar P F = ∑ m ∈ P.support,
      P.coeff m * ((∏ i, (m i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff m F := by
  conv_lhs => rw [P.as_sum]
  simp only [map_sum, LinearMap.sum_apply, apolar_monomial]

theorem prod_factorial_add_single [DecidableEq σ] (m : σ →₀ ℕ) (i : σ) :
    (∏ j, ((m + Finsupp.single i 1 : σ →₀ ℕ) j).factorial : ℕ) =
      (m i + 1) * ∏ j, (m j).factorial := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ (fun j => (m j).factorial) (Finset.mem_univ i), ← mul_assoc]
  congr 1
  · simp [Nat.factorial_succ]
  · refine Finset.prod_congr rfl fun j hj => ?_
    simp [Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hj)]

theorem apolar_X_mul (i : σ) (P : MvPolynomial σ ℂ) (F : MvPowerSeries σ ℂ) :
    apolar (MvPolynomial.X i * P) F = apolar P (MvPowerSeries.pderiv ℂ i F) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial m c =>
    rw [MvPolynomial.X, MvPolynomial.monomial_mul, apolar_monomial, apolar_monomial,
      MvPowerSeries.coeff_pderiv, add_comm _ m, prod_factorial_add_single]
    push_cast
    ring
  | add P Q hP hQ => simp only [mul_add, map_add, LinearMap.add_apply, hP, hQ]

theorem apolar_mul_X (i : σ) (P : MvPolynomial σ ℂ) (F : MvPowerSeries σ ℂ) :
    apolar P (MvPowerSeries.X i * F) = apolar (MvPolynomial.pderiv i P) F := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial m c =>
    rw [MvPolynomial.pderiv_monomial, apolar_monomial, apolar_monomial, MvPowerSeries.X_def,
      MvPowerSeries.coeff_monomial_mul]
    split_ifs with h
    · obtain ⟨m', rfl⟩ := exists_add_of_le h
      rw [add_tsub_cancel_left, add_comm _ m', prod_factorial_add_single]
      simp only [Finsupp.add_apply, Finsupp.single_eq_same]
      push_cast
      ring
    · have : m i = 0 := by
        rw [Finsupp.single_le_iff] at h; omega
      simp [this]
  | add P Q hP hQ => simp only [map_add, LinearMap.add_apply, hP, hQ]

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem polyDeriv_eq_apolar (P : MvPolynomial σ ℂ) (u : σ → W) (f : W → ℂ) :
    polyDeriv P u f 0 = apolar P (taylorDir u f) := by
  rw [apolar_apply, dirPolyDeriv_eq_sum_coeff_taylorDir]

theorem apolar_quad_mul (P : MvPolynomial σ ℂ) (β : σ → σ → ℂ)
    (hP : ∑ s, ∑ t, β s t • MvPolynomial.pderiv s (MvPolynomial.pderiv t P) = 0)
    (F : MvPowerSeries σ ℂ) :
    apolar P ((∑ s, ∑ t, β s t • (MvPowerSeries.X t * MvPowerSeries.X s)) * F) = 0 := by
  have h := congrArg (fun Q => apolar Q F) hP
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, map_zero,
    LinearMap.zero_apply] at h
  rw [← h]
  simp only [Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, mul_assoc, apolar_mul_X]

theorem apolar_eq_zero_of_mem_span {ι : Type*} (v : ι → σ → ℂ) (F : MvPowerSeries σ ℂ)
    (hF : ∀ k, ∑ s, v k s • MvPowerSeries.pderiv ℂ s F = 0) {P : MvPolynomial σ ℂ}
    (hP : P ∈ Ideal.span (Set.range fun k => ∑ s, v k s • (MvPolynomial.X s : MvPolynomial σ ℂ))) :
    apolar P F = 0 := by
  suffices h : ∀ Q, apolar (P * Q) F = 0 by simpa using h 1
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨k, rfl⟩ := hP
    intro Q
    have h := congrArg (apolar Q) (hF k)
    simp only [map_sum, map_smul, map_zero] at h
    rw [← h]
    simp only [Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, apolar_X_mul]
  | zero => simp
  | add P P' _ _ h h' => intro Q; rw [add_mul, map_add, LinearMap.add_apply, h, h', add_zero]
  | smul a P _ h => intro Q; rw [smul_eq_mul, mul_comm a, mul_assoc, h]

end Pairing

section Gauge

variable {σ : Type*} [Fintype σ] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem taylor_quad [DecidableEq σ] (β : σ → σ → ℂ) :
    taylor (fun z : σ → ℂ => ∑ s, ∑ t, β s t * z s * z t) =
      ∑ s, ∑ t, β s t • (MvPowerSeries.X t * MvPowerSeries.X s) := by
  have h := taylor_eval (∑ s, ∑ t, MvPolynomial.C (β s t) * MvPolynomial.X s * MvPolynomial.X t)
  simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X] at h
  rw [h, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply]
  simp only [map_sum, map_mul, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
    MvPolynomial.coe_C, MvPolynomial.coe_X, MvPowerSeries.smul_eq_C_mul]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring

theorem polyDeriv_exp_mul_dir (P : MvPolynomial σ ℂ) (β : σ → σ → ℂ)
    (hP : ∑ s, ∑ t, β s t • MvPolynomial.pderiv s (MvPolynomial.pderiv t P) = 0)
    (u : σ → W) {B G : W → ℂ} (hBa : AnalyticAt ℂ B 0)
    (hB : ∀ z : σ → ℂ, B (∑ i, z i • u i) = ∑ s, ∑ t, β s t * z s * z t)
    (hG : AnalyticAt ℂ G 0) :
    polyDeriv P u (fun w => Complex.exp (B w) * G w) 0 = polyDeriv P u G 0 := by
  classical
  have hd : AnalyticAt ℂ (dslope Complex.exp 0) (B 0) := by
    have : Differentiable ℂ (dslope Complex.exp 0) :=
      differentiableOn_univ.1 ((Complex.differentiableOn_dslope Filter.univ_mem).2
        Complex.differentiable_exp.differentiableOn)
    exact this.analyticAt _
  have hH : AnalyticAt ℂ (fun w => dslope Complex.exp 0 (B w) * G w) 0 := (hd.comp hBa).mul hG
  have h1 : (fun w => Complex.exp (B w) * G w) =
      G + B * fun w => dslope Complex.exp 0 (B w) * G w := by
    funext w
    have := sub_smul_dslope Complex.exp 0 (B w)
    simp only [sub_zero, smul_eq_mul, Complex.exp_zero] at this
    simp only [Pi.add_apply, Pi.mul_apply]
    linear_combination (-G w) * this
  have hT : taylorDir u B = ∑ s, ∑ t, β s t • (MvPowerSeries.X t * MvPowerSeries.X s) := by
    rw [taylorDir_eq_taylor u hBa, ← taylor_quad]
    simp only [hB]
  rw [h1, polyDeriv_eq_apolar, polyDeriv_eq_apolar, taylorDir_add u hG (hBa.mul hH),
    taylorDir_mul u hBa hH, map_add, hT, apolar_quad_mul P β hP, add_zero]

theorem analyticAt_quad (β : σ → σ → ℂ) (x : σ → ℂ) :
    AnalyticAt ℂ (fun z : σ → ℂ => ∑ s, ∑ t, β s t * z s * z t) x := by
  have h (i : σ) : AnalyticAt ℂ (fun z : σ → ℂ => z i) x :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticAt x
  exact Finset.analyticAt_fun_sum _ fun s _ => Finset.analyticAt_fun_sum _ fun t _ =>
    (analyticAt_const.mul (h s)).mul (h t)

theorem polyDeriv_exp_mul [DecidableEq σ] (P : MvPolynomial σ ℂ) (β : σ → σ → ℂ)
    (hP : ∑ s, ∑ t, β s t • MvPolynomial.pderiv s (MvPolynomial.pderiv t P) = 0)
    {G : (σ → ℂ) → ℂ} (hG : AnalyticAt ℂ G 0) :
    polyDeriv P (fun i => (Pi.single i 1 : σ → ℂ))
        (fun z => Complex.exp (∑ s, ∑ t, β s t * z s * z t) * G z) 0 =
      polyDeriv P (fun i => (Pi.single i 1 : σ → ℂ)) G 0 :=
  polyDeriv_exp_mul_dir P β hP _ (analyticAt_quad β 0)
    (fun z => by rw [← pi_eq_sum_univ' z]) hG

theorem polyDeriv_eq_zero_of_mem_span {ι : Type*} (v : ι → σ → ℂ) (u : σ → W) {G : W → ℂ}
    (hG : AnalyticAt ℂ G 0)
    (hv : ∀ k, ∀ᶠ w in 𝓝 (0 : W), fderiv ℂ G w (∑ s, v k s • u s) = 0) {P : MvPolynomial σ ℂ}
    (hP : P ∈ Ideal.span (Set.range fun k => ∑ s, v k s • (MvPolynomial.X s : MvPolynomial σ ℂ))) :
    polyDeriv P u G 0 = 0 := by
  rw [polyDeriv_eq_apolar]
  refine apolar_eq_zero_of_mem_span v _ (fun k => ?_) hP
  rw [← taylorDir_fderiv_sum u hG, taylorDir_congr u (g := 0) (hv k), taylorDir_zero]

omit [Fintype σ] in

theorem eventually_fderiv_eq_zero_of_invariant {G : W → ℂ} {x : W} (hG : AnalyticAt ℂ G x) {v : W}
    (hv : ∀ (w : W) (s : ℂ), G (w + s • v) = G w) : ∀ᶠ w in 𝓝 x, fderiv ℂ G w v = 0 := by
  filter_upwards [hG.eventually_analyticAt] with w hw
  rw [← hw.differentiableAt.lineDeriv_eq_fderiv, lineDeriv]
  simp [hv]

end Gauge

section Harmonic

open GlobalTheory.Harm

variable {T κ : Type*} {p q : ℕ} [Fintype T] [Fintype κ]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

def balCoeff [DecidableEq T] [DecidableEq κ] (γ : T → Fin p → Fin q → ℂ) :
    Var T p q κ → Var T p q κ → ℂ
  | (t, Sum.inl a, k), (t', Sum.inr b, k') => if t' = t ∧ k' = k then γ t a b else 0
  | _, _ => 0

theorem sum_balCoeff_smul [DecidableEq T] [DecidableEq κ] {M : Type*} [AddCommMonoid M]
    [Module ℂ M] (γ : T → Fin p → Fin q → ℂ) (f : Var T p q κ → Var T p q κ → M) :
    ∑ s, ∑ s', balCoeff γ s s' • f s s' =
      ∑ t, ∑ a, ∑ b, ∑ k, γ t a b • f (xVar t a k) (yVar t b k) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_sum_type, balCoeff, zero_smul,
    Finset.sum_const_zero, add_zero, zero_add, ite_and, ite_smul, Finset.sum_ite_irrel,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm

theorem quad_balCoeff [DecidableEq T] [DecidableEq κ] (γ : T → Fin p → Fin q → ℂ)
    (z : Var T p q κ → ℂ) :
    ∑ s, ∑ s', balCoeff γ s s' * z s * z s' =
      ∑ t, ∑ a, ∑ b, ∑ k, γ t a b * z (xVar t a k) * z (yVar t b k) := by
  simpa only [smul_eq_mul, mul_assoc] using sum_balCoeff_smul γ fun s s' => z s * z s'

theorem balCoeff_pderiv_eq_zero [DecidableEq T] [DecidableEq κ] {P : Poly ℂ T p q κ}
    (hP : IsHarmonic P) (γ : T → Fin p → Fin q → ℂ) :
    ∑ s, ∑ s', balCoeff γ s s' • MvPolynomial.pderiv s (MvPolynomial.pderiv s' P) = 0 := by
  rw [sum_balCoeff_smul]
  refine Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun a _ =>
    Finset.sum_eq_zero fun b _ => ?_
  rw [← Finset.smul_sum, ← laplacian_apply, hP, smul_zero]

theorem polyDeriv_exp_balanced_mul_dir {P : Poly ℂ T p q κ} (hP : IsHarmonic P)
    (γ : T → Fin p → Fin q → ℂ) (u : Var T p q κ → W) {B G : W → ℂ} (hBa : AnalyticAt ℂ B 0)
    (hB : ∀ z : Var T p q κ → ℂ, B (∑ i, z i • u i) =
      ∑ t, ∑ a, ∑ b, ∑ k, γ t a b * z (xVar t a k) * z (yVar t b k))
    (hG : AnalyticAt ℂ G 0) :
    polyDeriv P u (fun w => Complex.exp (B w) * G w) 0 = polyDeriv P u G 0 := by
  classical
  exact polyDeriv_exp_mul_dir P _ (balCoeff_pderiv_eq_zero hP γ) u hBa
    (fun z => by rw [hB, quad_balCoeff]) hG

omit [Fintype T] in

theorem det_rowForm_mem {ι : Type*} [Fintype ι] [DecidableEq ι] (t : T) (r : ι → Fin p ⊕ Fin q)
    (ε : ι → κ → ℂ) {v : ι → ℂ} (hv : v ≠ 0) {I : Ideal (Poly ℂ T p q κ)}
    (hI : ∀ k, ∑ a, v a • MvPolynomial.X (t, r a, k) ∈ I) :
    (Matrix.of fun a b => (rowForm t (r a) (ε b) : Poly ℂ T p q κ)).det ∈ I := by
  obtain ⟨a₀, ha₀⟩ := Function.ne_iff.1 hv
  set A : Matrix ι ι (Poly ℂ T p q κ) := Matrix.of fun a b => rowForm t (r a) (ε b) with hA
  have h1 := Matrix.det_updateRow_sum A a₀ fun a => MvPolynomial.C (v a)
  have h2 : (A.updateRow a₀ (∑ a, (MvPolynomial.C (v a) : Poly ℂ T p q κ) • A a)).det ∈ I := by
    rw [Matrix.det_apply']
    refine I.sum_mem fun s _ => I.mul_mem_left _ ?_
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (s.symm a₀))]
    refine I.mul_mem_right _ ?_
    rw [Equiv.apply_symm_apply, Matrix.updateRow_self, Finset.sum_apply]
    have h3 : ∑ a, ((MvPolynomial.C (v a) : Poly ℂ T p q κ) • A a) (s.symm a₀) =
        ∑ k, MvPolynomial.C (ε (s.symm a₀) k) * ∑ a, v a • MvPolynomial.X (t, r a, k) := by
      simp only [hA, Pi.smul_apply, Matrix.of_apply, rowForm_apply, smul_eq_mul, Finset.mul_sum,
        MvPolynomial.smul_eq_C_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [h3]
    exact I.sum_mem fun k _ => I.mul_mem_left _ (hI k)
  rw [h1, smul_eq_mul] at h2
  have h4 := I.mul_mem_left (MvPolynomial.C (v a₀)⁻¹) h2
  rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha₀, map_one, one_mul] at h4

theorem sum_lead_smul {M : Type*} [AddCommMonoid M] [Module ℂ M] {m : ℕ} (i : Fin m)
    {v : Fin m → ℂ} (hv : ∀ a, i < a → v a = 0) (f : Fin m → M) :
    ∑ a : Fin (i.val + 1), v (lead i a) • f (lead i a) = ∑ a, v a • f a := by
  refine Fintype.sum_of_injective (lead i) (Fin.castLE_injective _) _ _ (fun a ha => ?_)
    fun _ => rfl
  rw [hv a, zero_smul]
  by_contra h
  exact ha ⟨⟨a.val, Nat.lt_succ_iff.2 (Fin.le_def.1 (not_lt.1 h))⟩, rfl⟩

theorem lead_ne_zero {m : ℕ} (i : Fin m) {v : Fin m → ℂ} (hv0 : v ≠ 0)
    (hv : ∀ a, i < a → v a = 0) : (fun a : Fin (i.val + 1) => v (lead i a)) ≠ 0 := by
  intro h
  refine hv0 (funext fun a => ?_)
  by_cases ha : i < a
  · exact hv a ha
  · exact congrFun h ⟨a.val, Nat.lt_succ_iff.2 (Fin.le_def.1 (not_lt.1 ha))⟩

theorem rowBlockLeadingMinorProduct_mem_ideal_first {c : T → Fin p → ℕ} (c' : T → Fin q → ℕ) {t : T} {i : Fin p}
    (hc : 1 ≤ c t i) {v : Fin p → ℂ} (hv0 : v ≠ 0) (hv : ∀ a, i < a → v a = 0)
    {I : Ideal (Poly ℂ T p q κ)} (hI : ∀ k, ∑ a, v a • MvPolynomial.X (xVar t a k) ∈ I)
    (ε : T → Fin p → κ → ℂ) (φ : T → Fin q → κ → ℂ) : minorProd c c' ε φ ∈ I := by
  have h : (xMinor t i (ε t) : Poly ℂ T p q κ) ∈ I :=
    det_rowForm_mem t (fun a => Sum.inl (lead i a)) _ (lead_ne_zero i hv0 hv) fun k => by
      rw [sum_lead_smul i hv fun a => (MvPolynomial.X (xVar t a k) : Poly ℂ T p q κ)]
      exact hI k
  refine Ideal.mem_of_dvd I ?_ h
  exact ((dvd_pow_self _ (by omega)).trans (Finset.dvd_prod_of_mem
    (fun i => xMinor t i (ε t) ^ c t i) (Finset.mem_univ i))).mul_right _ |>.trans
    (Finset.dvd_prod_of_mem (fun t : T => ((∏ i : Fin p, xMinor t i (ε t) ^ c t i) *
      ∏ i : Fin q, yMinor t i (φ t) ^ c' t i : Poly ℂ T p q κ)) (Finset.mem_univ t))

theorem minorProd_mem_y (c : T → Fin p → ℕ) {c' : T → Fin q → ℕ} {t : T} {i : Fin q}
    (hc : 1 ≤ c' t i) {v : Fin q → ℂ} (hv0 : v ≠ 0) (hv : ∀ a, i < a → v a = 0)
    {I : Ideal (Poly ℂ T p q κ)} (hI : ∀ k, ∑ a, v a • MvPolynomial.X (yVar t a k) ∈ I)
    (ε : T → Fin p → κ → ℂ) (φ : T → Fin q → κ → ℂ) : minorProd c c' ε φ ∈ I := by
  have h : (yMinor t i (φ t) : Poly ℂ T p q κ) ∈ I :=
    det_rowForm_mem t (fun a => Sum.inr (lead i a)) _ (lead_ne_zero i hv0 hv) fun k => by
      rw [sum_lead_smul i hv fun a => (MvPolynomial.X (yVar t a k) : Poly ℂ T p q κ)]
      exact hI k
  refine Ideal.mem_of_dvd I ?_ h
  exact ((dvd_pow_self _ (by omega)).trans (Finset.dvd_prod_of_mem
    (fun i => yMinor t i (φ t) ^ c' t i) (Finset.mem_univ i))).mul_left _ |>.trans
    (Finset.dvd_prod_of_mem (fun t : T => ((∏ i : Fin p, xMinor t i (ε t) ^ c t i) *
      ∏ i : Fin q, yMinor t i (φ t) ^ c' t i : Poly ℂ T p q κ)) (Finset.mem_univ t))

noncomputable def minorSpan (κ : Type*) [Fintype κ] (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) :
    Submodule ℂ (Poly ℂ T p q κ) :=
  Submodule.span ℂ (Set.range fun x : (T → Fin p → κ → ℂ) × (T → Fin q → κ → ℂ) =>
    minorProd c c' x.1 x.2)

theorem minorProd_mem_minorSpan (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (ε : T → Fin p → κ → ℂ) (φ : T → Fin q → κ → ℂ) : minorProd c c' ε φ ∈ minorSpan κ c c' :=
  Submodule.subset_span ⟨(ε, φ), rfl⟩

theorem span_le_minorSpan {c : T → Fin p → ℕ} {c' : T → Fin q → ℕ} {S : Set (Poly ℂ T p q κ)}
    (hS : ∀ Q ∈ S, ∃ ε φ, Q = minorProd c c' ε φ) : Submodule.span ℂ S ≤ minorSpan κ c c' :=
  Submodule.span_le.2 fun Q hQ => by
    obtain ⟨ε, φ, rfl⟩ := hS Q hQ
    exact minorProd_mem_minorSpan c c' ε φ

theorem orbitSpan_le_minorSpan {n : ℕ} (h : p + q ≤ n) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) :
    orbitSpan ℂ h c c' ≤ minorSpan (Fin n) c c' :=
  span_le_minorSpan (by
    rintro _ ⟨g, rfl⟩
    exact ⟨_, _, colAct_minorProd g c c' _ _⟩)

theorem polyDeriv_eq_zero_of_mem_span_comb {σ ι α : Type*} [Fintype σ] [Fintype α] (v : α → ℂ)
    (l : ι → α → σ) (u : σ → W) {G : W → ℂ} (hG : AnalyticAt ℂ G 0)
    (hv : ∀ k, ∀ᶠ w in 𝓝 (0 : W), fderiv ℂ G w (∑ a, v a • u (l k a)) = 0) {P : MvPolynomial σ ℂ}
    (hP : P ∈ Ideal.span
      (Set.range fun k => ∑ a, v a • (MvPolynomial.X (l k a) : MvPolynomial σ ℂ))) :
    polyDeriv P u G 0 = 0 := by
  classical
  have key {M : Type _} [AddCommMonoid M] [Module ℂ M] (f : σ → M) (k : ι) :
      ∑ s, (∑ a, if l k a = s then v a else 0) • f s = ∑ a, v a • f (l k a) := by
    simp only [Finset.sum_smul]
    rw [Finset.sum_comm]
    simp [ite_smul]
  have key' (f : σ → MvPolynomial σ ℂ) (k : ι) :
      ∑ s, (∑ a, if l k a = s then v a else 0) • f s = ∑ a, v a • f (l k a) := by
    simp only [Finset.sum_smul]
    rw [Finset.sum_comm]
    simp [ite_smul]
  refine polyDeriv_eq_zero_of_mem_span (fun k s => ∑ a, if l k a = s then v a else 0) u hG
    (fun k => by rw [key]; exact hv k) ?_
  simpa only [key'] using hP

theorem polyDeriv_eq_zero_x_of_fderiv {c : T → Fin p → ℕ} {c' : T → Fin q → ℕ}
    {P : Poly ℂ T p q κ} (hP : P ∈ minorSpan κ c c') {t : T} {i : Fin p} (hc : 1 ≤ c t i)
    {v : Fin p → ℂ} (hv0 : v ≠ 0) (hv : ∀ a, i < a → v a = 0) (u : Var T p q κ → W) {G : W → ℂ}
    (hG : AnalyticAt ℂ G 0)
    (hd : ∀ k, ∀ᶠ w in 𝓝 (0 : W), fderiv ℂ G w (∑ a, v a • u (xVar t a k)) = 0) :
    polyDeriv P u G 0 = 0 := by
  refine polyDeriv_eq_zero_of_mem_span_comb v (fun k a => xVar t a k) u hG hd ?_
  refine (Submodule.span_le (p := Submodule.restrictScalars ℂ (Ideal.span _))).2 ?_ hP
  rintro _ ⟨x, rfl⟩
  refine rowBlockLeadingMinorProduct_mem_ideal_first (I := Ideal.span _) c' hc hv0 hv (fun k => ?_) _ _
  exact Ideal.subset_span ⟨k, rfl⟩

theorem polyDeriv_eq_zero_y_of_fderiv {c : T → Fin p → ℕ} {c' : T → Fin q → ℕ}
    {P : Poly ℂ T p q κ} (hP : P ∈ minorSpan κ c c') {t : T} {i : Fin q} (hc : 1 ≤ c' t i)
    {v : Fin q → ℂ} (hv0 : v ≠ 0) (hv : ∀ a, i < a → v a = 0) (u : Var T p q κ → W) {G : W → ℂ}
    (hG : AnalyticAt ℂ G 0)
    (hd : ∀ k, ∀ᶠ w in 𝓝 (0 : W), fderiv ℂ G w (∑ a, v a • u (yVar t a k)) = 0) :
    polyDeriv P u G 0 = 0 := by
  refine polyDeriv_eq_zero_of_mem_span_comb v (fun k a => yVar t a k) u hG hd ?_
  refine (Submodule.span_le (p := Submodule.restrictScalars ℂ (Ideal.span _))).2 ?_ hP
  rintro _ ⟨x, rfl⟩
  refine minorProd_mem_y (I := Ideal.span _) c hc hv0 hv (fun k => ?_) _ _
  exact Ideal.subset_span ⟨k, rfl⟩

theorem eq_zero_of_last_lt {m : ℕ} {i : Fin m} (hi : i.val + 1 = m) (v : Fin m → ℂ) (a : Fin m)
    (h : i < a) : v a = 0 := by
  have := a.isLt
  rw [Fin.lt_def] at h
  omega

theorem polyDeriv_eq_zero_x_dir {c : T → Fin p → ℕ} {c' : T → Fin q → ℕ}
    {P : Poly ℂ T p q κ} (hP : P ∈ minorSpan κ c c') {t : T} {i : Fin p} (hi : i.val + 1 = p)
    (hc : 1 ≤ c t i) {v : Fin p → ℂ} (hv0 : v ≠ 0) (u : Var T p q κ → W) {G : W → ℂ}
    (hG : AnalyticAt ℂ G 0)
    (hinv : ∀ k (w : W) (s : ℂ), G (w + s • ∑ a, v a • u (xVar t a k)) = G w) :
    polyDeriv P u G 0 = 0 :=
  polyDeriv_eq_zero_x_of_fderiv hP hc hv0 (eq_zero_of_last_lt hi v) u hG fun k =>
    eventually_fderiv_eq_zero_of_invariant hG (hinv k)

theorem polyDeriv_eq_zero_y_dir {c : T → Fin p → ℕ} {c' : T → Fin q → ℕ}
    {P : Poly ℂ T p q κ} (hP : P ∈ minorSpan κ c c') {t : T} {i : Fin q} (hi : i.val + 1 = q)
    (hc : 1 ≤ c' t i) {v : Fin q → ℂ} (hv0 : v ≠ 0) (u : Var T p q κ → W) {G : W → ℂ}
    (hG : AnalyticAt ℂ G 0)
    (hinv : ∀ k (w : W) (s : ℂ), G (w + s • ∑ a, v a • u (yVar t a k)) = G w) :
    polyDeriv P u G 0 = 0 :=
  polyDeriv_eq_zero_y_of_fderiv hP hc hv0 (eq_zero_of_last_lt hi v) u hG fun k =>
    eventually_fderiv_eq_zero_of_invariant hG (hinv k)

variable [DecidableEq T] [DecidableEq κ]

end Harmonic

end GlobalTheory.GaussGauge
