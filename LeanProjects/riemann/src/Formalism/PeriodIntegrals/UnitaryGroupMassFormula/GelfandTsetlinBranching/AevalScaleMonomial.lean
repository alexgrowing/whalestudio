import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.FockFRowActRight

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.REAL (fockF)

def IsUU {n : ℕ} (u : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ i j, j < i → u i j = 0) ∧ ∀ i, u i i = 1

def matOf {n : ℕ} (x : Fin n × Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => x (i, j)

theorem matOf_self {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) : matOf (fun v => Y v.1 v.2) = Y := by
  ext i j; rfl

def hwAt {n : ℕ} (κ : Fin n → ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  eval (fun v => Y v.1 v.2) (hw ℂ le_rfl κ)

theorem rowAct_comp_apply {R : Type} [CommRing R] {r c : ℕ} (A B : Matrix (Fin r) (Fin r) R)
    (p : MvPolynomial (Fin r × Fin c) R) : rowAct R B (rowAct R A p) = rowAct R (A * B) p := by
  rw [Formalism.UG.P.wlocal_rowAct_mul]; rfl

theorem rowAct_one_apply {R : Type} [CommRing R] {r c : ℕ} (p : MvPolynomial (Fin r × Fin c) R) :
    rowAct R (1 : Matrix (Fin r) (Fin r) R) p = p := by
  rw [Formalism.UG.P.wlocal_rowAct_one]; rfl

theorem map_rowAct {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r c : ℕ}
    (A : Matrix (Fin r) (Fin r) R) (p : MvPolynomial (Fin r × Fin c) R) :
    map φ (rowAct R A p) = rowAct S (A.map φ) (map φ p) := by
  have : (map φ).comp (rowAct R (n := c) A).toRingHom =
      (rowAct S (n := c) (A.map φ)).toRingHom.comp (map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [rowAct]
    · intro v; simp [rowAct]
  exact congrArg (fun ψ => ψ p) this

theorem eval_aeval_self {σ : Type} (x : σ → ℂ) (g : σ → MvPolynomial σ ℂ) (p : MvPolynomial σ ℂ) :
    eval x (aeval g p) = eval (fun v => eval x (g v)) p := by
  rw [aeval_eq_bind₁]; exact eval₂Hom_bind₁ _ _ _ _

section MC

variable {n k : ℕ} (f : MvPolynomial (Fin (n + k) × Fin (n + k)) ℂ)

def mcF (Y : Matrix (Fin n) (Fin n) ℂ) : ℂ := fockF (rowAct ℂ (iotaC ℂ n k Y).transpose f) f

def genY (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) ℂ) := Matrix.of fun i j => X (i, j)

def mcP : MvPolynomial (Fin n × Fin n) ℂ :=
  ∑ m ∈ f.support, (rowAct (MvPolynomial (Fin n × Fin n) ℂ) (iotaC _ n k (genY n)).transpose
      (map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ) f)).coeff m * C (star (f.coeff m) * fct m)

theorem eval_matrixCoeffPoly (x : Fin n × Fin n → ℂ) : eval x (mcP f) = mcF f (matOf x) := by
  have hmap : map (eval x) (rowAct (MvPolynomial (Fin n × Fin n) ℂ) (iotaC _ n k (genY n)).transpose
      (map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ) f)) = rowAct ℂ (iotaC ℂ n k (matOf x)).transpose f := by
    rw [map_rowAct, map_map, Matrix.transpose_map, iotaC_map]
    have h1 : (eval x).comp (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ) = RingHom.id ℂ :=
      RingHom.ext fun a => by simp
    have h2 : (genY n).map (eval x) = matOf x := by ext i j; simp [genY, matOf]
    rw [h1, map_id, h2]
  unfold mcP mcF
  rw [map_sum, fockF_eq_sum _ f f.support (fun m _ h => mem_support_iff.mpr h)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, eval_C, ← coeff_map, hmap, mul_assoc]

variable {f}

theorem mcF_mulU (hU : ∀ u, IsUU u → rowAct ℂ (iotaC ℂ n k u).transpose f = f)
    (Y U : Matrix (Fin n) (Fin n) ℂ) (hUU : IsUU U) : mcF f (Y * U) = mcF f Y := by
  unfold mcF
  rw [iotaC_mul, Matrix.transpose_mul, ← rowAct_comp_apply, hU U hUU]

theorem mcF_Lmul (hU : ∀ u, IsUU u → rowAct ℂ (iotaC ℂ n k u).transpose f = f)
    (L Y : Matrix (Fin n) (Fin n) ℂ) (hL : IsUU L.conjTranspose) : mcF f (L * Y) = mcF f Y := by
  unfold mcF
  rw [iotaC_mul, Matrix.transpose_mul, ← rowAct_comp_apply, fockRowAdj (n + k) (n + k)]
  have : ((iotaC ℂ n k L).transpose).conjTranspose = (iotaC ℂ n k L.conjTranspose).transpose := by
    rw [iotaC_conj]; ext i j; simp
  rw [this, hU _ hL]

theorem mcF_diag {κ : Fin n → ℕ}
    (hT : ∀ t : Fin n → ℂˣ, rowAct ℂ (iotaC ℂ n k (Matrix.diagonal fun i => (t i : ℂ))).transpose f =
      (∏ i, (t i : ℂ) ^ κ i) • f)
    (Y : Matrix (Fin n) (Fin n) ℂ) (t : Fin n → ℂˣ) :
    mcF f (Y * Matrix.diagonal fun i => (t i : ℂ)) = (∏ i, (t i : ℂ) ^ κ i) * mcF f Y := by
  unfold mcF
  rw [iotaC_mul, Matrix.transpose_mul, ← rowAct_comp_apply, hT t, map_smul, fockF_smul_left]

theorem mcF_one : mcF f 1 = fockF f f := by
  unfold mcF
  rw [iotaC_one, Matrix.transpose_one, rowAct_one_apply]

theorem isUU_E (l j : Fin n) (hlj : l < j) (c : ℂ) : IsUU (Formalism.UG.P.wlocal_E l j c) := by
  refine ⟨fun i j' h => ?_, fun i => ?_⟩
  · simp only [Formalism.UG.P.wlocal_E]
    rw [if_neg (by intro e; subst e; exact lt_irrefl _ h), if_neg]
    · simp
    · rintro ⟨rfl, rfl⟩; exact lt_asymm h hlj
  · simp only [Formalism.UG.P.wlocal_E, if_true]
    rw [if_neg]
    · simp
    · rintro ⟨rfl, rfl⟩; exact lt_irrefl _ hlj

theorem isUU_E_conj (a b : Fin n) (hab : a < b) (c : ℂ) :
    IsUU (Formalism.UG.P.wlocal_E b a c).conjTranspose := by
  refine ⟨fun i j' h => ?_, fun i => ?_⟩
  · simp only [Matrix.conjTranspose_apply, Formalism.UG.P.wlocal_E]
    rw [if_neg (by intro e; subst e; exact lt_irrefl _ h), if_neg]
    · simp
    · rintro ⟨rfl, rfl⟩; exact lt_asymm h hab
  · simp only [Matrix.conjTranspose_apply, Formalism.UG.P.wlocal_E, if_true]
    rw [if_neg]
    · simp
    · rintro ⟨rfl, h2⟩; exact lt_irrefl _ (h2 ▸ hab)

theorem colAdd_matrixCoeffPoly (hU : ∀ u, IsUU u → rowAct ℂ (iotaC ℂ n k u).transpose f = f)
    (l j : Fin n) (hlj : l < j) (c : ℂ) : colAdd ℂ l j c (mcP f) = mcP f := by
  apply MvPolynomial.funext
  intro x
  rw [colAdd, eval_aeval_self]
  have key : (fun v : Fin n × Fin n => eval x (if v.2 = j then X v + C c * X (v.1, l) else X v)) =
      fun v => (matOf x * Formalism.UG.P.wlocal_E l j c) v.1 v.2 := by
    funext v
    simp only [matOf, Matrix.mul_apply, Matrix.of_apply, Formalism.UG.P.wlocal_E, mul_add,
      Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases h : v.2 = j
    · simp [h, mul_comm] <;> rw [← h]
    · simp [h]
  rw [key, eval_matrixCoeffPoly, matOf_self, mcF_mulU hU _ _ (isUU_E l j hlj c), ← eval_matrixCoeffPoly]

theorem rowDiv_matrixCoeffPoly_eq_zero (hU : ∀ u, IsUU u → rowAct ℂ (iotaC ℂ n k u).transpose f = f)
    (a b : Fin n) (hab : a < b) (kk : ℕ) (hk : 1 ≤ kk) : rowDiv ℂ a b kk (mcP f) = 0 := by
  have hpt : ∀ c : ℂ, rowAct ℂ (Formalism.UG.P.wlocal_E b a c) (mcP f) = mcP f := by
    intro c
    apply MvPolynomial.funext
    intro x
    rw [rowAct, eval_aeval_self]
    have key : (fun v : Fin n × Fin n => eval x (∑ b' : Fin n, C (Formalism.UG.P.wlocal_E b a c v.1 b') * X (b', v.2))) =
        fun v => (Formalism.UG.P.wlocal_E b a c * matOf x) v.1 v.2 := by
      funext v
      simp [matOf, Matrix.mul_apply]
    rw [key, eval_matrixCoeffPoly, matOf_self, mcF_Lmul hU _ _ (isUU_E_conj a b hab c), ← eval_matrixCoeffPoly]
  set q := rowGen ℂ a b (mcP f) - Polynomial.C (mcP f) with hq
  have hroot : ∀ c : ℂ, q.IsRoot (C c) := by
    intro c
    rw [Polynomial.IsRoot, hq, Polynomial.eval_sub, Formalism.UG.P.wlocal_eval_rowGen b a c (mcP f), hpt,
      Polynomial.eval_C, sub_self]
  have hq0 : q = 0 := Polynomial.eq_zero_of_infinite_isRoot q
    (Set.infinite_of_injective_forall_mem (MvPolynomial.C_injective (Fin n × Fin n) ℂ) hroot)
  have : rowGen ℂ a b (mcP f) = Polynomial.C (mcP f) := sub_eq_zero.mp hq0
  rw [rowDiv, this, Polynomial.coeff_C, if_neg (by omega)]

theorem aeval_scale_monomial (t : Fin n → ℂ) (m : Fin n × Fin n →₀ ℕ) (a : ℂ) :
    aeval (fun v : Fin n × Fin n => C (t v.2) * X v) (monomial m a) =
      monomial m (a * m.prod fun v e => t v.2 ^ e) := by
  rw [aeval_monomial, monomial_eq]
  simp only [mul_pow, Finsupp.prod_mul, algebraMap_eq, map_mul]
  rw [map_finsuppProd]
  simp only [map_pow]
  ring

theorem coeff_scale (t : Fin n → ℂ) (P : MvPolynomial (Fin n × Fin n) ℂ) (m : Fin n × Fin n →₀ ℕ) :
    coeff m (aeval (fun v : Fin n × Fin n => C (t v.2) * X v) P) = (m.prod fun v e => t v.2 ^ e) * coeff m P := by
  refine MvPolynomial.induction_on' P ?_ ?_
  · intro m' a
    rw [aeval_scale_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; ring
    · simp
  · intro p q hp hq
    rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

theorem isWH_of_scale (κ : Fin n → ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ)
    (h : ∀ t : Fin n → ℂˣ, aeval (fun v : Fin n × Fin n => C ((t v.2 : ℂ)) * X v) P =
      C (∏ i, (t i : ℂ) ^ κ i) * P) :
    IsWeightedHomogeneous (colW n n) P κ := by
  classical
  intro m hm
  funext s
  let t : Fin n → ℂˣ := fun i => if i = s then Units.mk0 2 two_ne_zero else 1
  have h0 := coeff_scale (fun i => (t i : ℂ)) P m
  rw [h t, coeff_C_mul] at h0
  have h2 := (mul_right_cancel₀ hm h0).symm
  have ht : ∀ i, (t i : ℂ) = if i = s then 2 else 1 := by
    intro i; simp only [t]; split_ifs <;> simp
  simp only [ht, Finsupp.prod, ite_pow, one_pow] at h2
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_pow_eq_pow_sum,
    Finset.prod_ite_eq' Finset.univ s, if_pos (Finset.mem_univ _)] at h2
  have h3 : ∑ v ∈ m.support with v.2 = s, m v = κ s := by
    have h4 : ((2 ^ (∑ v ∈ m.support with v.2 = s, m v) : ℕ) : ℂ) = ((2 ^ κ s : ℕ) : ℂ) := by
      push_cast; exact h2
    exact Nat.pow_right_injective (le_refl 2) (Nat.cast_injective h4)
  rw [← h3, Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [colW, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases hv : v.2 = s
  · simp [hv]
  · simp [hv, Ne.symm hv]

theorem eval_lpMinor_one (s : ℕ) (h1 h2 : s ≤ n) :
    eval (fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) ℂ) v.1 v.2) (lpMinor ℂ s h1 h2) = 1 := by
  rw [lpMinor, RingHom.map_det]
  have : (eval fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) ℂ) v.1 v.2).mapMatrix
      (Matrix.of fun p q : Fin s => (X (Fin.castLE h1 p, Fin.castLE h2 q) : MvPolynomial (Fin n × Fin n) ℂ)) = 1 := by
    ext p q
    simp [Matrix.one_apply, Fin.castLE_inj]
  rw [this, Matrix.det_one]

theorem hwAt_one (κ : Fin n → ℕ) : hwAt κ 1 = 1 := by
  unfold hwAt hw
  rw [map_prod]
  simp only [map_pow, eval_lpMinor_one, one_pow, Finset.prod_const_one]

theorem mc_hw (κ : Fin n → ℕ) (hκ : Antitone κ)
    (hU : ∀ u, IsUU u → rowAct ℂ (iotaC ℂ n k u).transpose f = f)
    (hT : ∀ t : Fin n → ℂˣ, rowAct ℂ (iotaC ℂ n k (Matrix.diagonal fun i => (t i : ℂ))).transpose f =
      (∏ i, (t i : ℂ) ^ κ i) • f)
    (Y : Matrix (Fin n) (Fin n) ℂ) : mcF f Y = fockF f f * hwAt κ Y := by
  have hhom : IsWeightedHomogeneous (colW n n) (mcP f) κ := by
    apply isWH_of_scale
    intro t
    apply MvPolynomial.funext
    intro x
    rw [eval_aeval_self, eval_mul, eval_C, eval_matrixCoeffPoly, eval_matrixCoeffPoly]
    have : matOf (fun v : Fin n × Fin n => eval x (C ((t v.2 : ℂ)) * X v)) =
        matOf x * Matrix.diagonal fun i => (t i : ℂ) := by
      ext i j; simp [matOf, Matrix.mul_diagonal, mul_comm]
    rw [this, mcF_diag hT]
  have hmem : mcP f ∈ dualWeyl ℂ n n κ :=
    (dualWeylPoint ℂ n n κ (mcP f)).mpr ⟨hhom, fun l j hlj c => colAdd_matrixCoeffPoly hU l j hlj c⟩
  obtain ⟨c, hc⟩ := hwLine ℂ n n le_rfl κ hκ (mcP f) hmem
    (fun a b hab kk hk => rowDiv_matrixCoeffPoly_eq_zero hU a b hab kk hk)
  have h1 : eval (fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) ℂ) v.1 v.2) (mcP f) = fockF f f := by
    rw [eval_matrixCoeffPoly, matOf_self, mcF_one]
  rw [hc, smul_eval] at h1
  have h1' : c = fockF f f := by
    have := hwAt_one κ
    unfold hwAt at this
    rw [this, mul_one] at h1
    exact h1
  rw [← matOf_self Y, ← eval_matrixCoeffPoly, hc, smul_eval, h1']
  rfl

end MC

end PI.WGB
