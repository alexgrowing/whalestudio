import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableAtOfSmooth

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate

namespace GlobalTheory.CompanionTheory.RCalc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

section Pw

variable {A : Type*} [Ring A]

noncomputable def Pw (T : Fin n → Fin n → A) : ℕ → Fin n → Fin n → A
  | 0, a, b => if a = b then 1 else 0
  | m + 1, a, b => ∑ c, T a c * Pw T m c b

theorem Pw_eq_pow (T : Fin n → Fin n → A) (m : ℕ) (a b : Fin n) : Pw T m a b = ((Matrix.of T) ^ m) a b := by
  induction m generalizing a b with
  | zero => simp [Pw, Matrix.one_apply]
  | succ m ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp [Pw, ih]

theorem Pw_commute {T : Fin n → Fin n → A} {u : A} (h : ∀ a b, Commute u (T a b)) (m : ℕ) (a b : Fin n) :
    Commute u (Pw T m a b) := by
  induction m generalizing a b with
  | zero =>
    simp only [Pw]; split_ifs
    · exact Commute.one_right u
    · exact Commute.zero_right u
  | succ m ih =>
    simp only [Pw]
    exact Commute.sum_right _ _ _ fun c _ => (h a c).mul_right (ih c b)

theorem Pw_bracket {T : Fin n → Fin n → A}
    (hT : ∀ a b c d, T a b * T c d - T c d * T a b = (if b = c then T a d else 0) - (if d = a then T c b else 0))
    (m : ℕ) (a b c d : Fin n) :
    T a b * Pw T m c d - Pw T m c d * T a b =
      (if b = c then Pw T m a d else 0) - (if d = a then Pw T m c b else 0) := by
  induction m generalizing c d with
  | zero =>
    simp only [Pw]
    by_cases h1 : c = d <;> by_cases h2 : b = c <;> by_cases h3 : d = a <;> simp_all [eq_comm]
  | succ m ih =>
    have e : ∀ e, T a b * (T c e * Pw T m e d) - (T c e * Pw T m e d) * T a b =
        (T a b * T c e - T c e * T a b) * Pw T m e d + T c e * (T a b * Pw T m e d - Pw T m e d * T a b) := by
      intro e; noncomm_ring
    simp only [Pw]
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    simp only [e, hT, ih, sub_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul, mul_ite, zero_mul,
      mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have s1 : (∑ x, if x = a then T c b * Pw T m x d else 0) = T c b * Pw T m a d := by simp
    have s2 : (∑ x, if b = x then T c x * Pw T m a d else 0) = T c b * Pw T m a d := by simp
    by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [h1, h2, Finset.sum_const_zero] <;> abel

theorem trPw_central {T : Fin n → Fin n → A}
    (hT : ∀ a b c d, T a b * T c d - T c d * T a b = (if b = c then T a d else 0) - (if d = a then T c b else 0))
    (m : ℕ) (a b : Fin n) : Commute (T a b) (∑ c, Pw T m c c) := by
  have : T a b * ∑ c, Pw T m c c - (∑ c, Pw T m c c) * T a b = 0 := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    simp only [Pw_bracket hT, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp
  exact sub_eq_zero.mp this

end Pw

section Lie

variable {A : Type*} [Ring A] [Algebra ℂ A]

def eps (s : Bool) : ℂ := if s then -Complex.I else Complex.I

theorem eps_mul_self (s : Bool) : eps s * eps s = -1 := by
  cases s <;> simp [eps]

theorem eps_mul_not (s : Bool) : eps (!s) = - eps s := by
  cases s <;> simp [eps]

def TX (D : Mat n →+ A) (s : Bool) (X : Mat n) : A := (1 / 2 : ℂ) • (D X + eps s • D (Complex.I • X))

def Tc (D : Mat n →+ A) (s : Bool) (a b : Fin n) : A := TX D s (Matrix.single a b 1)

theorem TX_sub (D : Mat n →+ A) (s : Bool) (X Y : Mat n) : TX D s (X - Y) = TX D s X - TX D s Y := by
  simp only [TX, smul_sub, map_sub]
  module

private theorem quad (ε : ℂ) (hε : ε * ε = -1) (a b c d Z W : A) (h1 : a * c - c * a = Z) (h2 : a * d - d * a = W)
    (h3 : b * c - c * b = W) (h4 : b * d - d * b = -Z) :
    ((1 / 2 : ℂ) • (a + ε • b)) * ((1 / 2 : ℂ) • (c + ε • d)) - ((1 / 2 : ℂ) • (c + ε • d)) * ((1 / 2 : ℂ) • (a + ε • b)) =
      (1 / 2 : ℂ) • (Z + ε • W) := by
  have key : ((1 / 2 : ℂ) • (a + ε • b)) * ((1 / 2 : ℂ) • (c + ε • d)) - ((1 / 2 : ℂ) • (c + ε • d)) * ((1 / 2 : ℂ) • (a + ε • b)) =
      (1 / 4 : ℂ) • ((a * c - c * a) + ε • (a * d - d * a) + ε • (b * c - c * b) + (ε * ε) • (b * d - d * b)) := by
    simp only [smul_mul_assoc, mul_smul_comm, mul_add, add_mul, smul_smul, smul_add, smul_sub]
    module
  rw [key, h1, h2, h3, h4, hε]
  module

private theorem quad' (ε : ℂ) (hε : ε * ε = -1) (a b c d Z W : A) (h1 : a * c - c * a = Z) (h2 : a * d - d * a = W)
    (h3 : b * c - c * b = W) (h4 : b * d - d * b = -Z) :
    ((1 / 2 : ℂ) • (a + ε • b)) * ((1 / 2 : ℂ) • (c + (-ε) • d)) - ((1 / 2 : ℂ) • (c + (-ε) • d)) * ((1 / 2 : ℂ) • (a + ε • b)) = 0 := by
  have key : ((1 / 2 : ℂ) • (a + ε • b)) * ((1 / 2 : ℂ) • (c + (-ε) • d)) - ((1 / 2 : ℂ) • (c + (-ε) • d)) * ((1 / 2 : ℂ) • (a + ε • b)) =
      (1 / 4 : ℂ) • ((a * c - c * a) - ε • (a * d - d * a) + ε • (b * c - c * b) - (ε * ε) • (b * d - d * b)) := by
    simp only [smul_mul_assoc, mul_smul_comm, mul_add, add_mul, smul_smul, smul_add, smul_sub]
    module
  rw [key, h1, h2, h3, h4, hε]
  module

variable {D : Mat n →+ A}

private theorem four (hb : ∀ X Y, D X * D Y - D Y * D X = D (X * Y - Y * X)) (X Y : Mat n) :
    D X * D Y - D Y * D X = D (X * Y - Y * X) ∧
    D X * D (Complex.I • Y) - D (Complex.I • Y) * D X = D (Complex.I • (X * Y - Y * X)) ∧
    D (Complex.I • X) * D Y - D Y * D (Complex.I • X) = D (Complex.I • (X * Y - Y * X)) ∧
    D (Complex.I • X) * D (Complex.I • Y) - D (Complex.I • Y) * D (Complex.I • X) = - D (X * Y - Y * X) := by
  refine ⟨hb _ _, ?_, ?_, ?_⟩
  · rw [hb]; congr 1; simp [smul_sub]
  · rw [hb]; congr 1; simp [smul_sub]
  · rw [hb, ← map_neg]; congr 1
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_mul_I, smul_sub]
    simp only [neg_smul, one_smul]
    abel

theorem TX_bracket (hb : ∀ X Y, D X * D Y - D Y * D X = D (X * Y - Y * X)) (s : Bool) (X Y : Mat n) :
    TX D s X * TX D s Y - TX D s Y * TX D s X = TX D s (X * Y - Y * X) := by
  obtain ⟨h1, h2, h3, h4⟩ := four hb X Y
  exact quad (eps s) (eps_mul_self s) _ _ _ _ _ _ h1 h2 h3 h4

theorem TX_cross (hb : ∀ X Y, D X * D Y - D Y * D X = D (X * Y - Y * X)) (s : Bool) (X Y : Mat n) :
    Commute (TX D s X) (TX D (!s) Y) := by
  obtain ⟨h1, h2, h3, h4⟩ := four hb X Y
  have := quad' (eps s) (eps_mul_self s) _ _ _ _ _ _ h1 h2 h3 h4
  rw [← eps_mul_not] at this
  exact sub_eq_zero.mp this

theorem Tc_bracket (hb : ∀ X Y, D X * D Y - D Y * D X = D (X * Y - Y * X)) (s : Bool) (a b c d : Fin n) :
    Tc D s a b * Tc D s c d - Tc D s c d * Tc D s a b =
      (if b = c then Tc D s a d else 0) - (if d = a then Tc D s c b else 0) := by
  have z : TX D s (0 : Mat n) = 0 := by simp [TX]
  simp only [Tc]
  rw [TX_bracket hb, TX_sub]
  congr 1
  · by_cases h : b = c
    · subst h; simp
    · simp [h, Matrix.single_mul_single_of_ne, z]
  · by_cases h : d = a
    · subst h; simp
    · simp [h, Matrix.single_mul_single_of_ne, z]

def cs (s : Bool) : ℂ →+* ℂ := if s then RingHom.id ℂ else starRingEnd ℂ

theorem D_single (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X) (a b : Fin n) (z : ℂ) :
    D (Matrix.single a b z) = z • Tc D true a b + conj z • Tc D false a b := by
  have e : Matrix.single a b z = (z.re : ℂ) • (Matrix.single a b 1 : Mat n) +
      (z.im : ℂ) • (Complex.I • (Matrix.single a b 1 : Mat n)) := by
    rw [Matrix.smul_single, Matrix.smul_single, Matrix.smul_single, ← Matrix.single_add]
    congr 1
    apply Complex.ext <;> simp
  rw [e, map_add, hs, hs]
  simp only [Tc, TX, eps, if_true, Bool.false_eq_true, if_false]
  have hz : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := (Complex.re_add_im z).symm
  have hc : conj z = (z.re : ℂ) - (z.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [hc]
  nth_rewrite 3 [hz]
  generalize D (Matrix.single a b 1) = P
  generalize D (Complex.I • Matrix.single a b 1) = Q
  generalize (z.re : ℂ) = x
  generalize (z.im : ℂ) = y
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  match_scalars <;> first | ring1 | linear_combination y * hI

theorem D_expand (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X) (X : Mat n) :
    D X = ∑ a, ∑ b, (X a b • Tc D true a b + conj (X a b) • Tc D false a b) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum, D_single hs]

theorem TX_expand (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X) (s : Bool) (X : Mat n) :
    TX D s X = ∑ a, ∑ b, cs s (X a b) • Tc D s a b := by
  simp only [TX]
  rw [D_expand hs X, D_expand hs (Complex.I • X)]
  simp only [Finset.smul_sum, ← Finset.sum_add_distrib, Matrix.smul_apply, smul_eq_mul, map_mul, Complex.conj_I]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  generalize X a b = z
  cases s
  · simp only [eps, cs, Bool.false_eq_true, if_false]
    generalize conj z = w
    match_scalars <;> first | linear_combination (z / 2) * hI | linear_combination (-w / 2) * hI
  · simp only [eps, cs, if_true, RingHom.id_apply]
    generalize conj z = w
    match_scalars <;> first | linear_combination (-z / 2) * hI | linear_combination (w / 2) * hI

end Lie

section Inv

variable {A : Type*} [Ring A] [Algebra ℂ A] {D : Mat n →+ A}

theorem D_commute_trPw (hb : ∀ X Y, D X * D Y - D Y * D X = D (X * Y - Y * X))
    (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X) (s : Bool) (m : ℕ) (X : Mat n) :
    Commute (D X) (∑ c, Pw (Tc D s) m c c) := by
  have h1 : ∀ a b, Commute (Tc D s a b) (∑ c, Pw (Tc D s) m c c) := fun a b => trPw_central (Tc_bracket hb s) m a b
  have h2 : ∀ a b, Commute (Tc D (!s) a b) (∑ c, Pw (Tc D s) m c c) := fun a b =>
    Commute.sum_right _ _ _ fun c _ => Pw_commute (fun a' b' => (TX_cross hb s _ _).symm) m c c
  have h3 : ∀ t a b, Commute (Tc D t a b) (∑ c, Pw (Tc D s) m c c) := by
    intro t a b
    by_cases h : t = s
    · subst h; exact h1 a b
    · have : t = !s := by cases t <;> cases s <;> simp_all
      subst this; exact h2 a b
  rw [D_expand hs X]
  refine Commute.sum_left _ _ _ fun a _ => Commute.sum_left _ _ _ fun b _ => Commute.add_left ?_ ?_
  · exact (h3 true a b).smul_left _
  · exact (h3 false a b).smul_left _

theorem pow_conj {R : Type*} [Ring R] {T r S S' : R} (h : T * r = r * (S * T * S')) (h1 : S' * S = 1) (h2 : S * S' = 1)
    (m : ℕ) : T ^ m * r = r * (S * T ^ m * S') := by
  induction m with
  | zero => simp [h2]
  | succ m ih =>
    calc T ^ (m + 1) * r = T * (T ^ m * r) := by rw [pow_succ', mul_assoc]
      _ = (T * r) * (S * T ^ m * S') := by rw [ih]; exact (mul_assoc _ _ _).symm
      _ = r * (S * T * (S' * S) * T ^ m * S') := by rw [h]; simp only [mul_assoc]
      _ = r * (S * T ^ (m + 1) * S') := by rw [h1, pow_succ']; simp only [mul_assoc, mul_one]

theorem trace_conj (S S' : Matrix (Fin n) (Fin n) ℂ) (h : S' * S = 1) (M : Matrix (Fin n) (Fin n) A) :
    ∑ a, ((S.map (algebraMap ℂ A)) * M * (S'.map (algebraMap ℂ A))) a a = ∑ a, M a a := by
  have e : ∀ a, ((S.map (algebraMap ℂ A)) * M * (S'.map (algebraMap ℂ A))) a a =
      ∑ c, ∑ d, (S' d a * S a c) • M c d := by
    intro a
    simp only [Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [mul_assoc, ← Algebra.commutes, ← mul_assoc, ← map_mul, ← Algebra.smul_def, mul_comm]
  simp only [e]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  have : ∀ d, ∑ a, S' d a * S a c = if d = c then 1 else 0 := by
    intro d
    have := congrFun (congrFun h d) c
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  simp [this]

theorem conj_single_apply (y x : Mat n) (a b c d : Fin n) : (y * Matrix.single a b (1 : ℂ) * x) c d = y c a * x b d := by
  have e : ∀ i, (∑ j, if a = j ∧ b = i then y c j else 0) = if b = i then y c a else 0 := by
    intro i
    by_cases h : b = i <;> simp [h]
  simp [Matrix.mul_apply, Matrix.single, Finset.sum_ite_eq, e]

theorem trPw_conj (hs : ∀ (r : ℝ) X, D ((r : ℂ) • X) = (r : ℂ) • D X) (s : Bool) (m : ℕ) {ρ : A} {y x : Mat n}
    (hyx : y * x = 1) (hρ : ∀ X, D X * ρ = ρ * D (y * X * x)) :
    (∑ c, Pw (Tc D s) m c c) * ρ = ρ * ∑ c, Pw (Tc D s) m c c := by
  have hxy : x * y = 1 := mul_eq_one_comm.mp hyx
  have hT : ∀ X, TX D s X * ρ = ρ * TX D s (y * X * x) := by
    intro X
    have e : y * (Complex.I • X) * x = Complex.I • (y * X * x) := by simp [Matrix.mul_smul, Matrix.smul_mul]
    simp only [TX, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, hρ, e]
  set S₀ : Matrix (Fin n) (Fin n) ℂ := ((cs s).mapMatrix y)ᵀ with hS₀
  set S₁ : Matrix (Fin n) (Fin n) ℂ := ((cs s).mapMatrix x)ᵀ with hS₁
  have h10 : S₁ * S₀ = 1 := by
    rw [hS₀, hS₁, ← Matrix.transpose_mul, ← map_mul, hyx]; simp
  have h01 : S₀ * S₁ = 1 := by
    rw [hS₀, hS₁, ← Matrix.transpose_mul, ← map_mul, hxy]; simp
  set S := S₀.map (algebraMap ℂ A) with hS
  set S' := S₁.map (algebraMap ℂ A) with hS'
  have g10 : S' * S = 1 := by
    have := congrArg (algebraMap ℂ A).mapMatrix h10
    simpa [map_mul] using this
  have g01 : S * S' = 1 := by
    have := congrArg (algebraMap ℂ A).mapMatrix h01
    simpa [map_mul] using this
  set r : Matrix (Fin n) (Fin n) A := Matrix.diagonal fun _ => ρ with hr
  have hmain : Matrix.of (Tc D s) * r = r * (S * Matrix.of (Tc D s) * S') := by
    ext a b
    rw [hr, Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.of_apply]
    rw [Tc, hT, TX_expand hs]
    congr 1
    simp only [conj_single_apply]
    simp only [Matrix.mul_apply, Finset.sum_mul, hS, hS', Matrix.map_apply, Matrix.of_apply, hS₀, hS₁,
      Matrix.transpose_apply, RingHom.mapMatrix_apply, map_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    symm
    rw [mul_assoc, ← Algebra.commutes, ← mul_assoc, ← map_mul, ← Algebra.smul_def]
  have hp := pow_conj hmain g10 g01 m
  have ht := trace_conj S₀ S₁ h10 (Matrix.of (Tc D s) ^ m)
  calc (∑ c, Pw (Tc D s) m c c) * ρ = ∑ a, ((Matrix.of (Tc D s)) ^ m * r) a a := by
        simp [Finset.sum_mul, hr, Matrix.mul_diagonal, Pw_eq_pow]
    _ = ∑ a, (r * (S * Matrix.of (Tc D s) ^ m * S')) a a := by rw [hp]
    _ = ρ * ∑ a, (S * Matrix.of (Tc D s) ^ m * S') a a := by
        simp [Finset.mul_sum, hr, Matrix.diagonal_mul]
    _ = ρ * ∑ c, Pw (Tc D s) m c c := by rw [ht]; simp [Pw_eq_pow]

end Inv

end GlobalTheory.CompanionTheory.RCalc
