import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableAtOfSmooth

noncomputable section

open Matrix Finset
open scoped ContDiff ComplexConjugate

namespace GlobalTheory.CompanionTheory.GelC

open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.RCalc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

section Alg

variable {A : Type*} [Ring A] [Algebra ℂ A]

theorem pow_bracket (e : Matrix (Fin n) (Fin n) A)
    (he : ∀ a b c d, e a b * e c d - e c d * e a b = (if b = c then e a d else 0) - (if a = d then e c b else 0)) (m : ℕ) :
    ∀ a b c d, e a b * (e ^ m) c d - (e ^ m) c d * e a b =
      (if b = c then (e ^ m) a d else 0) - (if a = d then (e ^ m) c b else 0) := by
  induction m with
  | zero =>
    intro a b c d
    have hcb : (c = b) ↔ (b = c) := eq_comm
    simp only [pow_zero, one_apply, hcb]
    by_cases h1 : c = d <;> by_cases h2 : b = c <;> by_cases h3 : a = d <;> simp_all
  | succ m ih =>
    intro a b c d
    have hp : ∀ i j, (e ^ (m + 1)) i j = ∑ x, e i x * (e ^ m) x j := fun i j => by rw [pow_succ', mul_apply]
    have key : ∀ x, e a b * (e c x * (e ^ m) x d) - (e c x * (e ^ m) x d) * e a b =
        (if b = c then e a x * (e ^ m) x d else 0) - (if a = x then e c b * (e ^ m) x d else 0) +
          (if b = x then e c x * (e ^ m) a d else 0) - (if a = d then e c x * (e ^ m) x b else 0) := by
      intro x
      have e1 : e a b * (e c x * (e ^ m) x d) - (e c x * (e ^ m) x d) * e a b =
          (e a b * e c x - e c x * e a b) * (e ^ m) x d + e c x * (e a b * (e ^ m) x d - (e ^ m) x d * e a b) := by
        noncomm_ring
      rw [e1, he a b c x, ih a b x d, sub_mul, mul_sub, ite_mul, ite_mul, mul_ite, mul_ite, zero_mul, mul_zero]
      abel
    rw [hp c d, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_congr rfl fun x _ => key x]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    by_cases h2 : b = c <;> by_cases h3 : a = d <;> simp [h2, h3, hp]

theorem pow_central (e : Matrix (Fin n) (Fin n) A)
    (he : ∀ a b c d, e a b * e c d - e c d * e a b = (if b = c then e a d else 0) - (if a = d then e c b else 0))
    (m : ℕ) (a b : Fin n) : e a b * (e ^ m).trace = (e ^ m).trace * e a b := by
  rw [← sub_eq_zero]
  simp only [Matrix.trace, Matrix.diag, Finset.mul_sum, Finset.sum_mul]
  rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl fun c _ => pow_bracket e he m a b c c]
  simp [Finset.sum_sub_distrib]

theorem trace_cent (N : Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin n) A) :
    (N.map (algebraMap ℂ A) * Y).trace = (Y * N.map (algebraMap ℂ A)).trace := by
  simp only [Matrix.trace, Matrix.diag, mul_apply, map_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => Algebra.commutes _ _

theorem trace_conj (e : Matrix (Fin n) (Fin n) A) (r : A) (N M : Matrix (Fin n) (Fin n) ℂ) (hNM : N * M = 1) (hMN : M * N = 1)
    (h : ∀ p b, ∑ a, N p a • (e a b * r) = ∑ d, N d b • (r * e p d)) (m : ℕ) :
    r * (e ^ m).trace = (e ^ m).trace * r := by
  set φ : Matrix (Fin n) (Fin n) ℂ →+* Matrix (Fin n) (Fin n) A := (algebraMap ℂ A).mapMatrix with hφ
  have hφa : ∀ X, φ X = X.map (algebraMap ℂ A) := fun X => rfl
  set Rm : Matrix (Fin n) (Fin n) A := Matrix.diagonal fun _ => r with hRm
  have hNm : φ N * φ M = 1 := by rw [← map_mul, hNM, map_one]
  have hMn : φ M * φ N = 1 := by rw [← map_mul, hMN, map_one]
  have hcomm : ∀ X, Rm * φ X = φ X * Rm := by
    intro X
    ext i j
    simp [hRm, hφa, Matrix.diagonal_mul, Matrix.mul_diagonal, Algebra.commutes]
  have hrel : φ N * e * Rm = Rm * e * φ N := by
    ext p b
    have h0 := h p b
    simp only [Algebra.smul_def] at h0
    rw [hRm, Matrix.mul_diagonal, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_mul]
    simp only [Matrix.diagonal_mul, hφa, map_apply]
    rw [Finset.sum_congr rfl fun x _ => mul_assoc _ _ _, h0]
    exact Finset.sum_congr rfl fun d _ => Algebra.commutes _ _
  have h1 : Rm * e = φ N * e * φ M * Rm := by
    calc Rm * e = Rm * e * (φ N * φ M) := by rw [hNm, mul_one]
      _ = (Rm * e * φ N) * φ M := by rw [mul_assoc (Rm * e)]
      _ = φ N * e * Rm * φ M := by rw [hrel]
      _ = φ N * e * φ M * Rm := by
          rw [mul_assoc _ Rm, hcomm]
          simp only [mul_assoc]
  have hS : Commute (φ M * Rm) e := by
    show φ M * Rm * e = e * (φ M * Rm)
    rw [mul_assoc, h1]
    simp only [← mul_assoc]
    rw [hMn, one_mul]
  have hSm : φ M * Rm * e ^ m = e ^ m * (φ M * Rm) := hS.pow_right m
  have h2 : Rm * e ^ m = φ N * e ^ m * φ M * Rm := by
    calc Rm * e ^ m = φ N * (φ M * Rm * e ^ m) := by
          simp only [← mul_assoc]
          rw [hNm, one_mul]
      _ = φ N * (e ^ m * (φ M * Rm)) := by rw [hSm]
      _ = _ := by simp only [mul_assoc]
  have t1 : (Rm * e ^ m).trace = r * (e ^ m).trace := by
    simp [Matrix.trace, hRm, Matrix.diagonal_mul, Finset.mul_sum]
  have t2 : ∀ X : Matrix (Fin n) (Fin n) A, (X * Rm).trace = X.trace * r := by
    intro X
    simp [Matrix.trace, hRm, Matrix.mul_diagonal, Finset.sum_mul]
  have t3 : (φ N * e ^ m * φ M).trace = (e ^ m).trace := by
    rw [mul_assoc, hφa N, trace_cent, ← hφa, mul_assoc, hMn, mul_one]
  rw [← t1, h2, t2, t3]

theorem T_alg (p q u v t w : A) (ε ε' : ℂ) (h1 : p * u - u * p = t) (h2 : p * v - v * p = w)
    (h3 : q * u - u * q = w) (h4 : q * v - v * q = -t) :
    ((1 / 2 : ℂ) • (p + ε • q)) * ((1 / 2 : ℂ) • (u + ε' • v)) - ((1 / 2 : ℂ) • (u + ε' • v)) * ((1 / 2 : ℂ) • (p + ε • q)) =
      (1 / 4 : ℂ) • (t + (ε + ε') • w - (ε * ε') • t) := by
  have e : ((1 / 2 : ℂ) • (p + ε • q)) * ((1 / 2 : ℂ) • (u + ε' • v)) -
      ((1 / 2 : ℂ) • (u + ε' • v)) * ((1 / 2 : ℂ) • (p + ε • q)) =
      (1 / 4 : ℂ) • ((p * u - u * p) + ε' • (p * v - v * p) + ε • (q * u - u * q) + (ε * ε') • (q * v - v * q)) := by
    simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, smul_add, smul_sub, smul_smul]
    module
  rw [e, h1, h2, h3, h4]
  module

end Alg

section End

variable {M M' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']

theorem pow_intertw (e : Matrix (Fin n) (Fin n) (Module.End ℂ M)) (e' : Matrix (Fin n) (Fin n) (Module.End ℂ M'))
    (α : M →ₗ[ℂ] M') (h : ∀ a b x, α (e a b x) = e' a b (α x)) (m : ℕ) :
    ∀ a b x, α ((e ^ m) a b x) = (e' ^ m) a b (α x) := by
  induction m with
  | zero =>
    intro a b x
    simp only [pow_zero, one_apply]
    split_ifs <;> simp
  | succ m ih =>
    intro a b x
    simp only [pow_succ', mul_apply, LinearMap.sum_apply, map_sum, Module.End.mul_apply]
    exact Finset.sum_congr rfl fun c _ => by rw [h, ih]

theorem trace_intertw (e : Matrix (Fin n) (Fin n) (Module.End ℂ M)) (e' : Matrix (Fin n) (Fin n) (Module.End ℂ M'))
    (α : M →ₗ[ℂ] M') (h : ∀ a b x, α (e a b x) = e' a b (α x)) (m : ℕ) (x : M) :
    α ((e ^ m).trace x) = (e' ^ m).trace (α x) := by
  simp only [Matrix.trace, Matrix.diag, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun a _ => pow_intertw e e' α h m a a x

end End

section Sm

variable {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V'] [NormedSpace ℂ V']

variable (n V) in

def Sm : Submodule ℂ (Mat n → V) where
  carrier := {f | ContDiffOn ℝ ∞ f (GLs n) ∧ ∀ g, g ∉ GLs n → f g = 0}
  add_mem' := fun {f h} hf hh => ⟨hf.1.add hh.1, fun g hg => by simp [hf.2 g hg, hh.2 g hg]⟩
  zero_mem' := ⟨contDiffOn_const (c := (0 : V)), fun _ _ => rfl⟩
  smul_mem' := fun c f hf => ⟨hf.1.const_smul c, fun g hg => by simp [hf.2 g hg]⟩

theorem Sm.sm (x : Sm n V) : ContDiffOn ℝ ∞ x.1 (GLs n) := x.2.1

theorem Sm.ext' {x y : Sm n V} (h : ∀ g ∈ GLs n, x.1 g = y.1 g) : x = y := by
  apply Subtype.ext
  funext g
  by_cases hg : g ∈ GLs n
  · exact h g hg
  · rw [x.2.2 g hg, y.2.2 g hg]

def cut (F : Mat n → V) (hF : ContDiffOn ℝ ∞ F (GLs n)) : Sm n V :=
  ⟨(GLs n).indicator F, hF.congr (fun g hg => Set.indicator_of_mem hg F), fun g hg => Set.indicator_of_notMem hg F⟩

theorem cut_apply {F : Mat n → V} (hF : ContDiffOn ℝ ∞ F (GLs n)) {g : Mat n} (hg : g ∈ GLs n) : (cut F hF).1 g = F g :=
  Set.indicator_of_mem hg F

def lift (D : (Mat n → V) → (Mat n → V')) (hs : ∀ f, ContDiffOn ℝ ∞ f (GLs n) → ContDiffOn ℝ ∞ (D f) (GLs n))
    (ha : ∀ f f', ContDiffOn ℝ ∞ f (GLs n) → ContDiffOn ℝ ∞ f' (GLs n) → Set.EqOn (D (f + f')) (D f + D f') (GLs n))
    (hc : ∀ (c : ℂ) f, ContDiffOn ℝ ∞ f (GLs n) → Set.EqOn (D (c • f)) (c • D f) (GLs n)) : Sm n V →ₗ[ℂ] Sm n V' where
  toFun x := cut (D x.1) (hs _ (Sm.sm x))
  map_add' x y := Sm.ext' fun g hg => by
    have e : ∀ z : Sm n V, (cut (D z.1) (hs _ (Sm.sm z))).1 g = D z.1 g := fun z => cut_apply _ hg
    show (cut (D (x + y).1) _).1 g = (cut (D x.1) _).1 g + (cut (D y.1) _).1 g
    rw [e, e, e]
    exact ha _ _ (Sm.sm x) (Sm.sm y) hg
  map_smul' c x := Sm.ext' fun g hg => by
    have e : ∀ z : Sm n V, (cut (D z.1) (hs _ (Sm.sm z))).1 g = D z.1 g := fun z => cut_apply _ hg
    show (cut (D (c • x).1) _).1 g = c • (cut (D x.1) _).1 g
    rw [e, e]
    exact hc c _ (Sm.sm x) hg

theorem lift_val (D : (Mat n → V) → (Mat n → V')) (hs ha hc) (x : Sm n V) {g : Mat n} (hg : g ∈ GLs n) :
    (lift D hs ha hc x).1 g = D x.1 g := cut_apply (hs _ (Sm.sm x)) hg

def rd (X : Mat n) : Module.End ℂ (Sm n V) :=
  lift (Rd X) (fun _ hf => Rd_contDiffOn X hf) (fun _ _ hf hf' => Rd_add X hf hf') (fun c _ hf => Rd_smul c X hf)

theorem rd_val (X : Mat n) (x : Sm n V) {g : Mat n} (hg : g ∈ GLs n) : (rd X x).1 g = Rd X x.1 g := lift_val _ _ _ _ x hg

theorem rd_rd (X Y : Mat n) (x : Sm n V) {g : Mat n} (hg : g ∈ GLs n) : (rd X (rd Y x)).1 g = Rd X (Rd Y x.1) g := by
  rw [rd_val X _ hg]
  exact Rd_congr X (fun g' hg' => rd_val Y x hg') hg

theorem rd_add (X Y : Mat n) : (rd (X + Y) : Module.End ℂ (Sm n V)) = rd X + rd Y := by
  refine LinearMap.ext fun x => Sm.ext' fun g hg => ?_
  simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, rd_val _ _ hg, Rd_add_left]

theorem rd_rsmul (r : ℝ) (X : Mat n) : (rd (r • X) : Module.End ℂ (Sm n V)) = (r : ℂ) • rd X := by
  refine LinearMap.ext fun x => Sm.ext' fun g hg => ?_
  show (rd (r • X) x).1 g = (r : ℂ) • (rd X x).1 g
  rw [rd_val _ _ hg, rd_val _ _ hg, Rd_smul_left, Pi.smul_apply, Complex.coe_smul]

theorem rd_neg (X : Mat n) : (rd (-X) : Module.End ℂ (Sm n V)) = -rd X := by
  have := rd_rsmul (V := V) (-1) X
  simpa using this

theorem rd_bracket (X Y : Mat n) :
    (rd X * rd Y - rd Y * rd X : Module.End ℂ (Sm n V)) = rd (X * Y - Y * X) := by
  refine LinearMap.ext fun x => Sm.ext' fun g hg => ?_
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply, rd_rd _ _ _ hg, rd_val _ _ hg]
  exact Rd_bracket X Y (Sm.sm x) hg

def eps (s : Bool) : ℂ := if s then -Complex.I else Complex.I

theorem eps_sq (s : Bool) : eps s * eps s = -1 := by cases s <;> simp [eps]

def T (s : Bool) (Z : Mat n) : Module.End ℂ (Sm n V) := (1 / 2 : ℂ) • (rd Z + eps s • rd (Complex.I • Z))

def kap : Bool → ℂ →+* ℂ
  | true => RingHom.id ℂ
  | false => starRingEnd ℂ

theorem kap_eq (s : Bool) (c : ℂ) : kap s c = (c.re : ℂ) + (c.im : ℂ) * (-eps s) := by
  cases s
  · simp only [kap, eps]
    apply Complex.ext <;> simp
  · simp only [kap, eps]
    apply Complex.ext <;> simp

theorem T_add (s : Bool) (Z W : Mat n) : (T s (Z + W) : Module.End ℂ (Sm n V)) = T s Z + T s W := by
  simp only [T, smul_add, rd_add]
  module

theorem T_rsmul (s : Bool) (r : ℝ) (Z : Mat n) : (T s (r • Z) : Module.End ℂ (Sm n V)) = (r : ℂ) • T s Z := by
  simp only [T]
  rw [smul_comm Complex.I r Z, rd_rsmul, rd_rsmul]
  module

theorem T_I (s : Bool) (Z : Mat n) : (T s (Complex.I • Z) : Module.End ℂ (Sm n V)) = (-eps s) • T s Z := by
  have h : Complex.I • Complex.I • Z = -Z := by simp [smul_smul]
  simp only [T, h, rd_neg]
  have e : (-eps s) • ((1 / 2 : ℂ) • ((rd Z : Module.End ℂ (Sm n V)) + eps s • rd (Complex.I • Z))) =
      (1 / 2 : ℂ) • ((-eps s) • rd Z + (-(eps s * eps s)) • rd (Complex.I • Z)) := by module
  rw [e, eps_sq]
  module

theorem T_smul (s : Bool) (c : ℂ) (Z : Mat n) : (T s (c • Z) : Module.End ℂ (Sm n V)) = kap s c • T s Z := by
  have hZ : c • Z = c.re • Z + c.im • (Complex.I • Z) := by
    conv_lhs => rw [← Complex.re_add_im c]
    rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
  rw [hZ, T_add, T_rsmul, T_rsmul, T_I, kap_eq]
  module

theorem T_sum (s : Bool) {ι : Type*} (t : Finset ι) (c : ι → ℂ) (Z : ι → Mat n) :
    (T s (∑ i ∈ t, c i • Z i) : Module.End ℂ (Sm n V)) = ∑ i ∈ t, kap s (c i) • T s (Z i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have := T_smul (V := V) (n := n) s 0 0
    simpa using this
  | insert i t hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, T_add, T_smul, ih]

theorem T_sub (s : Bool) (Z W : Mat n) : (T s (Z - W) : Module.End ℂ (Sm n V)) = T s Z - T s W := by
  have := T_smul (V := V) s (-1) W
  rw [sub_eq_add_neg, T_add, sub_eq_add_neg]
  simpa using congrArg (T s Z + ·) this

theorem right_derivative_commutator (Z W : Mat n) :
    (rd Z * rd (Complex.I • W) - rd (Complex.I • W) * rd Z : Module.End ℂ (Sm n V)) = rd (Complex.I • (Z * W - W * Z)) ∧
    (rd (Complex.I • Z) * rd W - rd W * rd (Complex.I • Z) : Module.End ℂ (Sm n V)) = rd (Complex.I • (Z * W - W * Z)) ∧
    (rd (Complex.I • Z) * rd (Complex.I • W) - rd (Complex.I • W) * rd (Complex.I • Z) : Module.End ℂ (Sm n V)) =
      -rd (Z * W - W * Z) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [rd_bracket]
    simp only [mul_smul_comm, smul_mul_assoc, smul_sub]
  · rw [rd_bracket]
    simp only [mul_smul_comm, smul_mul_assoc, smul_sub]
  · rw [rd_bracket, ← rd_neg]
    congr 1
    simp only [mul_smul_comm, smul_mul_assoc, smul_smul, Complex.I_mul_I]
    simp
    abel

theorem T_bracket (s : Bool) (Z W : Mat n) :
    (T s Z * T s W - T s W * T s Z : Module.End ℂ (Sm n V)) = T s (Z * W - W * Z) := by
  obtain ⟨h2, h3, h4⟩ := right_derivative_commutator (V := V) Z W
  simp only [T]
  rw [T_alg _ _ _ _ _ _ _ _ (rd_bracket Z W) h2 h3 h4, eps_sq]
  module

theorem T_cross (s : Bool) (Z W : Mat n) :
    (T s Z * T (!s) W : Module.End ℂ (Sm n V)) = T (!s) W * T s Z := by
  obtain ⟨h2, h3, h4⟩ := right_derivative_commutator (V := V) Z W
  rw [← sub_eq_zero]
  simp only [T]
  rw [T_alg _ _ _ _ _ _ _ _ (rd_bracket Z W) h2 h3 h4]
  have e1 : eps s + eps (!s) = 0 := by cases s <;> simp [eps]
  have e2 : eps s * eps (!s) = 1 := by cases s <;> simp [eps]
  rw [e1, e2]
  simp

theorem rd_split (s : Bool) (X : Mat n) : (rd X : Module.End ℂ (Sm n V)) = T s X + T (!s) X := by
  have e1 : eps (!s) = -eps s := by cases s <;> simp [eps]
  simp only [T, e1]
  module

def eM (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (n : ℕ) (s : Bool) : Matrix (Fin n) (Fin n) (Module.End ℂ (Sm n V)) :=
  Matrix.of fun a b => T s (Matrix.single a b 1)

theorem eM_apply (s : Bool) (a b : Fin n) : eM V n s a b = T s (Matrix.single a b 1) := rfl

theorem eM_rel (s : Bool) (a b c d : Fin n) :
    eM V n s a b * eM V n s c d - eM V n s c d * eM V n s a b =
      (if b = c then eM V n s a d else 0) - (if a = d then eM V n s c b else 0) := by
  have T0 : (T s (0 : Mat n) : Module.End ℂ (Sm n V)) = 0 := by
    have := T_smul (V := V) (n := n) s 0 0
    simpa using this
  simp only [eM_apply, T_bracket]
  rw [T_sub]
  congr 1
  · by_cases h : b = c
    · subst h
      simp [Matrix.single_mul_single_same]
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ h]
      simp [h, T0]
  · by_cases h : a = d
    · subst h
      simp [Matrix.single_mul_single_same]
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm h)]
      simp [h, T0]

theorem Eu_val (s : Bool) (a b : Fin n) (x : Sm n V) {g : Mat n} (hg : g ∈ GLs n) :
    (eM V n s a b x).1 g = Eu s a b x.1 g := by
  have h : Complex.I • (Matrix.single a b 1 : Mat n) = Matrix.single a b Complex.I := by
    rw [Matrix.smul_single]; simp
  simp only [eM_apply, T, h, LinearMap.smul_apply, LinearMap.add_apply, Submodule.coe_smul, Submodule.coe_add,
    Pi.smul_apply, Pi.add_apply, rd_val _ _ hg, Eu, eps]

theorem Eu_congr' (s : Bool) (a b : Fin n) {f f' : Mat n → V} (h : Set.EqOn f f' (GLs n)) :
    Set.EqOn (Eu s a b f) (Eu s a b f') (GLs n) := by
  intro x hx
  simp only [Eu, Pi.smul_apply, Pi.add_apply, Rd_congr _ h hx]

theorem Epow_val (s : Bool) {F : Mat n → V} (x : Sm n V) (hx : Set.EqOn F x.1 (GLs n)) (m : ℕ) :
    ∀ a b, Set.EqOn (Epow s m a b F) (((eM V n s) ^ m) a b x).1 (GLs n) := by
  induction m with
  | zero =>
    intro a b g hg
    simp only [pow_zero, one_apply, Epow]
    by_cases h : a = b
    · simpa [h] using hx hg
    · simp [h]
  | succ m ih =>
    intro a b g hg
    simp only [Epow, pow_succ', mul_apply, LinearMap.sum_apply, Module.End.mul_apply, Finset.sum_apply,
      AddSubmonoidClass.coe_finset_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Eu_congr' s a c (ih c b) hg, Eu_val s a c _ hg]

def tr (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (n : ℕ) (s : Bool) (m : ℕ) : Module.End ℂ (Sm n V) :=
  ((eM V n s) ^ m).trace

theorem gel_val (s : Bool) {F : Mat n → V} (x : Sm n V) (hx : Set.EqOn F x.1 (GLs n)) (m : ℕ) :
    Set.EqOn (gel s m F) (tr V n s m x).1 (GLs n) := by
  intro g hg
  simp only [gel, tr, Matrix.trace, Matrix.diag, LinearMap.sum_apply, Finset.sum_apply, AddSubmonoidClass.coe_finset_sum]
  exact Finset.sum_congr rfl fun a _ => Epow_val s x hx m a a hg

end Sm

section Main

variable {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V'] [NormedSpace ℂ V']

theorem mul_mem {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at *
  exact mul_ne_zero hx hy

theorem rtr_smooth (h : Mat n) (hh : h ∈ GLs n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (fun y => f (y * h)) (GLs n) :=
  hf.comp (mulR h).contDiff.contDiffOn fun _ hy => mul_mem hy hh

theorem ltr_smooth (h : Mat n) (hh : h ∈ GLs n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (fun y => f (h * y)) (GLs n) :=
  hf.comp (mulL h).contDiff.contDiffOn fun _ hy => mul_mem hh hy

def rtr (h : Mat n) (hh : h ∈ GLs n) : Module.End ℂ (Sm n V) :=
  lift (fun f y => f (y * h)) (fun _ hf => rtr_smooth h hh hf) (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)

def ltr (h : Mat n) (hh : h ∈ GLs n) : Module.End ℂ (Sm n V) :=
  lift (fun f y => f (h * y)) (fun _ hf => ltr_smooth h hh hf) (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)

def cmap (A : V →L[ℂ] V') : Sm n V →ₗ[ℂ] Sm n V' :=
  lift (fun f y => A (f y))
    (fun _ hf => (A.restrictScalars ℝ).contDiff.comp_contDiffOn hf)
    (fun _ _ _ _ _ _ => by simp) (fun _ _ _ _ _ => by simp)

theorem Rd_right (X h : Mat n) (hh : h ∈ GLs n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n}
    (hg : g ∈ GLs n) : Rd X (fun y => f (y * h)) g = Rd (h⁻¹ * X * h) f (g * h) := by
  have h1 := ((differentiableAt_of_smooth hf (mul_mem hg hh)).hasFDerivAt.comp g (mulR h).hasFDerivAt).fderiv
  have hu : IsUnit h.det := isUnit_iff_ne_zero.2 hh
  have e : g * h * (h⁻¹ * X * h) = g * X * h := by
    simp only [← mul_assoc]
    rw [mul_assoc g h, Matrix.mul_nonsing_inv _ hu, mul_one]
  show fderiv ℝ (fun y => f (y * h)) g (g * X) = fderiv ℝ f (g * h) (g * h * (h⁻¹ * X * h))
  rw [e]
  have h2 : fderiv ℝ (fun y => f (y * h)) g = (fderiv ℝ f (g * h)).comp (mulR h) := h1
  rw [h2]
  rfl

theorem Rd_left (X h : Mat n) (hh : h ∈ GLs n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n}
    (hg : g ∈ GLs n) : Rd X (fun y => f (h * y)) g = Rd X f (h * g) := by
  have h1 := ((differentiableAt_of_smooth hf (mul_mem hh hg)).hasFDerivAt.comp g (mulL h).hasFDerivAt).fderiv
  have h2 : fderiv ℝ (fun y => f (h * y)) g = (fderiv ℝ f (h * g)).comp (mulL h) := h1
  show fderiv ℝ (fun y => f (h * y)) g (g * X) = fderiv ℝ f (h * g) (h * g * X)
  rw [h2, mul_assoc]
  rfl

theorem Rd_clm (X : Mat n) (A : V →L[ℂ] V') {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n}
    (hg : g ∈ GLs n) : Rd X (fun y => A (f y)) g = A (Rd X f g) := by
  have h1 := ((A.restrictScalars ℝ).hasFDerivAt.comp g (differentiableAt_of_smooth hf hg).hasFDerivAt).fderiv
  have h2 : fderiv ℝ (fun y => A (f y)) g = (A.restrictScalars ℝ).comp (fderiv ℝ f g) := h1
  show fderiv ℝ (fun y => A (f y)) g (g * X) = A (fderiv ℝ f g (g * X))
  rw [h2]
  rfl

theorem rtr_val (h : Mat n) (hh) (x : Sm n V) {g : Mat n} (hg : g ∈ GLs n) : (rtr h hh x).1 g = x.1 (g * h) :=
  lift_val _ _ _ _ x hg

theorem ltr_val (h : Mat n) (hh) (x : Sm n V) {g : Mat n} (hg : g ∈ GLs n) : (ltr h hh x).1 g = x.1 (h * g) :=
  lift_val _ _ _ _ x hg

theorem cmap_val (A : V →L[ℂ] V') (x : Sm n V) {g : Mat n} (hg : g ∈ GLs n) : (cmap A x).1 g = A (x.1 g) :=
  lift_val _ _ _ _ x hg

theorem rd_rtr (X h : Mat n) (hh : h ∈ GLs n) :
    (rd X * rtr h hh : Module.End ℂ (Sm n V)) = rtr h hh * rd (h⁻¹ * X * h) := by
  refine LinearMap.ext fun x => Sm.ext' fun g hg => ?_
  simp only [Module.End.mul_apply]
  rw [rd_val _ _ hg, rtr_val _ _ _ hg, rd_val _ _ (mul_mem hg hh), ← Rd_right X h hh (Sm.sm x) hg]
  exact Rd_congr X (fun g' hg' => rtr_val h hh x hg') hg

theorem T_rtr (s : Bool) (Z h : Mat n) (hh : h ∈ GLs n) :
    (T s Z * rtr h hh : Module.End ℂ (Sm n V)) = rtr h hh * T s (h⁻¹ * Z * h) := by
  have e : h⁻¹ * (Complex.I • Z) * h = Complex.I • (h⁻¹ * Z * h) := by
    simp only [mul_smul_comm, smul_mul_assoc]
  simp only [T, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, rd_rtr, e]

theorem rd_ltr (X h : Mat n) (hh : h ∈ GLs n) (x : Sm n V) : ltr h hh (rd X x) = rd X (ltr h hh x) := by
  refine Sm.ext' fun g hg => ?_
  rw [ltr_val _ _ _ hg, rd_val _ _ (mul_mem hh hg), rd_val _ _ hg, ← Rd_left X h hh (Sm.sm x) hg]
  exact (Rd_congr X (fun g' hg' => ltr_val h hh x hg') hg).symm

theorem rd_cmap (X : Mat n) (A : V →L[ℂ] V') (x : Sm n V) : cmap A (rd X x) = rd X (cmap A x) := by
  refine Sm.ext' fun g hg => ?_
  rw [cmap_val _ _ hg, rd_val _ _ hg, rd_val _ _ hg, ← Rd_clm X A (Sm.sm x) hg]
  exact (Rd_congr X (fun g' hg' => cmap_val A x hg') hg).symm

theorem T_intertw (α : Sm n V →ₗ[ℂ] Sm n V') (h : ∀ X x, α (rd X x) = rd X (α x)) (s : Bool) (Z : Mat n) (x : Sm n V) :
    α (T s Z x) = T s Z (α x) := by
  simp only [T, LinearMap.smul_apply, LinearMap.add_apply, map_smul, map_add, h]

theorem T_expand (s : Bool) (Z : Mat n) : (T s Z : Module.End ℂ (Sm n V)) =
    ∑ a, ∑ b, kap s (Z a b) • eM V n s a b := by
  have h : Z = ∑ p : Fin n × Fin n, Z p.1 p.2 • (Matrix.single p.1 p.2 1 : Mat n) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.smul_single]
    simp
  conv_lhs => rw [h]
  rw [T_sum, Fintype.sum_prod_type]
  rfl

theorem tr_T_same (s : Bool) (m : ℕ) (Z : Mat n) :
    (T s Z * tr V n s m : Module.End ℂ (Sm n V)) = tr V n s m * T s Z := by
  rw [T_expand]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, tr]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
    rw [pow_central _ (eM_rel s) m a b]

theorem tr_T_other (s : Bool) (m : ℕ) (Z : Mat n) (x : Sm n V) :
    T (!s) Z (tr V n s m x) = tr V n s m (T (!s) Z x) := by
  refine (trace_intertw (eM V n s) (eM V n s) (T (!s) Z) (fun a b y => ?_) m x)
  have := T_cross (V := V) s (Matrix.single a b 1) Z
  exact (LinearMap.congr_fun this y).symm

theorem tr_rd (s : Bool) (m : ℕ) (X : Mat n) (x : Sm n V) : rd X (tr V n s m x) = tr V n s m (rd X x) := by
  rw [rd_split s X, LinearMap.add_apply, LinearMap.add_apply, map_add, tr_T_other]
  congr 1
  exact LinearMap.congr_fun (tr_T_same s m X) x

theorem tr_rtr (s : Bool) (m : ℕ) (h : Mat n) (hh : h ∈ GLs n) (x : Sm n V) :
    rtr h hh (tr V n s m x) = tr V n s m (rtr h hh x) := by
  have hu : IsUnit h.det := isUnit_iff_ne_zero.2 hh
  have hrel : ∀ p b, ∑ a, ((h.map (kap s))ᵀ) p a • (eM V n s a b * rtr h hh) =
      ∑ d, ((h.map (kap s))ᵀ) d b • (rtr h hh * eM V n s p d) := by
    intro p b
    have h1 : h * Matrix.single p b 1 = ∑ a, h a p • (Matrix.single a b 1 : Mat n) := by
      ext i j
      rw [Matrix.sum_apply]
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.single_apply, Matrix.mul_apply]
      by_cases hj : b = j
      · subst hj
        simp
      · simp [hj]
    have h2 : Matrix.single p b 1 * h = ∑ d, h b d • (Matrix.single p d 1 : Mat n) := by
      ext i j
      rw [Matrix.sum_apply]
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.single_apply, Matrix.mul_apply]
      by_cases hi : p = i
      · subst hi
        simp
      · simp [hi]
    have h3 : h⁻¹ * (h * Matrix.single p b 1) * h = Matrix.single p b 1 * h := by
      rw [← mul_assoc, Matrix.nonsing_inv_mul _ hu, one_mul]
    have h4 := T_rtr (V := V) s (h * Matrix.single p b 1) h hh
    rw [h3, h2, T_sum, h1, T_sum, Finset.sum_mul, Finset.mul_sum] at h4
    simpa only [transpose_apply, map_apply, smul_mul_assoc, mul_smul_comm, eM_apply] using h4
  have hNM : (h.map (kap s))ᵀ * (h⁻¹.map (kap s))ᵀ = 1 := by
    rw [← Matrix.transpose_mul]
    have : h⁻¹.map (kap s) * h.map (kap s) = 1 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul, Matrix.nonsing_inv_mul _ hu, map_one]
    rw [this, Matrix.transpose_one]
  have hMN : (h⁻¹.map (kap s))ᵀ * (h.map (kap s))ᵀ = 1 := by
    rw [← Matrix.transpose_mul]
    have : h.map (kap s) * h⁻¹.map (kap s) = 1 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul, Matrix.mul_nonsing_inv _ hu, map_one]
    rw [this, Matrix.transpose_one]
  exact LinearMap.congr_fun (trace_conj (eM V n s) (rtr h hh) _ _ hNM hMN hrel m) x

end Main

theorem gelComm : PositivityTheory.RgBcC.GelComm := by
  intro n V V' _ _ _ _ s m f hf
  set x : Sm n V := cut f hf with hx
  have hxf : Set.EqOn f x.1 (GLs n) := fun g hg => (cut_apply hf hg).symm
  have hgel := gel_val s x hxf m
  refine ⟨(Sm.sm (tr V n s m x)).congr hgel, fun g hg => ⟨fun X => ?_, fun h hh => ⟨?_, ?_⟩, fun A => ?_⟩⟩
  · have h1 : Set.EqOn (Rd X f) (rd X x).1 (GLs n) := fun g' hg' => by
      rw [rd_val _ _ hg']
      exact Rd_congr X hxf hg'
    rw [gel_val s (rd X x) h1 m hg, ← tr_rd, rd_val _ _ hg]
    exact (Rd_congr X hgel hg).symm
  · have h1 : Set.EqOn (fun y => f (h * y)) (ltr h hh x).1 (GLs n) := fun g' hg' => by
      rw [ltr_val _ _ _ hg']
      exact hxf (mul_mem hh hg')
    have h2 : ∀ a b (y : Sm n V), ltr h hh (eM V n s a b y) = eM V n s a b (ltr h hh y) := fun a b y =>
      T_intertw (ltr h hh) (fun X z => rd_ltr X h hh z) s _ y
    rw [gel_val s _ h1 m hg, hgel (mul_mem hh hg)]
    have h3 := trace_intertw (eM V n s) (eM V n s) (ltr h hh) h2 m x
    show (tr V n s m (ltr h hh x)).1 g = _
    rw [show tr V n s m (ltr h hh x) = ltr h hh (tr V n s m x) from h3.symm, ltr_val _ _ _ hg]
  · have h1 : Set.EqOn (fun y => f (y * h)) (rtr h hh x).1 (GLs n) := fun g' hg' => by
      rw [rtr_val _ _ _ hg']
      exact hxf (mul_mem hg' hh)
    rw [gel_val s _ h1 m hg, hgel (mul_mem hg hh), ← tr_rtr, rtr_val _ _ _ hg]
  · have h1 : Set.EqOn (fun y => A (f y)) (cmap A x).1 (GLs n) := fun g' hg' => by
      rw [cmap_val _ _ hg']
      exact congrArg A (hxf hg')
    have h2 : ∀ a b (y : Sm n V), cmap A (eM V n s a b y) = eM V' n s a b (cmap A y) := fun a b y =>
      T_intertw (cmap A) (fun X z => rd_cmap X A z) s _ y
    rw [gel_val s _ h1 m hg, hgel hg]
    have h3 := trace_intertw (eM V n s) (eM V' n s) (cmap A) h2 m x
    show (tr V' n s m (cmap A x)).1 g = _
    rw [show tr V' n s m (cmap A x) = cmap A (tr V n s m x) from h3.symm, cmap_val _ _ hg]

end GlobalTheory.CompanionTheory.GelC
