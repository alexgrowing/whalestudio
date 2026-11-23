import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.KeyFormula

open Complex Matrix Real

noncomputable section

structure SiegelPt (g : ℕ) where

  τ : Matrix (Fin g) (Fin g) ℂ
  isSymm : τ.IsSymm
  im_posDef : (τ.map Complex.im).PosDef

def intVec {g : ℕ} (v : Fin g → ℤ) : Fin g → ℂ := fun i => (v i : ℂ)

structure HalfChar (g : ℕ) where

  ε : Fin g → Fin 2

  ε' : Fin g → Fin 2

namespace HalfChar

variable {g : ℕ} (m : HalfChar g)

def a : Fin g → ℂ := fun i => ((m.ε i : ℕ) : ℂ) / 2

def b : Fin g → ℂ := fun i => ((m.ε' i : ℕ) : ℂ) / 2

def zero (g : ℕ) : HalfChar g := ⟨fun _ => 0, fun _ => 0⟩

end HalfChar

def autFactor {g : ℕ} (P : SiegelPt g) (m : HalfChar g) (n : ℕ) (u : Fin g → ℤ) (z : Fin g → ℂ) :
    ℂ :=
  cexp (-(π * I * n * (intVec u ⬝ᵥ P.τ *ᵥ intVec u)) - 2 * π * I * n * (intVec u ⬝ᵥ (z + m.b)))

def perFactor {g : ℕ} (m : HalfChar g) (n : ℕ) (v : Fin g → ℤ) : ℂ :=
  cexp (2 * π * I * n * (m.a ⬝ᵥ intVec v))

def thetaSec {g : ℕ} (P : SiegelPt g) (m : HalfChar g) (n : ℕ) :
    Submodule ℂ ((Fin g → ℂ) → ℂ) where
  carrier := {f | Differentiable ℂ f ∧
    (∀ (v : Fin g → ℤ) (z : Fin g → ℂ), f (z + intVec v) = perFactor m n v * f z) ∧
    ∀ (u : Fin g → ℤ) (z : Fin g → ℂ), f (z + P.τ *ᵥ intVec u) = autFactor P m n u z * f z}
  add_mem' := by
    rintro f h ⟨hf, hf1, hf2⟩ ⟨hh, hh1, hh2⟩
    refine ⟨hf.add hh, fun v z => ?_, fun u z => ?_⟩
    · simp only [Pi.add_apply, hf1, hh1]; ring
    · simp only [Pi.add_apply, hf2, hh2]; ring
  zero_mem' := ⟨differentiable_const 0, fun _ _ => by simp, fun _ _ => by simp⟩
  smul_mem' := by
    rintro c f ⟨hf, hf1, hf2⟩
    refine ⟨hf.const_smul c, fun v z => ?_, fun u z => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, hf1]; ring
    · simp only [Pi.smul_apply, smul_eq_mul, hf2]; ring

lemma perFactor_add {g : ℕ} (m : HalfChar g) (k n : ℕ) (v : Fin g → ℤ) :
    perFactor m k v * perFactor m n v = perFactor m (k + n) v := by
  unfold perFactor
  rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma autFactor_add {g : ℕ} (P : SiegelPt g) (m : HalfChar g) (k n : ℕ) (u : Fin g → ℤ)
    (z : Fin g → ℂ) : autFactor P m k u z * autFactor P m n u z = autFactor P m (k + n) u z := by
  unfold autFactor
  rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem thetaSec_mul {g : ℕ} (P : SiegelPt g) (m : HalfChar g) {k n : ℕ}
    {f h : (Fin g → ℂ) → ℂ} (hf : f ∈ thetaSec P m k) (hh : h ∈ thetaSec P m n) :
    f * h ∈ thetaSec P m (k + n) := by
  obtain ⟨hf, hf1, hf2⟩ := hf
  obtain ⟨hh, hh1, hh2⟩ := hh
  refine ⟨hf.mul hh, fun v z => ?_, fun u z => ?_⟩
  · simp only [Pi.mul_apply, hf1, hh1, ← perFactor_add]; ring
  · simp only [Pi.mul_apply, hf2, hh2, ← autFactor_add]; ring

theorem const_mem_thetaSec_zero {g : ℕ} (P : SiegelPt g) (m : HalfChar g) (c : ℂ) :
    (fun _ => c) ∈ thetaSec P m 0 := by
  refine ⟨differentiable_const c, fun v z => ?_, fun u z => ?_⟩
  · simp [perFactor]
  · simp [autFactor]

structure RigSymForm (K : Type) [Field K] [Algebra K ℂ] where

  g : ℕ

  pt : SiegelPt g

  ch : HalfChar g

  S : ℕ → Submodule K ((Fin g → ℂ) → ℂ)
  S_le : ∀ n, ∀ f ∈ S n, f ∈ thetaSec pt ch n
  one_mem : (fun _ => (1 : ℂ)) ∈ S 0
  mul_mem : ∀ k n f h, f ∈ S k → h ∈ S n → f * h ∈ S (k + n)
  span_eq : ∀ n, Submodule.span ℂ (S n : Set ((Fin g → ℂ) → ℂ)) = thetaSec pt ch n
  linIndep : ∀ (n : ℕ) (s : Finset ((Fin g → ℂ) → ℂ)), (↑s : Set ((Fin g → ℂ) → ℂ)) ⊆ S n →
    LinearIndependent K (fun f : s => (f : (Fin g → ℂ) → ℂ)) →
    LinearIndependent ℂ (fun f : s => (f : (Fin g → ℂ) → ℂ))

  rig : ℂˣ
  rig_mem : ∀ n, ∀ f ∈ S n, ∃ c : K, (rig : ℂ) ^ n * f 0 = algebraMap K ℂ c

def tauI : SiegelPt 1 where
  τ := I • (1 : Matrix (Fin 1) (Fin 1) ℂ)
  isSymm := by simp [Matrix.IsSymm, Matrix.transpose_smul]
  im_posDef := by
    have : (I • (1 : Matrix (Fin 1) (Fin 1) ℂ)).map Complex.im = 1 := by
      ext i j; fin_cases i; fin_cases j; simp
    rw [this]; exact Matrix.PosDef.one

lemma jacobiTheta₂_add_int (w τ : ℂ) (k : ℤ) : jacobiTheta₂ (w + k) τ = jacobiTheta₂ w τ := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have := jacobiTheta₂_add_left (w + k) τ
    push_cast at ih ⊢; rw [← add_assoc, this, ih]
  | pred k ih =>
    have := jacobiTheta₂_add_left (w + (-(k : ℂ) - 1)) τ
    push_cast at ih ⊢
    rw [show w + (-(k : ℂ) - 1) + 1 = w + -(k : ℂ) by ring] at this
    rw [← this, ih]

lemma jacobiTheta₂_add_int_mul (w τ : ℂ) (k : ℤ) :
    jacobiTheta₂ (w + k * τ) τ = cexp (-(π * I * k ^ 2 * τ) - 2 * π * I * k * w) * jacobiTheta₂ w τ := by
  induction k using Int.induction_on generalizing w with
  | zero => simp
  | succ k ih =>
    push_cast at ih ⊢
    rw [show w + ((k : ℂ) + 1) * τ = (w + (k : ℂ) * τ) + τ by ring, jacobiTheta₂_add_left', ih,
      ← mul_assoc, ← Complex.exp_add]
    congr 1; ring_nf
  | pred k ih =>
    push_cast at ih ⊢
    have h := jacobiTheta₂_add_left' (w + (-(k : ℂ) - 1) * τ) τ
    rw [show w + (-(k : ℂ) - 1) * τ + τ = w + -(k : ℂ) * τ by ring, ih] at h
    have hne := Complex.exp_ne_zero (-π * I * (τ + 2 * (w + (-(k : ℂ) - 1) * τ)))
    rw [eq_comm, ← eq_inv_mul_iff_mul_eq₀ hne] at h
    rw [h, ← mul_assoc, ← Complex.exp_neg, ← Complex.exp_add]
    congr 1; ring_nf

def thetaOneVar : (Fin 1 → ℂ) → ℂ := fun z => jacobiTheta₂ (z 0) I

lemma intVec_one (v : Fin 1 → ℤ) : intVec v 0 = (v 0 : ℂ) := rfl

theorem thetaOneVar_mem : thetaOneVar ∈ thetaSec tauI (HalfChar.zero 1) 1 := by
  refine ⟨?_, fun v z => ?_, fun u z => ?_⟩
  · intro z
    have h1 : DifferentiableAt ℂ (fun w : ℂ => jacobiTheta₂ w I) (z 0) :=
      differentiableAt_jacobiTheta₂_fst (z 0) (by simp)
    have h2 : DifferentiableAt ℂ (fun z : Fin 1 → ℂ => z 0) z := (differentiable_apply 0) z
    exact h1.comp z h2
  · have : perFactor (HalfChar.zero 1) 1 v = 1 := by
      simp [perFactor, HalfChar.a, HalfChar.zero, dotProduct]
    rw [this, one_mul]
    simp only [thetaOneVar, Pi.add_apply, intVec_one]
    exact jacobiTheta₂_add_int (z 0) I (v 0)
  · simp only [thetaOneVar, Pi.add_apply, autFactor, tauI]
    have hτ : ((I • (1 : Matrix (Fin 1) (Fin 1) ℂ)) *ᵥ intVec u) 0 = (u 0 : ℂ) * I := by
      simp [Matrix.mulVec, dotProduct, intVec, mul_comm]
    rw [hτ, jacobiTheta₂_add_int_mul]
    congr 2
    simp [dotProduct, Matrix.mulVec, intVec, HalfChar.b, HalfChar.zero]
    ring

theorem thetaOneVar_zero_ne : thetaOneVar 0 ≠ 0 := by
  intro h
  have hb := norm_jacobiTheta_sub_one_le (τ := I) (by simp)
  rw [jacobiTheta_eq_jacobiTheta₂] at hb
  simp only [thetaOneVar, Pi.zero_apply] at h
  rw [h] at hb
  simp only [zero_sub, norm_neg, norm_one, Complex.I_im, mul_one] at hb
  have hπ : 3 < Real.exp Real.pi := by
    have := Real.add_one_le_exp Real.pi
    linarith [Real.pi_gt_three]
  have ht : Real.exp (-Real.pi) < 1 / 3 := by
    rw [Real.exp_neg]
    rw [inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
    simpa using hπ
  have htpos := Real.exp_pos (-Real.pi)
  have h1 : 0 < 1 - Real.exp (-Real.pi) := by linarith
  have : 2 / (1 - Real.exp (-Real.pi)) * Real.exp (-Real.pi) < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one h1]; linarith
  linarith

theorem thetaOneVar_ne_zero : thetaOneVar ≠ 0 := fun h => thetaOneVar_zero_ne (by rw [h]; rfl)

def rigSymFormTauI : RigSymForm ℂ where
  g := 1
  pt := tauI
  ch := HalfChar.zero 1
  S := fun n => thetaSec tauI (HalfChar.zero 1) n
  S_le := fun _ _ hf => hf
  one_mem := const_mem_thetaSec_zero _ _ 1
  mul_mem := fun _ _ _ _ hf hh => thetaSec_mul _ _ hf hh
  span_eq := fun n => Submodule.span_eq _
  linIndep := fun _ _ _ h => h
  rig := 1
  rig_mem := fun n f _ => ⟨(1 : ℂ) ^ n * f 0, by simp⟩

theorem rigSymFormTauI_nontrivial :
    rigSymFormTauI.g = 1 ∧ ∃ f ∈ rigSymFormTauI.S 1, f ≠ 0 :=
  ⟨rfl, thetaOneVar, thetaOneVar_mem, thetaOneVar_ne_zero⟩

end

end GroundTheory.Heights₂.Heights.KeyFormula
