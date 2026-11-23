import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobianDensityHermitianMetrics
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobiDensityWeightedThetaIntegralZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeEqFormDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VandermondeWeightedRootProductSum
open Filter Topology MeasureTheory Matrix
open GlobalTheory GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (emb jacDens)
open GlobalTheory.FlagFibre (Low uni)
open GlobalTheory.FlagFormDeg (apolar)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open scoped ContDiff ComplexOrder Classical

namespace GlobalTheory.UnitInvBilin

open Matrix

theorem conj_single {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (p q : Fin r) :
    Aᴴ * single p q 1 * A = of fun i j => star (A p i) * A q j := by
  ext i j
  simp [Matrix.mul_apply, Matrix.single_apply, Finset.sum_mul, ite_and]

def phase {r : ℕ} (k : Fin r) : Matrix (Fin r) (Fin r) ℂ :=
  diagonal fun i => if i = k then Complex.I else 1

theorem phase_unitary {r : ℕ} (k : Fin r) : (phase k)ᴴ * phase k = 1 := by
  rw [phase, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext i
  by_cases h : i = k <;> simp [h]

theorem phase_single {r : ℕ} (k p q : Fin r) :
    (phase k)ᴴ * single p q 1 * phase k =
      single p q (star (if p = k then Complex.I else 1) * (if q = k then Complex.I else 1)) := by
  rw [conj_single]
  ext i j
  simp only [phase, diagonal_apply, of_apply, single_apply]
  by_cases hi : p = i <;> by_cases hj : q = j <;> simp [hi, hj, eq_comm]

def rot {r : ℕ} (a c : Fin r) (x y : ℝ) : Matrix (Fin r) (Fin r) ℂ :=
  1 + single a a ((x : ℂ) - 1) + single c c ((x : ℂ) - 1) + single a c (y : ℂ) + single c a (-(y : ℂ))

theorem rot_unitary {r : ℕ} (a c : Fin r) (hac : a ≠ c) (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1) :
    (rot a c x y)ᴴ * rot a c x y = 1 := by
  have hC : (x : ℂ) ^ 2 + (y : ℂ) ^ 2 = 1 := by exact_mod_cast h
  have e1 : ∀ (p q : Fin r) (u v : ℂ), single p c u * single a q v = 0 :=
    fun p q u v => single_mul_single_of_ne _ _ _ _ hac.symm _
  have e2 : ∀ (p q : Fin r) (u v : ℂ), single p a u * single c q v = 0 :=
    fun p q u v => single_mul_single_of_ne _ _ _ _ hac _
  simp only [rot, conjTranspose_add, conjTranspose_one, conjTranspose_single, add_mul, mul_add,
    one_mul, mul_one, single_mul_single_same, e1, e2, star_sub, star_one, star_neg, Complex.star_def, Complex.conj_ofReal]
  ext i j
  simp only [Matrix.add_apply, Matrix.one_apply, single_apply, Matrix.zero_apply]
  by_cases hia : a = i <;> by_cases hic : c = i <;> by_cases hja : a = j <;> by_cases hjc : c = j <;>
    subst_vars <;> simp_all <;> first | linear_combination hC | ring

theorem rot_conj_aa {r : ℕ} (a c : Fin r) (hac : a ≠ c) (x y : ℝ) :
    (rot a c x y)ᴴ * single a a 1 * rot a c x y =
      ((x : ℂ) ^ 2) • single a a (1 : ℂ) + ((x : ℂ) * y) • single a c 1 + ((x : ℂ) * y) • single c a 1 +
        ((y : ℂ) ^ 2) • single c c 1 := by
  have e1 : ∀ (p q : Fin r) (u v : ℂ), single p c u * single a q v = 0 :=
    fun p q u v => single_mul_single_of_ne _ _ _ _ hac.symm _
  have e2 : ∀ (p q : Fin r) (u v : ℂ), single p a u * single c q v = 0 :=
    fun p q u v => single_mul_single_of_ne _ _ _ _ hac _
  simp only [rot, conjTranspose_add, conjTranspose_one, conjTranspose_single, add_mul, mul_add,
    one_mul, mul_one, single_mul_single_same, e1, e2, star_sub, star_one, star_neg, Complex.star_def,
    Complex.conj_ofReal, zero_add, add_zero]
  ext i j
  simp only [Matrix.add_apply, Matrix.one_apply, single_apply, Matrix.zero_apply, Matrix.smul_apply,
    smul_eq_mul]
  by_cases hia : a = i <;> by_cases hic : c = i <;> by_cases hja : a = j <;> by_cases hjc : c = j <;>
    subst_vars <;> simp_all <;> ring

theorem rot_conj_cc {r : ℕ} (a c : Fin r) (hac : a ≠ c) (x y : ℝ) :
    (rot a c x y)ᴴ * single c c 1 * rot a c x y =
      ((y : ℂ) ^ 2) • single a a (1 : ℂ) + (-((x : ℂ) * y)) • single a c 1 + (-((x : ℂ) * y)) • single c a 1 +
        ((x : ℂ) ^ 2) • single c c 1 := by
  have e1 : ∀ (p q : Fin r) (u v : ℂ), single p c u * single a q v = 0 :=
    fun p q u v => single_mul_single_of_ne _ _ _ _ hac.symm _
  have e2 : ∀ (p q : Fin r) (u v : ℂ), single p a u * single c q v = 0 :=
    fun p q u v => single_mul_single_of_ne _ _ _ _ hac _
  simp only [rot, conjTranspose_add, conjTranspose_one, conjTranspose_single, add_mul, mul_add,
    one_mul, mul_one, single_mul_single_same, e1, e2, star_sub, star_one, star_neg, Complex.star_def,
    Complex.conj_ofReal, zero_add, add_zero]
  ext i j
  simp only [Matrix.add_apply, Matrix.one_apply, single_apply, Matrix.zero_apply, Matrix.smul_apply,
    smul_eq_mul]
  by_cases hia : a = i <;> by_cases hic : c = i <;> by_cases hja : a = j <;> by_cases hjc : c = j <;>
    subst_vars <;> simp_all <;> ring

section forms

variable {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ →ₗ[ℂ] Matrix (Fin r) (Fin r) ℂ →ₗ[ℂ] ℂ)

theorem single_eq_smul (p q : Fin r) (u : ℂ) : single p q u = u • single p q (1 : ℂ) := by
  rw [smul_single, smul_eq_mul, mul_one]

theorem vanish
    (hU : ∀ U : Matrix (Fin r) (Fin r) ℂ, Uᴴ * U = 1 → ∀ F F', B (Uᴴ * F * U) (Uᴴ * F' * U) = B F F')
    (p q s t : Fin r) (hP : ¬((p = q ∧ s = t) ∨ (p = t ∧ q = s))) :
    B (single p q 1) (single s t 1) = 0 := by
  have key : ∀ k : Fin r, B (single p q 1) (single s t 1) *
      ((star (if p = k then Complex.I else 1) * (if q = k then Complex.I else 1)) *
        (star (if s = k then Complex.I else 1) * (if t = k then Complex.I else 1)) - 1) = 0 := by
    intro k
    have h := hU (phase k) (phase_unitary k) (single p q 1) (single s t 1)
    rw [phase_single, phase_single, single_eq_smul p q, single_eq_smul s t] at h
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    linear_combination h
  by_contra hne
  have hk : ∀ k : Fin r, (star (if p = k then Complex.I else 1) * (if q = k then Complex.I else 1)) *
        (star (if s = k then Complex.I else 1) * (if t = k then Complex.I else 1)) = 1 :=
    fun k => sub_eq_zero.1 ((mul_eq_zero.1 (key k)).resolve_left hne)
  by_cases hpq : p = q
  · subst hpq
    have hst : s ≠ t := fun h => hP (Or.inl ⟨rfl, h⟩)
    have h := hk s
    by_cases hps : p = s <;> simp [hps, hst, hst.symm, Complex.ext_iff] at h
  · by_cases hpt : p = t
    · subst hpt
      have hqs : q ≠ s := fun h => hP (Or.inr ⟨rfl, h⟩)
      have h := hk s
      by_cases hps : p = s <;> simp [hps, hqs, hqs.symm, Complex.ext_iff] at h
    · have h := hk p
      by_cases hsp : s = p <;>
        simp [hpq, hpt, Ne.symm hpq, Ne.symm hpt, hsp, Complex.ext_iff] at h <;> norm_num at h

theorem rot_rel
    (hU : ∀ U : Matrix (Fin r) (Fin r) ℂ, Uᴴ * U = 1 → ∀ F F', B (Uᴴ * F * U) (Uᴴ * F' * U) = B F F')
    (a c : Fin r) (hac : a ≠ c) (x y : ℝ) (hxy : x ^ 2 + y ^ 2 = 1) :
    let b := fun p q s t : Fin r => B (single p q 1) (single s t 1)
    b a a a a = (x : ℂ) ^ 4 * b a a a a +
        (x : ℂ) ^ 2 * (y : ℂ) ^ 2 * (b a a c c + b c c a a + b a c c a + b c a a c) + (y : ℂ) ^ 4 * b c c c c ∧
    b c c c c = (y : ℂ) ^ 4 * b a a a a +
        (x : ℂ) ^ 2 * (y : ℂ) ^ 2 * (b a a c c + b c c a a + b a c c a + b c a a c) + (x : ℂ) ^ 4 * b c c c c ∧
    b a a c c = (x : ℂ) ^ 2 * (y : ℂ) ^ 2 * b a a a a + (x : ℂ) ^ 4 * b a a c c + (y : ℂ) ^ 4 * b c c a a -
        (x : ℂ) ^ 2 * (y : ℂ) ^ 2 * (b a c c a + b c a a c) + (x : ℂ) ^ 2 * (y : ℂ) ^ 2 * b c c c c := by
  intro b
  have hv := vanish B hU
  have hR := rot_unitary a c hac x y hxy
  have h1 := hU _ hR (single a a 1) (single a a 1)
  have h2 := hU _ hR (single c c 1) (single c c 1)
  have h3 := hU _ hR (single a a 1) (single c c 1)
  rw [rot_conj_aa a c hac] at h1 h3
  rw [rot_conj_cc a c hac] at h2 h3
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at h1 h2 h3
  simp (disch := simp [hac, hac.symm]) only [hv, mul_zero, add_zero, zero_add] at h1 h2 h3
  refine ⟨?_, ?_, ?_⟩
  · linear_combination -h1
  · linear_combination -h2
  · linear_combination -h3

end forms

theorem eq_trace_form : ∀ (r : ℕ) (B : Matrix (Fin r) (Fin r) ℂ →ₗ[ℂ] Matrix (Fin r) (Fin r) ℂ →ₗ[ℂ] ℂ) (μ : ℂ), (∀ U : Matrix (Fin r) (Fin r) ℂ, Uᴴ * U = 1 → ∀ F F', B (Uᴴ * F * U) (Uᴴ * F' * U) = B F F') → (∀ a b c d : Fin r, B (Matrix.single a b 1) (Matrix.single c d 1) = B (Matrix.single c b 1) (Matrix.single a d 1)) → (∀ F, B 1 F = μ * F.trace) → ∀ F F', B F F' = μ / (r + 1) * (F.trace * F'.trace + (F * F').trace) := by
  intro r B μ hU hS h1
  have hv := vanish B hU
  have hr : (r : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero r
  have hdc : ∀ a c : Fin r, a ≠ c →
      B (single a a 1) (single a a 1) = B (single c c 1) (single c c 1) ∧
      B (single a a 1) (single c c 1) = B (single c c 1) (single c c 1) / 2 := by
    intro a c hac
    obtain ⟨R1, R2, -⟩ := rot_rel B hU a c hac (3 / 5) (4 / 5) (by norm_num)
    obtain ⟨-, -, R3⟩ := rot_rel B hU a c hac 0 1 (by norm_num)
    dsimp only at R1 R2 R3
    push_cast at R1 R2 R3
    have e2 := hS a a c c
    have e3 := hS c c a a
    have G1 : B (single a a 1) (single a a 1) = B (single c c 1) (single c c 1) := by
      linear_combination (625 / 800 : ℂ) * (R1 - R2)
    refine ⟨G1, ?_⟩
    linear_combination (-625 / 576 : ℂ) * R1 + (1 / 2 : ℂ) * R3 + (1 / 4 : ℂ) * e2 + (1 / 4 : ℂ) * e3 +
      (17 / 18 : ℂ) * G1
  have hβ : ∀ p : Fin r, B (single p p 1) (single p p 1) = 2 * (μ / (r + 1)) := by
    intro p
    have h := h1 (single p p 1)
    rw [trace_single_eq_same, mul_one] at h
    have hone : (1 : Matrix (Fin r) (Fin r) ℂ) = ∑ a, single a a 1 := by
      rw [sum_single_eq_diagonal (fun _ => (1 : ℂ)), diagonal_one]
    rw [hone, map_sum, LinearMap.sum_apply] at h
    have hterm : ∀ a : Fin r, B (single a a 1) (single p p 1) =
        B (single p p 1) (single p p 1) / 2 + (if a = p then B (single p p 1) (single p p 1) / 2 else 0) := by
      intro a
      by_cases hap : a = p
      · subst hap; simp only [if_true]; ring
      · rw [(hdc a p hap).2, if_neg hap, add_zero]
    rw [Finset.sum_congr rfl (fun a _ => hterm a), Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, Finset.sum_ite_eq', if_pos (Finset.mem_univ _), nsmul_eq_mul] at h
    field_simp
    linear_combination 2 * h
  have hb : ∀ p q s t : Fin r, B (single p q 1) (single s t 1) =
      μ / (r + 1) * ((if p = q ∧ s = t then 1 else 0) + (if q = s ∧ p = t then 1 else 0)) := by
    intro p q s t
    by_cases hP : (p = q ∧ s = t) ∨ (p = t ∧ q = s)
    · rcases hP with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · by_cases hps : p = s
        · subst hps; rw [hβ]; simp <;> ring
        · rw [(hdc p s hps).2, hβ]; simp [hps] <;> ring
      · by_cases hpq : p = q
        · subst hpq; rw [hβ]; simp <;> ring
        · rw [← hS q q p p, (hdc q p (Ne.symm hpq)).2, hβ]; simp [hpq] <;> ring
    · rw [hv p q s t hP]
      have h2 : ¬(q = s ∧ p = t) := fun h => hP (Or.inr ⟨h.2, h.1⟩)
      simp [hP, h2]
      tauto
  intro F F'
  induction F using Matrix.induction_on' with
  | h_zero => simp
  | h_add P Q hP hQ => simp only [map_add, LinearMap.add_apply, add_mul, trace_add, hP, hQ]; ring
  | h_std_basis i j x =>
    induction F' using Matrix.induction_on' with
    | h_zero => simp
    | h_add P Q hP hQ => simp only [map_add, mul_add, trace_add, hP, hQ]; ring
    | h_std_basis s t y =>
      rw [single_eq_smul i j x, single_eq_smul s t y]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Matrix.smul_mul, Matrix.mul_smul,
        trace_smul, hb]
      clear hb hβ hdc hv hU hS h1
      by_cases hij : i = j <;> by_cases hst : s = t <;> by_cases hjs : j = s <;> by_cases hit : i = t <;>
        subst_vars <;>
        simp_all [single_mul_single_same, single_mul_single_of_ne, trace_single_eq_of_ne] <;> ring

end GlobalTheory.UnitInvBilin
