import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TupMemLatT
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.TraceConjugationCover

open scoped BigOperators

def trBound {l : ℕ} [Fact l.Prime] {a m : ℕ} (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) : ℝ :=
  ∑ k, ∑ x ∈ t k, ‖x.trace‖

theorem trBound_nonneg {l : ℕ} [Fact l.Prime] {a m : ℕ} (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) :
    0 ≤ trBound t :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem le_trBound {l : ℕ} [Fact l.Prime] {a m : ℕ} (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l)))
    (k : Fin m) {x : Matrix (Fin a) (Fin a) (Om l)} (hx : x ∈ t k) : ‖x.trace‖ ≤ trBound t := by
  unfold trBound
  refine le_trans ?_ (Finset.single_le_sum (f := fun k => ∑ x ∈ t k, ‖x.trace‖)
    (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ k))
  exact Finset.single_le_sum (f := fun x => ‖x.trace‖) (fun _ _ => norm_nonneg _) hx

theorem norm_trace_latL {l : ℕ} [Fact l.Prime] {a m : ℕ} (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l)))
    (M : ℕ) (y : Fin m → Matrix (Fin a) (Fin a) (Om l)) (hy : y ∈ latL t M) (k : Fin m) :
    ‖(y k).trace‖ ≤ ((l : ℝ)⁻¹) ^ M * trBound t := by
  have h0 : 0 ≤ ((l : ℝ)⁻¹) ^ M * trBound t := mul_nonneg (pow_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) _) (trBound_nonneg t)
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
    obtain ⟨z, hz, rfl⟩ := hj
    dsimp only
    by_cases hjk : k = j
    · subst hjk
      rw [Pi.single_eq_same, Matrix.trace_smul, smul_eq_mul, norm_mul, norm_pow, norm_l]
      exact mul_le_mul_of_nonneg_left (le_trBound t k hz) (pow_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) _)
    · rw [Pi.single_eq_of_ne hjk, Matrix.trace_zero, norm_zero]
      exact h0
  | zero => simpa using h0
  | add x y _ _ hx hy =>
    rw [Pi.add_apply, Matrix.trace_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  | smul c x _ hx =>
    rw [Pi.smul_apply, Matrix.trace_smul, ← zOm_smul, smul_eq_mul, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_zOm_le c)).trans hx

end GlobalTheory.TraceConjugationCover

namespace GlobalTheory

theorem trace_estimate_latL : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a : ℕ) (r : Γ →* GL (Fin a) (Om l)) (m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (c N n : ℕ) (cs : Fin m → Om l), n ≤ N → (∀ g, ‖trc r g - ∑ k, cs k * trc (ρs k) g‖ ≤ ((l : ℝ)⁻¹) ^ (N + c)) → ∃ M₁ : ℕ, ∀ M, M₁ ≤ M → ∀ (F : Γ →₀ ℤ_[l]) (y : Fin m → Matrix (Fin a) (Fin a) (Om l)), y ∈ GlobalTheory.TraceConjugationCover.latL t M → ‖(F.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))).trace - ∑ k, cs k * (((F.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) + y) k).trace‖ ≤ ((l : ℝ) ^ n)⁻¹ := by
  intro l _ Γ _ a r m ρs t c N n cs hnN hr
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := zero_lt_one.trans hl1
  set C : ℝ := TraceConjugationCover.trBound t * ∑ k, ‖cs k‖ with hC
  have hC0 : 0 ≤ C := mul_nonneg (TraceConjugationCover.trBound_nonneg t) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt C hl1
  refine ⟨n + K, fun M hM F y hy => ?_⟩
  have hinv : ((l : ℝ)⁻¹) ^ n = ((l : ℝ) ^ n)⁻¹ := inv_pow _ _
  have hle1 : (l : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hl1.le
  have hinv0 : (0 : ℝ) ≤ (l : ℝ)⁻¹ := inv_nonneg.2 hl0.le

  have hsplit : (F.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))).trace - ∑ k, cs k * (((F.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) + y) k).trace
      = (F.sum fun h c => zOm l c * (trc r h - ∑ k, cs k * trc (ρs k) h)) - ∑ k, cs k * (y k).trace := by
    simp only [Finsupp.sum, Pi.add_apply, Finset.sum_apply, Matrix.trace_add, Matrix.trace_sum, Pi.smul_apply,
      Matrix.trace_smul, smul_eq_mul, TraceConjugationCover.tup, trc, mul_add, Finset.sum_add_distrib, mul_sub, Finset.mul_sum]
    rw [Finset.sum_sub_distrib, Finset.sum_comm (s := (Finset.univ : Finset (Fin m)))]
    simp only [mul_left_comm (cs _)]
    ring
  rw [hsplit]
  have h1 : ‖F.sum fun h c => zOm l c * (trc r h - ∑ k, cs k * trc (ρs k) h)‖ ≤ ((l : ℝ) ^ n)⁻¹ := by
    rw [← hinv]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hinv0 _) fun h _ => ?_
    rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (TraceConjugationCover.norm_zOm_le _)).trans ((hr h).trans ?_)
    exact pow_le_pow_of_le_one hinv0 hle1 (by omega)
  have h2 : ‖∑ k, cs k * (y k).trace‖ ≤ ((l : ℝ) ^ n)⁻¹ := by
    calc ‖∑ k, cs k * (y k).trace‖ ≤ ∑ k, ‖cs k‖ * (((l : ℝ)⁻¹) ^ M * TraceConjugationCover.trBound t) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (TraceConjugationCover.norm_trace_latL t M y hy k) (norm_nonneg _)
      _ = ((l : ℝ)⁻¹) ^ M * C := by rw [hC, ← Finset.sum_mul]; ring
      _ ≤ ((l : ℝ)⁻¹) ^ (n + K) * (l : ℝ) ^ K :=
          mul_le_mul (pow_le_pow_of_le_one hinv0 hle1 hM) hK.le hC0 (pow_nonneg hinv0 _)
      _ = ((l : ℝ) ^ n)⁻¹ := by
          rw [pow_add, inv_pow, inv_pow, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hl0.ne'), mul_one]
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 ?_)
  rwa [norm_neg]

end GlobalTheory

end
