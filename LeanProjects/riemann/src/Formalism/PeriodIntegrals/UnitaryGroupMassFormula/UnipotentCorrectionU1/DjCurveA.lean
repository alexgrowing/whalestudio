import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CoreStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumEqSumCompEmbedding
import Lemmata.B110.ExistsMoved

open Matrix

noncomputable section

namespace PI.UnitaryCorollaryDerivatives.DjC

section Gen

variable {N j : ℕ}

def Pres (S : Set (Fin N)) (Y : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ c b : Fin N, b ∈ S → c ∉ S → Y c b = 0

theorem pres_mul {S : Set (Fin N)} {X Y : Matrix (Fin N) (Fin N) ℂ} (hX : Pres S X) (hY : Pres S Y) :
    Pres S (X * Y) := by
  intro c b hb hc
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  by_cases hm : m ∈ S
  · rw [hX c m hm hc, zero_mul]
  · rw [hY m b hb hm, mul_zero]

theorem pres_pow {S : Set (Fin N)} {Y : Matrix (Fin N) (Fin N) ℂ} (hY : Pres S Y) (n : ℕ) :
    Pres S (Y ^ n) := by
  induction n with
  | zero =>
    intro c b hb hc
    rw [pow_zero, Matrix.one_apply_ne]
    rintro rfl; exact hc hb
  | succ n ih => rw [pow_succ]; exact pres_mul ih hY

theorem pres_smul {S : Set (Fin N)} {Y : Matrix (Fin N) (Fin N) ℂ} (hY : Pres S Y) (z : ℂ) :
    Pres S (z • Y) := by
  intro c b hb hc
  rw [Matrix.smul_apply, hY c b hb hc, smul_zero]

theorem pres_neg {S : Set (Fin N)} {Y : Matrix (Fin N) (Fin N) ℂ} (hY : Pres S Y) : Pres S (-Y) := by
  intro c b hb hc
  rw [Matrix.neg_apply, hY c b hb hc, neg_zero]

open scoped Matrix.Norms.Operator in
theorem pres_exp {S : Set (Fin N)} {Y : Matrix (Fin N) (Fin N) ℂ} (hY : Pres S Y) :
    Pres S (NormedSpace.exp Y) := by
  intro c b hb hc
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Y
  have h1 := Pi.hasSum.1 h c
  have h2 := Pi.hasSum.1 h1 b
  have h3 : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹ • Y ^ n) c b) 0 := by
    have : (fun n : ℕ => ((n.factorial : ℂ)⁻¹ • Y ^ n) c b) = fun _ => 0 := by
      funext n; rw [Matrix.smul_apply, pres_pow hY n c b hb hc, smul_zero]
    rw [this]; exact hasSum_zero
  exact h2.unique h3

theorem sum_emb (e : Fin j ↪ Fin N) (f : Fin N → ℂ) (hf : ∀ c, c ∉ Set.range e → f c = 0) :
    ∑ c, f c = ∑ a, f (e a) := by
  first | exact GlobalTheory.EmbeddingSum.sum_eq_sum_comp_embedding .. | (apply GlobalTheory.EmbeddingSum.sum_eq_sum_comp_embedding <;> assumption) | (intros; apply GlobalTheory.EmbeddingSum.sum_eq_sum_comp_embedding <;> assumption) | (apply @GlobalTheory.EmbeddingSum.sum_eq_sum_comp_embedding <;> assumption) | (intros; apply @GlobalTheory.EmbeddingSum.sum_eq_sum_comp_embedding <;> assumption) | (apply @GlobalTheory.EmbeddingSum.sum_eq_sum_comp_embedding <;> first | assumption | infer_instance) | exact @GlobalTheory.EmbeddingSum.sum_eq_sum_comp_embedding N j e f hf | exact @GlobalTheory.EmbeddingSum.sum_eq_sum_comp_embedding N j e f | exact @GlobalTheory.EmbeddingSum.sum_eq_sum_comp_embedding N j e | exact @GlobalTheory.EmbeddingSum.sum_eq_sum_comp_embedding N j | exact @GlobalTheory.EmbeddingSum.sum_eq_sum_comp_embedding N

def sub (e : Fin j ↪ Fin N) (E : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin j) (Fin j) ℂ :=
  Matrix.of fun a b => E (e a) (e b)

theorem sub_right (e : Fin j ↪ Fin N) (row : Fin j → Fin N) (h E : Matrix (Fin N) (Fin N) ℂ)
    (hE : Pres (Set.range e) E) :
    (Matrix.of fun a b => (h * E) (row a) (e b)) = (Matrix.of fun a b => h (row a) (e b)) * sub e E := by
  ext a b
  rw [Matrix.of_apply, Matrix.mul_apply, Matrix.mul_apply]
  exact sum_emb e _ fun c hc => by rw [hE c (e b) ⟨b, rfl⟩ hc, mul_zero]

theorem sub_left (e : Fin j ↪ Fin N) (col : Fin j → Fin N) (h E : Matrix (Fin N) (Fin N) ℂ)
    (hE : Pres (Set.range e)ᶜ E) :
    (Matrix.of fun a b => (E * h) (e a) (col b)) = sub e E * (Matrix.of fun a b => h (e a) (col b)) := by
  ext a b
  rw [Matrix.of_apply, Matrix.mul_apply, Matrix.mul_apply]
  exact sum_emb e _ fun c hc => by rw [hE (e a) c hc (fun h' => h' ⟨a, rfl⟩), zero_mul]

end Gen

section DetExp

variable {n : Type} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.Operator in
theorem hasDerivAt_exp_entry (X : Matrix n n ℂ) (i j : n) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • X)) i j) (X i j) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let L : Matrix n n ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem hasDerivAt_det_of_one (A : ℝ → Matrix n n ℂ) (A' : Matrix n n ℂ) (h0 : A 0 = 1)
    (h : ∀ i j, HasDerivAt (fun t => A t i j) (A' i j) 0) :
    HasDerivAt (fun t => (A t).det) A'.trace 0 := by
  first | exact Bl.b110.goal1 .. | (apply Bl.b110.goal1 <;> assumption) | (intros; apply Bl.b110.goal1 <;> assumption) | (apply @Bl.b110.goal1 <;> assumption) | (intros; apply @Bl.b110.goal1 <;> assumption) | (apply @Bl.b110.goal1 <;> first | assumption | infer_instance) | exact @Bl.b110.goal1 n ‹_› ‹_› A A' h0 h | exact @Bl.b110.goal1 n ‹_› ‹_› A A' h0 | exact @Bl.b110.goal1 n ‹_› ‹_› A A' | exact @Bl.b110.goal1 n ‹_› ‹_› A | exact @Bl.b110.goal1 n ‹_› ‹_› | exact @Bl.b110.goal1 n ‹_› | exact @Bl.b110.goal1 n

end DetExp

theorem mul_hom_exp (φ : ℝ → ℂ) (c : ℂ) (hmul : ∀ s t, φ (s + t) = φ s * φ t) (h1 : φ 0 = 1)
    (h0 : HasDerivAt φ c 0) (t : ℝ) : φ t = Complex.exp (t * c) := by
  have hd : ∀ t, HasDerivAt φ (φ t * c) t := by
    intro t
    have h1' : HasDerivAt (fun s => φ (s - t)) c t := by
      have h00 := h0
      rw [← sub_self t] at h00
      exact h00.comp_sub_const t t
    have h2 := h1'.const_mul (φ t)
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    show φ s = φ t * φ (s - t)
    rw [← hmul]; congr 1; ring
  let ψ : ℝ → ℂ := fun t => φ t * Complex.exp (-((t : ℂ) * c))
  have hψ : ∀ t, HasDerivAt ψ 0 t := by
    intro t
    have e0 : HasDerivAt (fun t : ℝ => -((t : ℂ) * c)) (-(1 * c)) t := by
      have h := ((hasDerivAt_id t).ofReal_comp.mul_const c).fun_neg
      simpa using h
    have e1 := e0.cexp
    have h3 := (hd t).fun_mul e1
    have h4 : φ t * c * Complex.exp (-((t : ℂ) * c)) +
        φ t * (Complex.exp (-((t : ℂ) * c)) * -(1 * c)) = 0 := by ring
    rw [h4] at h3
    exact h3
  have hc := is_const_of_deriv_eq_zero (fun t => (hψ t).differentiableAt) (fun t => (hψ t).deriv) t 0
  simp only [ψ, h1, Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one] at hc
  rw [Complex.exp_neg] at hc
  exact eq_of_mul_inv_eq_one hc

end PI.UnitaryCorollaryDerivatives.DjC
