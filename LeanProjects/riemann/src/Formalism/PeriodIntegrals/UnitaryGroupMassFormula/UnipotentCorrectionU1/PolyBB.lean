import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.PolyBA

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section pb2

variable {k r : ℕ}

lemma pb_entry_le_gN (M : B.Mat k r) (i j : Fin (2 * r + k + 1)) : ‖M i j‖ ≤ B.gN M := by
  unfold B.gN
  have h1 : ‖M i j‖ ^ 2 ≤ ∑ a, ∑ b, Complex.normSq (M a b) := by
    rw [← Complex.normSq_eq_norm_sq]
    calc Complex.normSq (M i j) ≤ ∑ b, Complex.normSq (M i b) :=
          Finset.single_le_sum (f := fun b => Complex.normSq (M i b))
            (fun b _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ a, ∑ b, Complex.normSq (M a b) :=
          Finset.single_le_sum (f := fun a => ∑ b, Complex.normSq (M a b))
            (fun a _ => Finset.sum_nonneg fun b _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  calc ‖M i j‖ = Real.sqrt (‖M i j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt h1

lemma pb_sup_le_gN (g : B.Mat k r) : ‖g‖ ≤ B.gN g := by
  have h0 : 0 ≤ B.gN g := by unfold B.gN; positivity
  exact (Matrix.norm_le_iff h0).2 (fun i j => pb_entry_le_gN g i j)

lemma pb_mul_norm_le (A A' : B.Mat k r) : ‖A * A'‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (‖A‖ * ‖A'‖) := by
  rw [Matrix.norm_le_iff (by positivity)]
  intro i j
  rw [Matrix.mul_apply]
  calc ‖∑ l, A i l * A' l j‖ ≤ ∑ l, ‖A i l * A' l j‖ := norm_sum_le _ _
    _ ≤ ∑ _l : Fin (2 * r + k + 1), ‖A‖ * ‖A'‖ := Finset.sum_le_sum fun l _ => by
        rw [norm_mul]
        exact mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm A)
          (Matrix.norm_entry_le_entrywise_sup_norm A') (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp

lemma pb_dirL_le {x : Bool × B.Mat k r} (hx : B.unitLie k r x.2) (g : B.Mat k r) :
    ‖dirL x g‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * ‖g‖ := by
  have hX : ‖x.2‖ ≤ 1 := (Matrix.norm_le_iff zero_le_one).2 hx.2
  unfold dirL
  split_ifs
  · show ‖-x.2 * g‖ ≤ _
    calc ‖-x.2 * g‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (‖-x.2‖ * ‖g‖) := pb_mul_norm_le _ _
      _ ≤ _ := by
        rw [norm_neg]
        exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg _) hX) (by positivity)
  · first
    | show ‖g * x.2‖ ≤ _
      calc ‖g * x.2‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (‖g‖ * ‖x.2‖) := pb_mul_norm_le _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (norm_nonneg _) hX) (by positivity)
    | (unfold mulRightRealCLM; done)

lemma pb_Dw_clm {K : ℝ} (hK : 0 ≤ K) (w : List (Bool × B.Mat k r))
    (hw : ∀ x ∈ w, ∀ g, ‖dirL x g‖ ≤ K * ‖g‖) :
    ∀ (Λ : B.Mat k r →L[ℝ] ℂ) (c : ℝ), 0 ≤ c → (∀ g, ‖Λ g‖ ≤ c * ‖g‖) → ∃ Λ' : B.Mat k r →L[ℝ] ℂ,
      Dw w (fun g => Λ g) = (fun g => Λ' g) ∧ ∀ g, ‖Λ' g‖ ≤ c * K ^ w.length * ‖g‖ := by
  have hD : ∀ (L : B.Mat k r →L[ℝ] ℂ) (x : Bool × B.Mat k r),
      Dx x (fun g => L g) = fun g => L (dirL x g) := by
    intro L x
    funext g
    rw [Dx_eq, dirL_apply]
    exact (L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (crv_hasDerivAt x g)).deriv
  induction w with
  | nil =>
    intro Λ c hc hΛ
    refine ⟨Λ, rfl, fun g => ?_⟩
    simpa using hΛ g
  | cons x w ih =>
    intro Λ c hc hΛ
    obtain ⟨Λ₁, h₁, hb₁⟩ := ih (fun y hy => hw y (by simp [hy])) Λ c hc hΛ
    refine ⟨Λ₁.comp (dirL x), ?_, fun g => ?_⟩
    · show Dx x (Dw w fun g => Λ g) = _
      rw [h₁, hD]
      rfl
    · have hx := hw x (by simp) g
      calc ‖(Λ₁.comp (dirL x)) g‖ = ‖Λ₁ (dirL x g)‖ := rfl
        _ ≤ c * K ^ w.length * ‖dirL x g‖ := hb₁ _
        _ ≤ c * K ^ w.length * (K * ‖g‖) :=
          mul_le_mul_of_nonneg_left hx (mul_nonneg hc (pow_nonneg hK _))
        _ = c * K ^ (x :: w).length * ‖g‖ := by
          rw [List.length_cons, pow_succ]
          ring

lemma pb_clm (Λ : B.Mat k r →L[ℝ] ℂ) (hΛ : ∀ g, ‖Λ g‖ ≤ 1 * ‖g‖) : PG 1 (fun g => Λ g) := by
  refine ⟨Λ.contDiff, fun n => ?_⟩
  have hK1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
  refine ⟨((2 * r + k + 1 : ℕ) : ℝ) ^ n, fun w hw hn g _ => ?_⟩
  obtain ⟨Λ', hΛ', hb⟩ := pb_Dw_clm (by linarith) w (fun x hx g => pb_dirL_le (hw x hx) g)
    Λ 1 zero_le_one hΛ
  rw [hΛ', Real.rpow_one]
  calc ‖Λ' g‖ ≤ 1 * ((2 * r + k + 1 : ℕ) : ℝ) ^ w.length * ‖g‖ := hb g
    _ ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ n * B.gN g := by
      rw [one_mul]
      exact mul_le_mul (pow_le_pow_right₀ hK1 hn) (pb_sup_le_gN g) (norm_nonneg _) (by positivity)

def pbCo (a b : Fin (2 * r + k + 1)) : B.Mat k r →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => g a b, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => by simp }

def pbCc (a b : Fin (2 * r + k + 1)) : B.Mat k r →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => star (g a b), map_add' := fun _ _ => by simp, map_smul' := fun _ _ => by simp }

def pbVar (g : B.Mat k r) : (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) → ℂ :=
  Sum.elim (fun x => g x.1 x.2) (fun x => star (g x.1 x.2))

lemma pb_var (i : (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) :
    PG 1 (fun g : B.Mat k r => pbVar g i) := by
  rcases i with ⟨a, b⟩ | ⟨a, b⟩
  · have e : (fun g : B.Mat k r => pbVar g (Sum.inl (a, b))) = fun g => pbCo a b g := by
      funext g
      simp [pbVar, pbCo] <;> rfl
    rw [e]
    refine pb_clm (pbCo a b) (fun g => ?_)
    have e2 : pbCo a b g = g a b := by simp [pbCo] <;> rfl
    rw [e2, one_mul]
    exact Matrix.norm_entry_le_entrywise_sup_norm g
  · have e : (fun g : B.Mat k r => pbVar g (Sum.inr (a, b))) = fun g => pbCc a b g := by
      funext g
      simp [pbVar, pbCc] <;> rfl
    rw [e]
    refine pb_clm (pbCc a b) (fun g => ?_)
    have e2 : pbCc a b g = star (g a b) := by simp [pbCc] <;> rfl
    rw [e2, one_mul, norm_star]
    exact Matrix.norm_entry_le_entrywise_sup_norm g

lemma pb_pow {e : ℝ} {f : B.Mat k r → ℂ} (hf : PG e f) (m : ℕ) : PG ((m : ℝ) * e) (fun g => f g ^ m) := by
  induction m with
  | zero =>
    have h : PG 0 (fun _ : B.Mat k r => (1 : ℂ)) := pb_const 1
    simpa using h
  | succ m ih =>
    have h := pb_mul ih hf
    have e1 : ((m + 1 : ℕ) : ℝ) * e = (m : ℝ) * e + e := by push_cast; ring
    rw [e1]
    convert h using 1
    funext g
    ring

lemma pb_prod {ι : Type*} (s : Finset ι) (e : ι → ℝ) (F : ι → B.Mat k r → ℂ)
    (hF : ∀ i ∈ s, PG (e i) (F i)) : PG (∑ i ∈ s, e i) (fun g => ∏ i ∈ s, F i g) := by
  classical
  revert hF
  refine Finset.induction_on s ?_ ?_
  · intro _
    have h : PG 0 (fun _ : B.Mat k r => (1 : ℂ)) := pb_const 1
    simpa using h
  · intro a s ha ih hF
    have h1 := hF a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
    rw [Finset.sum_insert ha]
    convert pb_mul h1 h2 using 1
    funext g
    rw [Finset.prod_insert ha]

lemma pb_sum {ι : Type*} (s : Finset ι) {e : ℝ} (F : ι → B.Mat k r → ℂ)
    (hF : ∀ i ∈ s, PG e (F i)) : PG e (fun g => ∑ i ∈ s, F i g) := by
  classical
  revert hF
  refine Finset.induction_on s ?_ ?_
  · intro _
    have h : PG e (fun _ : B.Mat k r => (0 : ℂ)) := pb_zero e
    simpa using h
  · intro a s ha ih hF
    have h1 := hF a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
    convert pb_add h1 h2 using 1
    funext g
    rw [Finset.sum_insert ha]

theorem pb_poly {κ : ℕ} {P : B.Mat k r → ℂ} (hP : IsPolyDeg κ P) : PG (κ : ℝ) P := by
  obtain ⟨q, hq, hPq⟩ := hP
  have hfun : P = fun g => ∑ d ∈ q.support, q.coeff d * ∏ i ∈ d.support, pbVar g i ^ d i := by
    funext g
    rw [hPq g, MvPolynomial.eval_eq]
    rfl
  rw [hfun]
  refine pb_sum q.support (fun d g => q.coeff d * ∏ i ∈ d.support, pbVar g i ^ d i) (fun d hd => ?_)
  have h1 : PG (∑ i ∈ d.support, ((d i : ℕ) : ℝ) * 1) (fun g => ∏ i ∈ d.support, pbVar g i ^ d i) :=
    pb_prod d.support (fun i => ((d i : ℕ) : ℝ) * 1) (fun i g => pbVar g i ^ d i)
      (fun i _ => pb_pow (pb_var i) (d i))
  have h0 : PG 0 (fun _ : B.Mat k r => q.coeff d) := pb_const _
  have h2 := pb_mul h0 h1
  refine pb_mono h2 ?_
  have hdeg : (d.sum fun _ e => e) ≤ κ := (MvPolynomial.le_totalDegree hd).trans hq
  have hs : (∑ i ∈ d.support, ((d i : ℕ) : ℝ) * 1) = ((d.sum fun _ e => e : ℕ) : ℝ) := by
    simp [Finsupp.sum]
  rw [zero_add, hs]
  exact_mod_cast hdeg

end pb2

end PI.UnitaryCorollaryDerivatives
