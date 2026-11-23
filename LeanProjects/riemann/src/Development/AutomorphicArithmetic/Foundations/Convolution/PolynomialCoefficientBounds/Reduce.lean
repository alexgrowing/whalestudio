import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.Generators
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.MatrixEntryAbsSumUnitaryLieCoordinatesSplit

open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

private noncomputable def nrm {ι : Type} (p : MvPolynomial ι ℂ) : ℝ :=
  ∑ α ∈ p.support, ‖p.coeff α‖

private theorem nrm_nonneg {ι : Type} (p : MvPolynomial ι ℂ) : 0 ≤ nrm p :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

private theorem nrm_add {ι : Type} (p q : MvPolynomial ι ℂ) : nrm (p + q) ≤ nrm p + nrm q :=
  (UpperTheory.ConvolutionTheory.FX.coeffL1_submultiplicative_facts ι p q).1

private theorem nrm_mul {ι : Type} (p q : MvPolynomial ι ℂ) : nrm (p * q) ≤ nrm p * nrm q :=
  (UpperTheory.ConvolutionTheory.FX.coeffL1_submultiplicative_facts ι p q).2.1

private theorem nrm_monomial {ι : Type} (a : ι →₀ ℕ) (c : ℂ) :
    nrm (monomial a c : MvPolynomial ι ℂ) = ‖c‖ :=
  (UpperTheory.ConvolutionTheory.FX.coeffL1_submultiplicative_facts ι 0 0).2.2.2.1 a c

private def FXRep {ι B : Type} [Fintype B] (φ : MvPolynomial ι ℂ →ₐ[ℂ] MvPolynomial ι ℂ)
    (m : B → MvPolynomial ι ℂ) (p : MvPolynomial ι ℂ) (d : ℕ) (c : ℝ) : Prop :=
  ∃ G : B → MvPolynomial ι ℂ, p = ∑ β, φ (G β) * m β ∧ ∑ β, nrm (G β) ≤ c ∧ ∀ β, (G β).totalDegree ≤ d

section
variable {ι B : Type} [Fintype B] {φ : MvPolynomial ι ℂ →ₐ[ℂ] MvPolynomial ι ℂ}
  {m : B → MvPolynomial ι ℂ}

private theorem FXRep.mono {p c d e e'} (h : FXRep φ m p e c) (hcd : c ≤ d) (he : e ≤ e') : FXRep φ m p e' d := by
  obtain ⟨G, h1, h2, h3⟩ := h
  exact ⟨G, h1, h2.trans hcd, fun β => (h3 β).trans he⟩

private theorem FXRep.add {p q c d e} (h : FXRep φ m p e c) (h' : FXRep φ m q e d) :
    FXRep φ m (p + q) e (c + d) := by
  obtain ⟨G, h1, h2, h3⟩ := h
  obtain ⟨G', h1', h2', h3'⟩ := h'
  refine ⟨fun β => G β + G' β, ?_, ?_, fun β => (totalDegree_add _ _).trans (max_le (h3 β) (h3' β))⟩
  · rw [h1, h1', ← Finset.sum_add_distrib]
    simp only [map_add, add_mul]
  · refine (Finset.sum_le_sum fun β _ => nrm_add _ _).trans ?_
    rw [Finset.sum_add_distrib]
    linarith

private theorem FXRep.sum {κ : Type} (s : Finset κ) (f : κ → MvPolynomial ι ℂ) (c : κ → ℝ) {e : ℕ}
    (h : ∀ i ∈ s, FXRep φ m (f i) e (c i)) : FXRep φ m (∑ i ∈ s, f i) e (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp, by simp [nrm], by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private theorem FXRep.smul {p c e e'} (g : MvPolynomial ι ℂ) (hg : g.totalDegree ≤ e') (h : FXRep φ m p e c) :
    FXRep φ m (φ g * p) (e' + e) (nrm g * c) := by
  obtain ⟨G, h1, h2, h3⟩ := h
  refine ⟨fun β => g * G β, ?_, ?_, fun β => (totalDegree_mul _ _).trans (add_le_add hg (h3 β))⟩
  · rw [h1, Finset.mul_sum]
    simp only [map_mul, mul_assoc]
  · refine (Finset.sum_le_sum fun β _ => nrm_mul _ _).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left h2 (nrm_nonneg g)

private theorem FXRep.basis (β : B) : FXRep φ m (m β) 0 1 := by
  classical
  refine ⟨fun γ => if γ = β then 1 else 0, ?_, ?_, fun γ => by dsimp only; split_ifs <;> simp⟩
  · rw [Finset.sum_eq_single β] <;> simp +contextual
  · rw [Finset.sum_eq_single β]
    · have := nrm_monomial (0 : ι →₀ ℕ) 1
      simp only [monomial_zero', C_1, norm_one] at this
      simp [this]
    · intro b _ hb
      simp [hb, nrm]
    · simp

private theorem FXRep.mul_left {p c e} (x : MvPolynomial ι ℂ) (K : ℝ) (hK : 0 ≤ K)
    (hx : ∀ β, FXRep φ m (x * m β) 1 K) (h : FXRep φ m p e c) : FXRep φ m (x * p) (e + 1) (K * c) := by
  obtain ⟨G, h1, h2, hd⟩ := h
  have h3 := FXRep.sum Finset.univ _ _ fun β _ => (hx β).smul (G β) (hd β)
  have h4 : x * p = ∑ β, φ (G β) * (x * m β) := by
    rw [h1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun β _ => by ring
  rw [h4]
  refine h3.mono ?_ le_rfl
  rw [← Finset.sum_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left h2 hK

end

private theorem vieta (n : ℕ) (j : Fin n) :
    (X j : MvPolynomial (Fin n) ℂ) ^ n =
      ∑ i : Fin n, C (-(-1) ^ n * (-1) ^ (n - (i + 1)) : ℂ) * esymm (Fin n) ℂ (i + 1) *
        X j ^ (n - (i + 1)) := by
  have h := congrArg (Polynomial.eval (-(X j : MvPolynomial (Fin n) ℂ)))
    (MvPolynomial.prod_C_add_X_eq_sum_esymm ℂ (Fin n))
  rw [Polynomial.eval_prod, Finset.prod_eq_zero (Finset.mem_univ j) (by simp),
    Polynomial.eval_finset_sum, Fintype.card_fin, Finset.sum_range_succ',
    Finset.sum_range] at h
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    esymm_zero, one_mul, Nat.sub_zero] at h
  have h2 : (X j : MvPolynomial (Fin n) ℂ) ^ n = (-1) ^ n * (-X j) ^ n := by
    rw [← mul_pow]; simp
  have h3 := eq_neg_of_add_eq_zero_right h.symm
  rw [h2, h3, mul_neg, ← neg_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [neg_pow (X j : MvPolynomial (Fin n) ℂ)]
  simp only [map_mul, map_neg, map_pow, map_one]
  ring

private theorem prod_update {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (β : ι → Fin n)
    (u : ι) (k : Fin n) :
    (∏ v, (X v : MvPolynomial ι ℂ) ^ (Function.update β u k v : ℕ)) =
      X u ^ (k : ℕ) * ∏ v ∈ Finset.univ.erase u, X v ^ (β v : ℕ) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ u), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hv)]

private theorem step (τ : Type) [Fintype τ] [DecidableEq τ] (n : ℕ) (u : τ × Fin n)
    (β : τ × Fin n → Fin n) :
    FXRep (aeval (fun ti : τ × Fin n => rename (fun j => (ti.1, j)) (esymm (Fin n) ℂ (ti.2 + 1))))
      (fun β : τ × Fin n → Fin n => ∏ u, (X u : MvPolynomial (τ × Fin n) ℂ) ^ (β u : ℕ))
      (X u * ∏ v, X v ^ (β v : ℕ)) 1 ((n : ℝ) + 1) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ u), ← mul_assoc, ← pow_succ']
  by_cases h : (β u : ℕ) + 1 < n
  · have := prod_update β u ⟨_, h⟩
    simp only at this
    rw [← this]
    exact (FXRep.basis _).mono (by linarith [Nat.cast_nonneg (α := ℝ) n]) (Nat.zero_le _)
  · have hn : (β u : ℕ) + 1 = n := by have := (β u).2; omega
    have hv := congrArg (rename (fun j => (u.1, j))) (vieta n u.2)
    simp only [map_pow, rename_X, map_sum, map_mul, Prod.mk.eta, rename_C] at hv
    rw [hn, hv, Finset.sum_mul]
    have key := FXRep.sum (φ := aeval (fun ti : τ × Fin n =>
        rename (fun j => (ti.1, j)) (esymm (Fin n) ℂ (ti.2 + 1))))
      (m := fun β : τ × Fin n → Fin n => ∏ u, (X u : MvPolynomial (τ × Fin n) ℂ) ^ (β u : ℕ))
      (Finset.univ : Finset (Fin n)) _ _ fun i _ =>
        (FXRep.basis (Function.update β u i.rev)).smul
          (e' := 1) (monomial (Finsupp.single (u.1, i) 1) (-(-1) ^ n * (-1) ^ (n - (i + 1)) : ℂ))
          ((totalDegree_monomial_le _ _).trans (by simp))
    refine FXRep.mono (c := ∑ i : Fin n, _) (Eq.mpr (congrArg (FXRep _ _ · _ _) ?_) key) ?_ le_rfl
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [prod_update, Fin.val_rev]
      rw [aeval_monomial, Finsupp.prod_single_index (by simp), pow_one, algebraMap_eq]
      simp only [mul_assoc, map_mul, map_pow]
    · simp only [nrm_monomial]
      simp

theorem UpperTheory.ConvolutionTheory.FX.reduce :
    ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (n : ℕ), ∃ K : ℝ, 1 ≤ K ∧ ∀ α : τ × Fin n →₀ ℕ, ∃ G : (τ × Fin n → Fin n) → MvPolynomial (τ × Fin n) ℂ, (monomial α (1 : ℂ) = ∑ β, aeval blockE (G β) * ∏ u, X u ^ (β u : ℕ)) ∧ ∑ β, l1 (G β) ≤ K ^ α.degree ∧ ∀ β, (G β).totalDegree ≤ α.degree := by
  intro τ _ _ n
  have hK : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine ⟨(n : ℝ) + 1, by linarith, fun α => ?_⟩
  change FXRep (aeval (fun ti : τ × Fin n =>
      rename (fun j => (ti.1, j)) (esymm (Fin n) ℂ (ti.2 + 1))))
    (fun β : τ × Fin n → Fin n => ∏ u, (X u : MvPolynomial (τ × Fin n) ℂ) ^ (β u : ℕ))
    (monomial α 1) α.degree (((n : ℝ) + 1) ^ α.degree)
  induction α using Finsupp.induction with
  | zero =>
    have := FXRep.basis (φ := aeval (fun ti : τ × Fin n =>
        rename (fun j => (ti.1, j)) (esymm (Fin n) ℂ (ti.2 + 1))))
      (m := fun β : τ × Fin n → Fin n => ∏ u, (X u : MvPolynomial (τ × Fin n) ℂ) ^ (β u : ℕ))
      (fun u => ⟨0, u.2.pos⟩)
    simpa using this
  | single_add a b f _ _ ih =>
    rw [monomial_single_add, map_add, Finsupp.degree_single, pow_add]
    clear * - ih hK
    induction b with
    | zero => simpa using ih
    | succ b ihb =>
      rw [pow_succ', pow_succ', mul_assoc, mul_assoc]
      exact (ihb.mul_left _ _ (by linarith) (step τ n a)).mono le_rfl (by omega)
