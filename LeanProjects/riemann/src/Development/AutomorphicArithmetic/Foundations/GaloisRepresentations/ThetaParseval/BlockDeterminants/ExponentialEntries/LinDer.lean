import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

noncomputable section

open MvPolynomial GlobalTheory.RealLift

namespace UpperTheory.TP.RP

theorem hasSum_cauchy {a b : ℕ → ℂ} {A B : ℂ} (ha : HasSum a A) (hb : HasSum b B) :
    HasSum (fun n => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, a kl.1 * b kl.2) (A * B) := by
  have hna : Summable fun n => ‖a n‖ := ha.summable.norm
  have hnb : Summable fun n => ‖b n‖ := hb.summable.norm
  have key := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hna hnb
  rw [ha.tsum_eq, hb.tsum_eq] at key
  rw [key]
  exact (summable_norm_sum_mul_antidiagonal_of_summable_norm hna hnb).of_norm.hasSum

theorem inv_fact_choose (i j : ℕ) :
    ((i + j).factorial : ℂ)⁻¹ * ((i + j).choose i : ℂ) = (i.factorial : ℂ)⁻¹ * (j.factorial : ℂ)⁻¹ := by
  have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right i j)
  rw [Nat.add_sub_cancel_left] at h
  have h' : ((i + j).choose i : ℂ) * i.factorial * j.factorial = (i + j).factorial := by exact_mod_cast h
  have hi : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have hj : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have hn : ((i + j).factorial : ℂ) ≠ 0 := by exact_mod_cast (i + j).factorial_ne_zero
  field_simp
  linear_combination h'

theorem isExp_add_smul {V : Type} [AddCommGroup V] [Module ℂ V] {L U : Module.End ℂ V} (h : IsExp L U) (c : ℂ) :
    IsExp (L + c • 1) (Complex.exp c • U) := by
  intro v l
  have hc : HasSum (fun n : ℕ => (n.factorial : ℂ)⁻¹ * c ^ n) (Complex.exp c) := by
    have := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℂ) c
    rw [← Complex.exp_eq_exp_ℂ] at this
    simpa [div_eq_inv_mul] using this
  have key := hasSum_cauchy (h v l) hc
  have hcomm : Commute L (c • (1 : Module.End ℂ V)) := (Commute.one_right L).smul_right c
  have hval : l ((Complex.exp c • U) v) = l (U v) * Complex.exp c := by
    simp [mul_comm]
  rw [hval]
  convert key using 2 with n
  rw [hcomm.add_pow', LinearMap.sum_apply, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  rintro ⟨i, j⟩ hij
  obtain rfl : i + j = n := by simpa using hij
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  simp only [smul_pow, one_pow, mul_smul_comm, mul_one, LinearMap.smul_apply, map_smul, smul_eq_mul]
  linear_combination (c ^ j * l ((L ^ i) v)) * inv_fact_choose i j

theorem dual_eq_top_of_sep {M : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (W : Submodule ℂ (Module.Dual ℂ M)) (h : ∀ x : M, (∀ f ∈ W, f x = 0) → x = 0) : W = ⊤ := by
  have h1 : W.dualCoannihilator = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    exact h x fun f hf => (Submodule.mem_dualCoannihilator _).1 hx f hf
  have h2 := Subspace.dualCoannihilator_dualAnnihilator_eq (W := W)
  rw [h1, Submodule.dualAnnihilator_bot] at h2
  exact h2.symm

theorem hasSum_of_mem_span {M : Type} [AddCommGroup M] [Module ℂ M] (S : Set (Module.Dual ℂ M)) (w : ℕ → M) (u : M)
    (a : ℕ → ℂ) (hS : ∀ f ∈ S, HasSum (fun n => a n * f (w n)) (f u)) :
    ∀ f ∈ Submodule.span ℂ S, HasSum (fun n => a n * f (w n)) (f u) := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf => exact hS f hf
  | zero => simpa using hasSum_zero
  | add f g _ _ hf hg => simpa [mul_add] using hf.add hg
  | smul c f _ hf => simpa [mul_left_comm] using hf.mul_left c

theorem isExp_of_sep {V : Type} [AddCommGroup V] [Module ℂ V] {L U : Module.End ℂ V} (hL : LocFin L)
    (E : Set (V →ₗ[ℂ] ℂ)) (hE : ∀ v, (∀ e ∈ E, e v = 0) → v = 0)
    (h : ∀ e ∈ E, ∀ v, HasSum (fun n : ℕ => (n.factorial : ℂ)⁻¹ * e ((L ^ n) v)) (e (U v))) : IsExp L U := by
  intro v l
  obtain ⟨N', hfd, hw, hu⟩ : ∃ N' : Submodule ℂ V, FiniteDimensional ℂ N' ∧ (∀ n, (L ^ n) v ∈ N') ∧ U v ∈ N' := by
    obtain ⟨N, hNf, hvN, hst⟩ := hL v
    have hw : ∀ n, (L ^ n) v ∈ N := by
      intro n
      induction n with
      | zero => simpa using hvN
      | succ n ih => rw [pow_succ', Module.End.mul_apply]; exact hst _ ih
    exact ⟨N ⊔ Submodule.span ℂ {U v}, Submodule.finiteDimensional_sup _ _, fun n => Submodule.mem_sup_left (hw n),
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)⟩
  have hW : Submodule.span ℂ ((fun e : V →ₗ[ℂ] ℂ => e ∘ₗ N'.subtype) '' E) = ⊤ := by
    refine dual_eq_top_of_sep _ fun x hx => Subtype.ext (hE _ fun e he => ?_)
    exact hx (e ∘ₗ N'.subtype) (Submodule.subset_span ⟨e, he, rfl⟩)
  have key := hasSum_of_mem_span ((fun e : V →ₗ[ℂ] ℂ => e ∘ₗ N'.subtype) '' E)
    (fun n => (⟨(L ^ n) v, hw n⟩ : N')) (⟨U v, hu⟩ : N') (fun n => (n.factorial : ℂ)⁻¹) (by
      rintro _ ⟨e, he, rfl⟩
      exact h e he v) (l ∘ₗ N'.subtype) (hW ▸ Submodule.mem_top)
  exact key

section Der

variable {σ : Type} [Fintype σ] [DecidableEq σ]

theorem der_pow_mul (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) (n : ℕ) (P Q : MvPolynomial σ ℂ) :
    ((D : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ) ^ n) (P * Q) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, n.choose ij.1 •
        (((D : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ) ^ ij.1) P *
          ((D : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ) ^ ij.2) Q) := by
  set L : Module.End ℂ (MvPolynomial σ ℂ) := (D : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ) with hLdef
  have hL : ∀ a b, L (a * b) = a * L b + L a * b := by
    intro a b
    have := D.leibniz a b
    simp only [smul_eq_mul] at this
    simp [hLdef, this, mul_comm]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_antidiagonal_choose_succ_nsmul (fun i j => (L ^ i) P * (L ^ j) Q) n, pow_succ',
      Module.End.mul_apply, ih, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    rintro ⟨i, j⟩ hij
    obtain rfl : i + j = n := by simpa using hij
    have hs : (i + j).choose j = (i + j).choose i := Nat.choose_symm_add.symm
    simp only [map_nsmul, hL, pow_succ', Module.End.mul_apply, hs, smul_add]

theorem eval_series_mul (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (U : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ) (z : σ → ℂ) {P Q : MvPolynomial σ ℂ}
    (hP : HasSum (fun n : ℕ => (n.factorial : ℂ)⁻¹ *
      eval z (((D : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ) ^ n) P)) (eval z (U P)))
    (hQ : HasSum (fun n : ℕ => (n.factorial : ℂ)⁻¹ *
      eval z (((D : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ) ^ n) Q)) (eval z (U Q))) :
    HasSum (fun n : ℕ => (n.factorial : ℂ)⁻¹ *
      eval z (((D : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ) ^ n) (P * Q))) (eval z (U (P * Q))) := by
  have key := hasSum_cauchy hP hQ
  rw [map_mul, map_mul]
  convert key using 2 with n
  rw [der_pow_mul, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  rintro ⟨i, j⟩ hij
  obtain rfl : i + j = n := by simpa using hij
  simp only [nsmul_eq_mul, map_mul, map_natCast]
  linear_combination (eval z (((D : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ) ^ i) P) *
    eval z (((D : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ) ^ j) Q)) * inv_fact_choose i j

theorem der_sum_apply {ι : Type} (s : Finset ι) (g : ι → Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (f : MvPolynomial σ ℂ) : (∑ i ∈ s, g i) f = ∑ i ∈ s, g i f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

def linDer (T : Matrix σ σ ℂ) : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ) :=
  ∑ l, ∑ l', (C (T l l') * X l : MvPolynomial σ ℂ) • pderiv l'

theorem linDer_apply (T : Matrix σ σ ℂ) (f : MvPolynomial σ ℂ) :
    linDer T f = ∑ l, ∑ l', T l l' • (X l * pderiv l' f) := by
  simp [linDer, der_sum_apply, smul_eq_C_mul, mul_assoc]

theorem linDer_X (T : Matrix σ σ ℂ) (i : σ) : linDer T (X i) = ∑ l, T l i • (X l : MvPolynomial σ ℂ) := by
  simp [linDer_apply, pderiv_X, Pi.single_apply]

theorem linDer_pow_X (T : Matrix σ σ ℂ) (n : ℕ) (i : σ) :
    (((linDer T : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ) ^ n)
      (X i) = ∑ l, (T ^ n) l i • (X l : MvPolynomial σ ℂ) := by
  induction n with
  | zero => simp [Matrix.one_apply, ite_smul]
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_sum, pow_succ']
    simp only [map_smul, Derivation.coeFn_coe, linDer_X, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => by rw [mul_comm]

theorem linDer_locFin (T : Matrix σ σ ℂ) :
    LocFin ((linDer T : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ) := by
  have hst0 : ∀ y ∈ Submodule.span ℂ (Set.range (X : σ → MvPolynomial σ ℂ)),
      linDer T y ∈ Submodule.span ℂ (Set.range (X : σ → MvPolynomial σ ℂ)) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      rw [linDer_X]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
    | zero => simp
    | add a b _ _ ha hb => simpa using Submodule.add_mem _ ha hb
    | smul c a _ ha => simpa using Submodule.smul_mem _ c ha
  have hfd0 : (Submodule.span ℂ (Set.range (X : σ → MvPolynomial σ ℂ))).FG :=
    Submodule.fg_span (Set.finite_range _)
  intro v
  induction v using MvPolynomial.induction_on with
  | C a =>
    refine ⟨Submodule.span ℂ {C a}, inferInstance, Submodule.mem_span_singleton_self _, fun y hy => ?_⟩
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have h0 : linDer T (C a) = 0 := (linDer T).map_algebraMap a
    simp [h0]
  | add p q hp hq =>
    obtain ⟨N₁, f₁, m₁, s₁⟩ := hp
    obtain ⟨N₂, f₂, m₂, s₂⟩ := hq
    refine ⟨N₁ ⊔ N₂, Submodule.finiteDimensional_sup _ _, Submodule.add_mem_sup m₁ m₂, fun y hy => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
    rw [map_add]
    exact Submodule.add_mem_sup (s₁ a ha) (s₂ b hb)
  | mul_X p i hp =>
    obtain ⟨N, f, m, s⟩ := hp
    refine ⟨N * Submodule.span ℂ (Set.range (X : σ → MvPolynomial σ ℂ)),
      Module.Finite.iff_fg.2 (Submodule.FG.mul (Module.Finite.iff_fg.1 f) hfd0),
      Submodule.mul_mem_mul m (Submodule.subset_span ⟨i, rfl⟩), fun y hy => ?_⟩
    induction hy using Submodule.mul_induction_on' with
    | mem_mul_mem a ha b hb =>
      have hl := (linDer T).leibniz a b
      simp only [smul_eq_mul] at hl
      simp only [Derivation.coeFn_coe, hl]
      rw [mul_comm b]
      exact Submodule.add_mem _ (Submodule.mul_mem_mul ha (hst0 b hb)) (Submodule.mul_mem_mul (s a ha) hb)
    | add a _ b _ ha hb =>
      rw [map_add]
      exact Submodule.add_mem _ ha hb

def evL (z : σ → ℂ) : MvPolynomial σ ℂ →ₗ[ℂ] ℂ where
  toFun := eval z
  map_add' := by simp
  map_smul' := by simp [smul_eval]

def linSub (G : Matrix σ σ ℂ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
  aeval fun i => ∑ l, G l i • (X l : MvPolynomial σ ℂ)

theorem linDer_eval_series (T G : Matrix σ σ ℂ)
    (hG : ∀ i j, HasSum (fun n : ℕ => (n.factorial : ℂ)⁻¹ * (T ^ n) i j) (G i j)) (z : σ → ℂ)
    (P : MvPolynomial σ ℂ) :
    HasSum (fun n : ℕ => (n.factorial : ℂ)⁻¹ *
      eval z ((((linDer T : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) :
        MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ) ^ n) P)) (eval z (linSub G P)) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h0 : linDer T (C a) = 0 := (linDer T).map_algebraMap a
    have hv : linSub G (C a) = C a := by simp [linSub, algebraMap_eq]
    rw [hv]
    convert hasSum_single (f := fun n : ℕ => (n.factorial : ℂ)⁻¹ *
      eval z ((((linDer T : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) :
        MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ) ^ n) (C a))) 0 ?_ using 1
    · simp
    · intro n hn
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      simp [pow_succ, Module.End.mul_apply, h0]
  | add p q hp hq =>
    simpa [mul_add, map_add] using hp.add hq
  | mul_X p i hp =>
    refine eval_series_mul _ _ z hp ?_
    have hv : eval z (linSub G (X i)) = ∑ l, G l i * z l := by
      simp [linSub, smul_eval]
    rw [hv]
    have hs := hasSum_sum (s := Finset.univ) fun l _ => (hG l i).mul_right (z l)
    have heq : (fun n : ℕ => (n.factorial : ℂ)⁻¹ *
        eval z ((((linDer T : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) :
          MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ) ^ n) (X i))) =
        fun b : ℕ => ∑ l, (b.factorial : ℂ)⁻¹ * (T ^ b) l i * z l := by
      funext n
      rw [linDer_pow_X, map_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by simp [smul_eval, mul_assoc]
    rw [heq]
    exact hs

theorem linDer_isExp (T G : Matrix σ σ ℂ)
    (hG : ∀ i j, HasSum (fun n : ℕ => (n.factorial : ℂ)⁻¹ * (T ^ n) i j) (G i j)) :
    IsExp ((linDer T : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ)
      (linSub G).toLinearMap := by
  refine isExp_of_sep (linDer_locFin T) (Set.range evL) (fun v hv => ?_) ?_
  · exact MvPolynomial.funext fun z => by simpa [evL] using hv (evL z) ⟨z, rfl⟩
  · rintro _ ⟨z, rfl⟩ v
    exact linDer_eval_series T G hG z v

open scoped Matrix.Norms.Operator in

theorem hasSum_exp_entry (Y : Matrix σ σ ℂ) (a b : σ) :
    HasSum (fun n : ℕ => (n.factorial : ℂ)⁻¹ * (Y ^ n) a b) (NormedSpace.exp Y a b) := by
  have key := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Y
  exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ a b)).hasSum key

end Der

section Kron

open scoped Kronecker

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem kron_left_pow (Y : Matrix α α ℂ) (n : ℕ) :
    (Y ⊗ₖ (1 : Matrix β β ℂ)) ^ n = (Y ^ n) ⊗ₖ (1 : Matrix β β ℂ) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, ← Matrix.mul_kronecker_mul, pow_succ, mul_one]

theorem linDer_kron_left_isExp (Y : Matrix α α ℂ) :
    IsExp ((linDer (Y ⊗ₖ (1 : Matrix β β ℂ)) :
        Derivation ℂ (MvPolynomial (α × β) ℂ) (MvPolynomial (α × β) ℂ)) :
          MvPolynomial (α × β) ℂ →ₗ[ℂ] MvPolynomial (α × β) ℂ)
      (linSub (NormedSpace.exp Y ⊗ₖ (1 : Matrix β β ℂ))).toLinearMap := by
  refine linDer_isExp _ _ fun i j => ?_
  simp only [kron_left_pow, Matrix.kroneckerMap_apply]
  simpa [mul_assoc] using (hasSum_exp_entry Y i.1 j.1).mul_right ((1 : Matrix β β ℂ) i.2 j.2)

end Kron

open Formalism.BasicNotions.TH in

theorem omAct_definite (n d : ℕ) (T : Matrix (Ln n 0 d 0) (Ln n 0 d 0) ℂ) :
    omAct n 0 d 0 T = ((linDer T : Derivation ℂ (Pol n 0 d 0) (Pol n 0 d 0)) : Pol n 0 d 0 →ₗ[ℂ] Pol n 0 d 0) +
      ((1 / 2 : ℂ) * T.trace) • 1 := by
  have hpos : ∀ l : Ln n 0 d 0, linePos l = true := by
    rintro ⟨a | a, c | c⟩
    · rfl
    · exact c.elim0
    · exact a.elim0
    · exact a.elim0
  have hE : ∀ (l l' : Ln n 0 d 0) (f : Pol n 0 d 0),
      omE l l' f = X l * pderiv l' f + (if l = l' then (1 / 2 : ℂ) • f else 0) := by
    intro l l' f
    by_cases h : l = l' <;> simp [omE, raiB, lowB, hpos, h]
  refine LinearMap.ext fun f => ?_
  have htr : ∑ l, ∑ l', T l l' • (if l = l' then (1 / 2 : ℂ) • f else 0) = ((1 / 2 : ℂ) * T.trace) • f := by
    simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.trace, Matrix.diag_apply,
      smul_smul, Finset.mul_sum, Finset.sum_smul, mul_comm]
  rw [omAct_apply]
  simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, hE, smul_add, Finset.sum_add_distrib,
    Derivation.coeFn_coe, linDer_apply, Module.End.one_apply, htr]

end UpperTheory.TP.RP
