import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Smooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL

open Matrix Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory

private theorem list_prod_ofFn_sum_eq_sum_prod {A : Type*} [Semiring A] {ι : Type*} [Fintype ι] :
    ∀ {t : ℕ} (f : Fin t → ι → A),
      (List.ofFn fun k => ∑ i, f k i).prod = ∑ c : Fin t → ι, (List.ofFn fun k => f k (c k)).prod
  | 0, f => by simp
  | t + 1, f => by
    rw [List.ofFn_succ, List.prod_cons, list_prod_ofFn_sum_eq_sum_prod (fun k => f k.succ), Finset.sum_mul_sum,
      ← (Fin.consEquiv fun _ => ι).sum_comp, Fintype.sum_prod_type]
    simp [Fin.consEquiv, List.ofFn_succ]

private theorem list_prod_ofFn_smul_eq_prod_smul {A : Type*} [Semiring A] [Algebra ℂ A] :
    ∀ {t : ℕ} (r : Fin t → ℂ) (x : Fin t → A),
      (List.ofFn fun k => r k • x k).prod = (∏ k, r k) • (List.ofFn x).prod
  | 0, r, x => by simp
  | t + 1, r, x => by
    rw [List.ofFn_succ, List.prod_cons, list_prod_ofFn_smul_eq_prod_smul (fun k => r k.succ) (fun k => x k.succ),
      smul_mul_smul_comm, Fin.prod_univ_succ, List.ofFn_succ (f := x), List.prod_cons]

private theorem Tm_conj_eq_sum_conj_Tm {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) (v : ℂ) (a b : Fin n) :
    Formalism.REAL.Tm (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) v a b =
      ∑ c, ∑ d, (P c a * Q b d) • Formalism.REAL.Tm E v c d := by
  have h1 : ∑ c, P c a * Q b c = if a = b then 1 else 0 := by
    have := congrFun (congrFun hQP b) a
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [show (∑ c, P c a * Q b c) = ∑ c, Q b c * P c a from
      Finset.sum_congr rfl fun c _ => mul_comm _ _, this]
    by_cases h : a = b <;> simp [h, eq_comm]
  simp only [Formalism.REAL.Tm, smul_add, Finset.sum_add_distrib, smul_ite, smul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  congr 1
  rw [← Finset.sum_smul, h1]
  by_cases h : a = b <;> simp [h]

private theorem sum_sign_mul_prod_eq_zero_of_not_bijective {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (r : Fin n → Fin n)
    (hr : ¬ Function.Bijective r) :
    ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, P (r k) (σ k) = 0 := by
  have := Matrix.det_mul_aux (M := Pᵀ) (N := Matrix.of fun _ _ => (1 : ℂ)) hr
  simpa [Matrix.transpose_apply] using this

private theorem sum_sign_mul_prod_perm_eq_sign_mul_det {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (τ : Equiv.Perm (Fin n)) :
    ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, P (τ k) (σ k) =
      ((Equiv.Perm.sign τ : ℤ) : ℂ) * Matrix.det P := by
  rw [← Matrix.det_transpose, Matrix.det_apply', Finset.mul_sum]
  conv_lhs => rw [← Equiv.sum_comp (Equiv.mulRight τ)]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  simp only [Equiv.coe_mulRight, Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul, Equiv.Perm.coe_mul,
    Function.comp_apply, Matrix.transpose_apply]
  rw [show (∏ k, P (τ k) (ρ (τ k))) = ∏ j, P j (ρ j) from Equiv.prod_comp τ (fun j => P j (ρ j))]
  ring

private theorem sum_fun_eq_sum_perm_of_eq_zero_of_not_bijective {M : Type*} [AddCommMonoid M] {n : ℕ} (g : (Fin n → Fin n) → M)
    (h : ∀ r, ¬ Function.Bijective r → g r = 0) :
    ∑ r, g r = ∑ τ : Equiv.Perm (Fin n), g τ := by
  let e : Equiv.Perm (Fin n) ↪ (Fin n → Fin n) := ⟨fun τ => τ, DFunLike.coe_injective⟩
  rw [show (∑ τ : Equiv.Perm (Fin n), g τ) = ∑ r ∈ Finset.univ.map e, g r from
    (Finset.sum_map Finset.univ e g).symm]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro r _ hr
  apply h r
  intro hb
  exact hr (Finset.mem_map.2 ⟨Equiv.ofBijective r hb, Finset.mem_univ _, rfl⟩)

private theorem qminor_eq_zero_of_not_bijective {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (hE : Formalism.REAL.GlRel E) (u : ℂ) (s : Fin n → Fin n) (hs : ¬ Function.Bijective s) :
    Formalism.REAL.qminor E id s u = 0 := by
  have hni : ¬ Function.Injective s := fun hi => hs (Finite.injective_iff_bijective.mp hi)
  obtain ⟨p, q, hsq, hpq⟩ : ∃ p q, s p = s q ∧ p ≠ q := by
    simp only [Function.Injective, not_forall] at hni
    obtain ⟨p, q, h1, h2⟩ := hni
    exact ⟨p, q, h1, h2⟩
  have hsw : s ∘ Equiv.swap p q = s := by
    funext i
    simp only [Function.comp_apply]
    rcases eq_or_ne i p with rfl | hip
    · simp [hsq]
    rcases eq_or_ne i q with rfl | hiq
    · simp [hsq]
    · rw [Equiv.swap_apply_of_ne_of_ne hip hiq]
  have h := Formalism.REAL.qSkewCol A n n E hE id s (Equiv.swap p q) u
  rw [hsw, Equiv.Perm.sign_swap hpq] at h
  set x := Formalism.REAL.qminor E id s u
  have h2 : x + x = 0 := by
    nth_rewrite 2 [h]
    simp
  calc x = (1 / 2 : ℂ) • (x + x) := by rw [← two_smul ℂ x, smul_smul]; norm_num
    _ = 0 := by rw [h2, smul_zero]

private theorem qdet_conj_eq_qdet_of_mul_eq_one {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (hE : Formalism.REAL.GlRel E) (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) (hPQ : P * Q = 1)
    (u : ℂ) :
    Formalism.REAL.qdet (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) u = Formalism.REAL.qdet E u := by
  classical
  have hsg : ∀ (z : ℤ) (x : A), (z : A) * x = (z : ℂ) • x := fun z x => by
    rw [Algebra.smul_def, map_intCast]
  have ha : ∀ σ : Equiv.Perm (Fin n),
      (List.ofFn fun k : Fin n => Formalism.REAL.Tm (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d)
        (u - (k : ℂ)) (id (σ k)) (id k)).prod =
        ∑ r : Fin n → Fin n, ∑ s : Fin n → Fin n, (∏ k, (P (r k) (σ k) * Q k (s k))) •
          (List.ofFn fun k : Fin n => Formalism.REAL.Tm E (u - (k : ℂ)) (r k) (s k)).prod := by
    intro σ
    simp only [id, Tm_conj_eq_sum_conj_Tm E P Q hQP]
    rw [list_prod_ofFn_sum_eq_sum_prod (fun k c => ∑ d, (P c (σ k) * Q k d) • Formalism.REAL.Tm E (u - (k : ℂ)) c d)]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [list_prod_ofFn_sum_eq_sum_prod (fun k d => (P (r k) (σ k) * Q k d) • Formalism.REAL.Tm E (u - (k : ℂ)) (r k) d)]
    refine Finset.sum_congr rfl fun s _ => ?_
    exact list_prod_ofFn_smul_eq_prod_smul (fun k => P (r k) (σ k) * Q k (s k))
      (fun k => Formalism.REAL.Tm E (u - (k : ℂ)) (r k) (s k))
  have hq : ∀ s : Fin n → Fin n, Formalism.REAL.qminor E id s u =
      ∑ τ : Equiv.Perm (Fin n), ((Equiv.Perm.sign τ : ℤ) : ℂ) •
        (List.ofFn fun k : Fin n => Formalism.REAL.Tm E (u - (k : ℂ)) (τ k) (s k)).prod := by
    intro s
    unfold Formalism.REAL.qminor
    exact Finset.sum_congr rfl fun τ _ => hsg _ _
  have hs : ∀ s : Fin n → Fin n,
      ∑ r : Fin n → Fin n, (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ k, (P (r k) (σ k) * Q k (s k))) •
          (List.ofFn fun k : Fin n => Formalism.REAL.Tm E (u - (k : ℂ)) (r k) (s k)).prod =
        (∏ k, Q k (s k)) • (Matrix.det P • Formalism.REAL.qminor E id s u) := by
    intro s
    have hD : ∀ r : Fin n → Fin n, (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ k, (P (r k) (σ k) * Q k (s k))) =
          (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, P (r k) (σ k)) *
            ∏ k, Q k (s k) := by
      intro r
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun σ _ => by rw [Finset.prod_mul_distrib, mul_assoc]
    simp_rw [hD]
    rw [sum_fun_eq_sum_perm_of_eq_zero_of_not_bijective _ (fun r hr => by rw [sum_sign_mul_prod_eq_zero_of_not_bijective P r hr, zero_mul, zero_smul])]
    simp_rw [sum_sign_mul_prod_perm_eq_sign_mul_det P]
    rw [hq s, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [smul_smul, smul_smul]
    congr 1
    ring
  have hL : Formalism.REAL.qdet (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) u =
      ∑ s : Fin n → Fin n, (∏ k, Q k (s k)) • (Matrix.det P • Formalism.REAL.qminor E id s u) := by
    have step : Formalism.REAL.qdet (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) u =
        ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : A) *
          ∑ r : Fin n → Fin n, ∑ s : Fin n → Fin n, (∏ k, (P (r k) (σ k) * Q k (s k))) •
            (List.ofFn fun k : Fin n => Formalism.REAL.Tm E (u - (k : ℂ)) (r k) (s k)).prod := by
      unfold Formalism.REAL.qdet Formalism.REAL.qminor
      exact Finset.sum_congr rfl fun σ _ => by rw [ha σ]
    rw [step]
    simp_rw [← hs]
    simp only [Finset.sum_smul, Finset.mul_sum, Finset.smul_sum, hsg, smul_smul]
    first
      | exact Finset.sum_comm
      | exact Eq.trans Finset.sum_comm (Finset.sum_congr rfl fun r _ => Finset.sum_comm)
      | exact Eq.trans Finset.sum_comm (Eq.trans (Finset.sum_congr rfl fun r _ => Finset.sum_comm) Finset.sum_comm)
  have hperm : ∀ τ : Equiv.Perm (Fin n),
      Formalism.REAL.qminor E id τ u = ((Equiv.Perm.sign τ : ℤ) : ℂ) • Formalism.REAL.qdet E u := by
    intro τ
    have h := Formalism.REAL.qSkewCol A n n E hE id id τ u
    rw [hsg] at h
    exact h
  have hdetQ : ∑ τ : Equiv.Perm (Fin n), ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ k, Q k (τ k) =
      Matrix.det Q := by
    rw [← Matrix.det_transpose, Matrix.det_apply']
    rfl
  have hscal : ∑ τ : Equiv.Perm (Fin n), (∏ k, Q k (τ k)) *
      (Matrix.det P * ((Equiv.Perm.sign τ : ℤ) : ℂ)) = 1 := by
    rw [show (1 : ℂ) = Matrix.det P * Matrix.det Q by rw [← Matrix.det_mul, hPQ, Matrix.det_one],
      ← hdetQ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun τ _ => by ring
  rw [hL, sum_fun_eq_sum_perm_of_eq_zero_of_not_bijective _ (fun s hs => by rw [qminor_eq_zero_of_not_bijective E hE u s hs, smul_zero, smul_zero])]
  simp_rw [hperm, smul_smul]
  rw [← Finset.sum_smul, hscal, one_smul]

theorem capelli_transport_conj : PI.UnitaryGroupMassFormula.CapelliEig.CapTransport := by
  intro n ε E _ _ H P Q F u g hQP hPQ hH hF hg
  have hx : Formalism.REAL.inUJ ε (P * g * Q) := Formalism.QuantumDeterminants.ioh_inUJ ε H P Q g hPQ hH hg
  obtain ⟨x₀, hx₀⟩ := Formalism.QuantumDeterminants.io_rep_mk hF
  have hA := Formalism.QuantumDeterminants.ioh_qminor_rep (Formalism.QuantumDeterminants.ioh_repr (ε := ε) (E := E) P Q) id id u hx₀
  have hB := Formalism.QuantumDeterminants.io_qminor_rep (ε := ε) id id u hx₀
  have hkey : Formalism.REAL.qminor (Formalism.QuantumDeterminants.iohE ε E P Q) id id u =
      Formalism.REAL.qminor (Formalism.QuantumDeterminants.ioE ε E) id id u :=
    qdet_conj_eq_qdet_of_mul_eq_one (Formalism.QuantumDeterminants.ioE ε E) (Formalism.QuantumDeterminants.io_gl ε E) P Q hQP hPQ u
  have h1 := Formalism.QuantumDeterminants.ioh_qminor ε H P Q hQP hPQ hH (id : Fin n → Fin n) id u F g
  show Formalism.QuantumDeterminants.qminorOp (Formalism.QuantumDeterminants.EabH H) id id u F g =
    Formalism.QuantumDeterminants.qminorOp (Formalism.REAL.EabV ε) id id u (fun x => F (Q * x * P)) (P * g * Q)
  rw [h1, hA _ hx, hB _ hx, hkey]

end GlobalTheory
