import ReciprocityTheory.DualLattices.FischerAdjointStatement

noncomputable section

open MvPolynomial Matrix Finset

namespace ReciprocityTheory.PGsh

section General

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

theorem deriv_finsetProd {ι : Type*} [DecidableEq ι] (D : Derivation R A A) (t : Finset ι)
    (P : ι → A) :
    D (∏ k ∈ t, P k) = ∑ k₀ ∈ t, ∏ k ∈ t, (if k = k₀ then D (P k) else P k) := by
  induction t using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
    have h1 : ∏ k ∈ t, (if k = a then D (P k) else P k) = ∏ k ∈ t, P k :=
      Finset.prod_congr rfl fun k hk => if_neg fun h => ha (by rw [← h]; exact hk)
    have h2 : ∀ k₀ ∈ t, ∏ k ∈ insert a t, (if k = k₀ then D (P k) else P k) =
        P a * ∏ k ∈ t, (if k = k₀ then D (P k) else P k) := fun k₀ hk₀ => by
      rw [Finset.prod_insert ha, if_neg fun h => ha (by rw [h]; exact hk₀)]
    rw [Finset.prod_insert ha, Derivation.leibniz, ih, Finset.sum_insert ha,
      Finset.prod_insert ha, if_pos (rfl : a = a), h1, Finset.sum_congr rfl h2,
      smul_eq_mul, smul_eq_mul, Finset.mul_sum]
    ring

theorem deriv_finsetProd_eq_zero {ι : Type*} [DecidableEq ι] (D : Derivation R A A) (t : Finset ι)
    (P : ι → A) (h : ∀ k ∈ t, D (P k) = 0) : D (∏ k ∈ t, P k) = 0 := by
  rw [deriv_finsetProd]
  exact Finset.sum_eq_zero fun k₀ hk₀ => Finset.prod_eq_zero hk₀ (by simp [h k₀ hk₀])

theorem leibniz_ofFn {m s : ℕ} (ds : Fin m → Derivation R A A) (P : Fin s → A) :
    (List.ofFn fun i => (ds i : A →ₗ[R] A)).prod (∏ k, P k) =
      ∑ φ : Fin m → Fin s,
        ∏ k, (List.ofFn fun i => if φ i = k then (ds i : A →ₗ[R] A) else 1).prod (P k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hce : ∀ x : Fin s × (Fin m → Fin s),
        (Fin.consEquiv fun _ => Fin s) x = Fin.cons x.1 x.2 := fun x => rfl
    rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply, ih (fun i => ds i.succ), map_sum,
      ← (Fin.consEquiv fun _ => Fin s).sum_comp, Fintype.sum_prod_type]
    simp only [Derivation.coeFn_coe, deriv_finsetProd, hce, List.ofFn_succ, Fin.cons_zero,
      Fin.cons_succ, List.prod_cons, Module.End.mul_apply]
    refine Finset.sum_comm.trans
      (Finset.sum_congr rfl fun k₀ _ => Finset.sum_congr rfl fun φ _ =>
        Finset.prod_congr rfl fun k _ => ?_)
    by_cases h : k = k₀
    · subst h; simp
    · simp [h, Ne.symm h]

theorem prod_map_ite_one {M ι : Type*} [Monoid M] (l : List ι) (p : ι → Prop) [DecidablePred p]
    (d : ι → M) :
    (l.map fun j => if p j then d j else 1).prod = ((l.filter fun j => p j).map d).prod := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : p a <;> simp [List.filter_cons, h, ih]

end General

variable {n : ℕ}

section ChainRule

variable {R : Type*} [CommRing R]

def linSub (g : Matrix (Fin n) (Fin n) R) :
    MvPolynomial (Fin n × Fin n) R →ₐ[R] MvPolynomial (Fin n × Fin n) R :=
  aeval fun p => ∑ k, C (g p.1 k) * X (k, p.2)

theorem pderiv_linSub_X (g : Matrix (Fin n) (Fin n) R) (a b : Fin n) (v : Fin n × Fin n) :
    pderiv (a, b) (linSub g (X v)) = if v.2 = b then C (g v.1 a) else 0 := by
  simp only [linSub, aeval_X, map_sum, Derivation.leibniz, pderiv_C, pderiv_X, smul_zero,
    add_zero, smul_eq_mul, Pi.single_apply, Prod.mk.injEq]
  by_cases hb : v.2 = b
  · subst hb; simp
  · simp [hb]

theorem pderiv_linSub (g : Matrix (Fin n) (Fin n) R) (a b : Fin n)
    (q : MvPolynomial (Fin n × Fin n) R) :
    pderiv (a, b) (linSub g q) = ∑ i, C (g i a) * linSub g (pderiv (i, b) q) := by
  induction q using MvPolynomial.induction_on
  next c =>
    simp [linSub]
  next p q hp hq =>
    simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  next p v hp =>
    have hs : ∀ i, linSub g (Pi.single (M := fun _ : Fin n × Fin n => MvPolynomial (Fin n × Fin n) R) (i, b) 1 v) =
        if v = (i, b) then 1 else 0 := fun i => by
      rw [Pi.single_apply]; split_ifs <;> simp
    rw [map_mul, Derivation.leibniz, hp, pderiv_linSub_X]
    simp only [Derivation.leibniz, pderiv_X, map_add, map_mul, smul_eq_mul, mul_add,
      Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · simp only [hs, mul_ite, mul_one, mul_zero]
      by_cases hb : v.2 = b
      · rw [if_pos hb, Finset.sum_eq_single v.1]
        · rw [if_pos (by ext <;> simp [hb])]; ring
        · intro i _ hi; rw [if_neg (fun h => hi (congrArg Prod.fst h).symm)]
        · simp
      · rw [if_neg hb]; symm
        exact Finset.sum_eq_zero fun i _ => if_neg (fun h => hb (congrArg Prod.snd h))
    · exact Finset.sum_congr rfl fun i _ => by ring

def dOp {m : ℕ} (r c : Fin m → Fin n) : Module.End R (MvPolynomial (Fin n × Fin n) R) :=
  (List.ofFn fun t => ((pderiv (r t, c t) : Derivation R _ _) :
    MvPolynomial (Fin n × Fin n) R →ₗ[R] MvPolynomial (Fin n × Fin n) R)).prod

theorem dOp_linSub {m : ℕ} (g : Matrix (Fin n) (Fin n) R) (r c : Fin m → Fin n)
    (q : MvPolynomial (Fin n × Fin n) R) :
    dOp r c (linSub g q) =
      ∑ τ : Fin m → Fin n, C (∏ t, g (τ t) (r t)) * linSub g (dOp τ c q) := by
  induction m with
  | zero => simp [dOp]
  | succ m ih =>
    have key : ∀ (r' c' : Fin (m + 1) → Fin n) (p : MvPolynomial (Fin n × Fin n) R),
        dOp r' c' p = pderiv (r' 0, c' 0) (dOp (fun i => r' i.succ) (fun i => c' i.succ) p) := by
      intro r' c' p
      simp only [dOp, List.ofFn_succ, List.prod_cons, Module.End.mul_apply, Derivation.coeFn_coe]
    have hce : ∀ x : Fin n × (Fin m → Fin n),
        (Fin.consEquiv fun _ => Fin n) x = Fin.cons x.1 x.2 := fun x => rfl
    rw [key, ih, map_sum, ← (Fin.consEquiv fun _ => Fin n).sum_comp, Fintype.sum_prod_type]
    simp only [hce, key, Fin.cons_zero, Fin.cons_succ, Fin.prod_univ_succ, Derivation.leibniz,
      pderiv_C, smul_zero, smul_eq_mul, mul_zero, add_zero, pderiv_linSub, Finset.mul_sum, map_mul]
    exact Finset.sum_comm.trans
      (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun τ _ => by ring)

theorem cayMono_eq_dOp (σ : Equiv.Perm (Fin n)) : cayMono n R σ = dOp σ id := by
  unfold cayMono dOp
  simp only [List.ofFn_eq_map, id_eq]

theorem sum_fun_eq_sum_perm {M : Type*} [AddCommMonoid M] (F : (Fin n → Fin n) → M)
    (h : ∀ τ, ¬ Function.Injective τ → F τ = 0) :
    ∑ τ, F τ = ∑ e : Equiv.Perm (Fin n), F e := by
  classical
  have e : ∑ e : Equiv.Perm (Fin n), F e = ∑ τ ∈ Finset.univ.map
      ⟨fun e : Equiv.Perm (Fin n) => (e : Fin n → Fin n), DFunLike.coe_injective⟩, F τ :=
    by simp [Finset.sum_map]
  rw [e]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro τ _ hτ
  apply h
  intro hinj
  apply hτ
  rw [Finset.mem_map]
  exact ⟨Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hinj), Finset.mem_univ _, rfl⟩

theorem cayOp_linSub (g : Matrix (Fin n) (Fin n) R) (q : MvPolynomial (Fin n × Fin n) R) :
    cayOp n R (linSub g q) = C g.det * linSub g (cayOp n R q) := by
  have hdet : ∀ τ : Fin n → Fin n, ∑ σ : Equiv.Perm (Fin n),
      (Equiv.Perm.sign σ : ℤ) • ∏ t, g (τ t) (σ t) = (g.submatrix τ id).det := by
    intro τ
    rw [← Matrix.det_transpose, Matrix.det_apply]
    simp [Units.smul_def]
  have h0 : ∀ τ : Fin n → Fin n, ¬ Function.Injective τ → (g.submatrix τ id).det = 0 := by
    intro τ hτ
    simp only [Function.Injective, not_forall] at hτ
    obtain ⟨i, j, hij, hne⟩ := hτ
    exact Matrix.det_zero_of_row_eq hne (by ext k; simp [hij])
  calc cayOp n R (linSub g q)
      = ∑ σ : Equiv.Perm (Fin n), ∑ τ : Fin n → Fin n,
          C ((Equiv.Perm.sign σ : ℤ) • ∏ t, g (τ t) (σ t)) * linSub g (dOp τ id q) := by
        simp only [cayOp, LinearMap.sum_apply, LinearMap.smul_apply, cayMono_eq_dOp, dOp_linSub,
          Finset.smul_sum, map_zsmul, smul_mul_assoc]
    _ = ∑ τ : Fin n → Fin n, C ((g.submatrix τ id).det) * linSub g (dOp τ id q) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [← hdet, map_sum, Finset.sum_mul]
    _ = ∑ e : Equiv.Perm (Fin n), C ((g.submatrix e id).det) * linSub g (dOp e id q) :=
        sum_fun_eq_sum_perm _ fun τ hτ => by rw [h0 τ hτ, map_zero, zero_mul]
    _ = C g.det * linSub g (cayOp n R q) := by
        simp only [cayOp, LinearMap.sum_apply, LinearMap.smul_apply, cayMono_eq_dOp, map_sum,
          Finset.mul_sum, Matrix.det_permute, map_zsmul, map_mul, map_intCast]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [zsmul_eq_mul]
        ring

theorem linSub_cayDet (g : Matrix (Fin n) (Fin n) R) :
    linSub g (cayDet n R) = C g.det * cayDet n R := by
  show linSub g (Matrix.mvPolynomialX (Fin n) (Fin n) R).det = _
  rw [AlgHom.map_det]
  have e : (linSub g).mapMatrix (Matrix.mvPolynomialX (Fin n) (Fin n) R) =
      (C : R →+* MvPolynomial (Fin n × Fin n) R).mapMatrix g *
        Matrix.mvPolynomialX (Fin n) (Fin n) R := by
    ext i j
    simp [linSub, Matrix.mul_apply]
  rw [e, Matrix.det_mul, ← RingHom.map_det]

end ChainRule

section Integer

def onePt : Fin n × Fin n → ℤ := fun v => (1 : Matrix (Fin n) (Fin n) ℤ) v.1 v.2

theorem eval_onePt_linSub (x : Fin n × Fin n → ℤ) (p : MvPolynomial (Fin n × Fin n) ℤ) :
    eval onePt (linSub (Matrix.of fun i j => x (i, j)) p) = eval x p := by
  have e : (eval onePt).comp (linSub (Matrix.of fun i j => x (i, j))).toRingHom = eval x := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [linSub]
    · intro v
      simp [linSub, onePt, Matrix.one_apply]
  exact RingHom.congr_fun e p

theorem eval_cayDet (x : Fin n × Fin n → ℤ) :
    eval x (cayDet n ℤ) = (Matrix.of fun i j => x (i, j)).det := by
  show eval x (Matrix.mvPolynomialX (Fin n) (Fin n) ℤ).det = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp

theorem detPoly_mul_cayleyOmega_pow (s : ℕ) :
    cayDet n ℤ * cayOp n ℤ (cayDet n ℤ ^ s) =
      C (eval onePt (cayOp n ℤ (cayDet n ℤ ^ s))) * cayDet n ℤ ^ s := by
  apply MvPolynomial.funext
  intro x
  have h1 := cayOp_linSub (Matrix.of fun i j => x (i, j)) (cayDet n ℤ ^ s)
  rw [map_pow (linSub (Matrix.of fun i j => x (i, j))), linSub_cayDet, mul_pow,
    ← map_pow (C : ℤ →+* MvPolynomial (Fin n × Fin n) ℤ), MvPolynomial.C_mul', map_smul,
    ← MvPolynomial.C_mul'] at h1
  have h3 := congrArg (eval onePt) h1
  simp only [map_mul, map_pow, eval_C, eval_onePt_linSub] at h3
  simp only [map_mul, map_pow, eval_C, eval_cayDet]
  linear_combination -1 * h3

theorem cayley_int_succ (s : ℕ) :
    cayOp n ℤ (cayDet n ℤ ^ (s + 1)) =
      C (eval onePt (cayOp n ℤ (cayDet n ℤ ^ (s + 1)))) * cayDet n ℤ ^ s := by
  have h := detPoly_mul_cayleyOmega_pow (n := n) (s + 1)
  have hne : cayDet n ℤ ≠ 0 := Matrix.det_mvPolynomialX_ne_zero (Fin n) ℤ
  apply mul_left_cancel₀ hne
  rw [h]; ring

def funMat (ρ : Fin n → Fin n) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun a b => if a = ρ b then 1 else 0

theorem funMat_mul (ρ ρ' : Fin n → Fin n) : funMat ρ * funMat ρ' = funMat (ρ ∘ ρ') := by
  ext a c
  simp only [funMat, Matrix.mul_apply, Matrix.of_apply, Function.comp_apply, mul_ite, mul_one,
    mul_zero]
  simp

theorem funMat_id : funMat (fun b : Fin n => b) = 1 := by
  ext a b
  simp [funMat, Matrix.one_apply]

theorem det_funMat_perm (σ : Equiv.Perm (Fin n)) : (funMat σ).det = Equiv.Perm.sign σ := by
  have e : funMat σ = (σ.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) ℤ)ᵀ := by
    ext a b
    by_cases h : a = σ b
    · simp [funMat, PEquiv.toMatrix_apply, h]
    · have h' : σ b ≠ a := fun e => h e.symm
      simp [funMat, PEquiv.toMatrix_apply, h, h']
  rw [e, Matrix.det_transpose]
  simp [Matrix.det_permutation]

theorem list_prod_funMat {s : ℕ} (σ : Equiv.Perm (Fin n)) (φ : Fin n → Fin s)
    (hσ : ∀ b, φ (σ b) = φ b) (L : List (Fin s)) (hL : L.Nodup) :
    (L.map fun k => funMat (fun b => if φ b = k then σ b else b)).prod =
      funMat (fun b => if φ b ∈ L then σ b else b) := by
  induction L with
  | nil => simp [funMat_id]
  | cons k L ih =>
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.prod_cons, ih hL.2, funMat_mul]
    congr 1
    funext b
    by_cases hb : φ b ∈ L
    · have hk : φ b ≠ k := fun h => hL.1 (by rw [← h]; exact hb)
      simp [hb, hσ, hk]
    · by_cases hk : φ b = k <;> simp [hb, hk, hL.1]

theorem prod_det_funMat {s : ℕ} (σ : Equiv.Perm (Fin n)) (φ : Fin n → Fin s) :
    ∏ k, (funMat (fun b => if φ b = k then σ b else b)).det =
      if φ ∘ σ = φ then (Equiv.Perm.sign σ : ℤ) else 0 := by
  split_ifs with h
  · have hσ : ∀ b, φ (σ b) = φ b := fun b => congrFun h b
    have e := list_prod_funMat σ φ hσ (List.finRange s) (List.nodup_finRange s)
    have e2 : (funMat fun b => if φ b ∈ List.finRange s then σ b else b) = funMat σ := by
      congr 1; funext b; simp
    rw [e2] at e
    rw [← det_funMat_perm, ← e, ← List.prod_ofFn, List.ofFn_eq_map,
      show ∀ l : List (Matrix (Fin n) (Fin n) ℤ), l.prod.det = (l.map Matrix.det).prod from
        fun l => map_list_prod (Matrix.detMonoidHom) l, List.map_map]
    try rfl
  · have hex : ∃ b, φ (σ b) ≠ φ b := by
      by_contra hc
      push_neg at hc
      exact h (funext hc)
    obtain ⟨b, hb⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ (φ b))
    have hne : b ≠ σ b := fun e => hb (by rw [← e])
    apply Matrix.det_zero_of_column_eq hne
    intro a
    simp [funMat, hb]

def yP (σ τ : Fin n → Fin n) (S : Finset (Fin n)) : MvPolynomial (Fin n × Fin n) ℤ :=
  ∏ b, if b ∈ S then (if τ b = σ b then 1 else 0) else X (τ b, b)

theorem pderiv_yP (σ τ : Fin n → Fin n) (S : Finset (Fin n)) (j : Fin n) (hj : j ∉ S) :
    pderiv (σ j, j) (yP σ τ S) = yP σ τ (insert j S) := by
  rw [yP, yP, deriv_finsetProd, Finset.sum_eq_single j]
  · refine Finset.prod_congr rfl fun b _ => ?_
    by_cases hb : b = j
    · subst hb; simp [hj, pderiv_X, Pi.single_apply]
    · simp [hb, Finset.mem_insert]
  · intro b₀ _ hb₀
    apply Finset.prod_eq_zero (Finset.mem_univ b₀)
    by_cases hS : b₀ ∈ S
    · simp [hS, apply_ite (⇑(pderiv (σ j, j) : Derivation ℤ (MvPolynomial (Fin n × Fin n) ℤ)
        (MvPolynomial (Fin n × Fin n) ℤ))), Derivation.map_one_eq_zero]
    · simp [hS, pderiv_X, Pi.single_apply, hb₀]
  · simp

theorem list_pderiv_yP (σ τ : Fin n → Fin n) (l : List (Fin n)) (hl : l.Nodup)
    (S : Finset (Fin n)) (hS : ∀ j ∈ l, j ∉ S) :
    (l.map fun j => ((pderiv (σ j, j) : Derivation ℤ _ _) :
      MvPolynomial (Fin n × Fin n) ℤ →ₗ[ℤ] MvPolynomial (Fin n × Fin n) ℤ)).prod (yP σ τ S) =
      yP σ τ (S ∪ l.toFinset) := by
  induction l with
  | nil => simp
  | cons j l ih =>
    rw [List.nodup_cons] at hl
    have hS' : ∀ i ∈ l, i ∉ S := fun i hi => hS i (List.mem_cons_of_mem j hi)
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ih hl.2 hS', Derivation.coeFn_coe,
      pderiv_yP]
    · rw [List.toFinset_cons, Finset.union_insert]
    · simp only [Finset.mem_union, List.mem_toFinset, not_or]
      exact ⟨hS j (by simp), hl.1⟩

def fibOp (σ : Fin n → Fin n) {s : ℕ} (φ : Fin n → Fin s) (k : Fin s) :
    Module.End ℤ (MvPolynomial (Fin n × Fin n) ℤ) :=
  (List.ofFn fun j => if φ j = k then ((pderiv (σ j, j) : Derivation ℤ _ _) :
    MvPolynomial (Fin n × Fin n) ℤ →ₗ[ℤ] MvPolynomial (Fin n × Fin n) ℤ) else 1).prod

theorem eval_fibOp_cayDet (σ : Fin n → Fin n) {s : ℕ} (φ : Fin n → Fin s) (k : Fin s) :
    eval onePt (fibOp σ φ k (cayDet n ℤ)) =
      (funMat fun b => if φ b = k then σ b else b).det := by
  have hf : fibOp σ φ k = (((List.finRange n).filter fun j => φ j = k).map fun j =>
      ((pderiv (σ j, j) : Derivation ℤ (MvPolynomial (Fin n × Fin n) ℤ) _) :
        MvPolynomial (Fin n × Fin n) ℤ →ₗ[ℤ] MvPolynomial (Fin n × Fin n) ℤ)).prod := by
    unfold fibOp
    rw [List.ofFn_eq_map, prod_map_ite_one]
  have hc : cayDet n ℤ = ∑ τ : Equiv.Perm (Fin n), (Equiv.Perm.sign τ : ℤ) • yP σ τ ∅ := by
    simp [cayDet, Matrix.det_apply, yP, Units.smul_def, Matrix.mvPolynomialX_apply]
  have hS : ((List.finRange n).filter fun j => φ j = k).toFinset =
      Finset.univ.filter fun b => φ b = k := by
    ext b; simp
  rw [hf, hc, map_sum, map_sum, Matrix.det_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_zsmul, list_pderiv_yP σ τ _ (List.Nodup.filter _ (List.nodup_finRange n)) ∅ (by simp),
    Finset.empty_union, hS, map_zsmul, Units.smul_def]
  congr 1
  simp only [yP, map_prod]
  refine Finset.prod_congr rfl fun b _ => ?_
  by_cases hb : φ b = k
  · simp [hb, funMat, onePt, apply_ite (eval onePt)]
  · simp [hb, funMat, onePt, Matrix.one_apply, apply_ite (eval onePt)]

theorem cayMono_pow (σ : Equiv.Perm (Fin n)) (s : ℕ) :
    cayMono n ℤ σ (cayDet n ℤ ^ s) = ∑ φ : Fin n → Fin s, ∏ k, fibOp σ φ k (cayDet n ℤ) := by
  have h := leibniz_ofFn
    (fun i : Fin n => (pderiv (σ i, i) : Derivation ℤ (MvPolynomial (Fin n × Fin n) ℤ) _))
    (fun _ : Fin s => cayDet n ℤ)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  unfold cayMono fibOp
  rw [← List.ofFn_eq_map]
  exact h

theorem card_fibre_cons {s m : ℕ} (k₀ : Fin s) (φ : Fin m → Fin s) (k : Fin s) :
    #{a | (Fin.cons k₀ φ : Fin (m + 1) → Fin s) a = k} = #{a | φ a = k} + if k₀ = k then 1 else 0 := by
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

theorem sum_prod_factorial_add_ite {s : ℕ} (c : Fin s → ℕ) :
    ∑ k₀, ∏ k, (c k + if k₀ = k then 1 else 0).factorial =
      (∏ k, (c k).factorial) * (∑ k, c k + s) := by
  have h : ∀ k₀, ∏ k, (c k + if k₀ = k then 1 else 0).factorial =
      (∏ k, (c k).factorial) * (c k₀ + 1) := by
    intro k₀
    have e : ∀ k, (c k + if k₀ = k then 1 else 0).factorial =
        (c k).factorial * (if k₀ = k then c k + 1 else 1) := by
      intro k
      split_ifs
      · rw [Nat.factorial_succ, mul_comm]
      · simp
    simp only [e, Finset.prod_mul_distrib, Finset.prod_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_congr rfl fun k₀ _ => h k₀, ← Finset.mul_sum, Finset.sum_add_distrib]
  simp

theorem sum_prod_factorial_fibres (s : ℕ) : ∀ m : ℕ,
    ∑ φ : Fin m → Fin s, ∏ k, (#{a | φ a = k}).factorial = ∏ j ∈ range m, (s + j)
  | 0 => by simp
  | m + 1 => by
    rw [Finset.prod_range_succ, ← sum_prod_factorial_fibres s m, Finset.sum_mul,
      ← Fintype.sum_equiv (Fin.consEquiv fun _ => Fin s)
        (fun p => ∏ k, (#{a | (Fin.cons p.1 p.2 : Fin (m + 1) → Fin s) a = k}).factorial) _
        (fun p => rfl), Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun φ _ => ?_
    simp only [card_fibre_cons]
    have hsum : ∑ k, #{a | φ a = k} = m := by
      have := Finset.card_eq_sum_card_fiberwise (f := φ) (s := univ) (t := univ)
        (fun x _ => mem_univ _)
      simpa using this.symm
    rw [sum_prod_factorial_add_ite, hsum, add_comm m s]

theorem eval_one_cayOp_pow (s : ℕ) :
    eval onePt (cayOp n ℤ (cayDet n ℤ ^ s)) = ((∏ k ∈ range n, (s + k) : ℕ) : ℤ) := by
  have hstab : ∀ φ : Fin n → Fin s, ∑ σ : Equiv.Perm (Fin n),
      (if φ ∘ σ = φ then (1 : ℤ) else 0) = ∏ k, ((#{a | φ a = k}).factorial : ℤ) := by
    intro φ
    rw [Finset.sum_boole]
    have h := DomMulAct.stabilizer_card φ
    simp only [Fintype.card_subtype] at h
    exact_mod_cast h
  have h1 : ∀ σ : Equiv.Perm (Fin n), eval onePt (cayMono n ℤ σ (cayDet n ℤ ^ s)) =
      ∑ φ : Fin n → Fin s, if φ ∘ σ = φ then (Equiv.Perm.sign σ : ℤ) else 0 := by
    intro σ
    rw [cayMono_pow, map_sum]
    simp only [map_prod, eval_fibOp_cayDet, prod_det_funMat]
  have hsq : ∀ σ : Equiv.Perm (Fin n),
      (Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign σ : ℤ) = 1 := fun σ => by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  simp only [cayOp, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul, h1,
    Finset.smul_sum, smul_ite, smul_zero, smul_eq_mul, Finset.mul_sum, mul_ite, mul_zero, hsq]
  rw [Finset.sum_comm]
  simp only [hstab]
  have h2 := sum_prod_factorial_fibres s n
  exact_mod_cast h2

end Integer

section Map

variable {R : Type*} [CommRing R]

theorem cayOp_map (p : MvPolynomial (Fin n × Fin n) ℤ) :
    cayOp n R (map (Int.castRingHom R) p) = map (Int.castRingHom R) (cayOp n ℤ p) := by
  have hl : ∀ (l : List (Fin n)) (σ : Equiv.Perm (Fin n)) (q : MvPolynomial (Fin n × Fin n) ℤ),
      (l.map fun j => ((pderiv (σ j, j) : Derivation R _ _) :
        MvPolynomial (Fin n × Fin n) R →ₗ[R] MvPolynomial (Fin n × Fin n) R)).prod
          (map (Int.castRingHom R) q) =
      map (Int.castRingHom R) ((l.map fun j => ((pderiv (σ j, j) : Derivation ℤ _ _) :
        MvPolynomial (Fin n × Fin n) ℤ →ₗ[ℤ] MvPolynomial (Fin n × Fin n) ℤ)).prod q) := by
    intro l σ q
    induction l with
    | nil => simp
    | cons j l ih =>
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih, Derivation.coeFn_coe,
        pderiv_map]
  simp only [cayOp, cayMono, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul, hl]

theorem cayDet_map : map (Int.castRingHom R) (cayDet n ℤ) = cayDet n R := by
  show map (Int.castRingHom R) (Matrix.mvPolynomialX (Fin n) (Fin n) ℤ).det =
    (Matrix.mvPolynomialX (Fin n) (Fin n) R).det
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.mvPolynomialX_apply, map_X]

end Map

theorem cayley : CayleyStatement := by
  unfold CayleyStatement
  intro n R _ s
  rcases s with _ | t
  · rcases n with _ | m
    · simp [cayOp, cayMono]
    · have hd : (0 : Matrix (Fin (m + 1)) (Fin (m + 1)) R).det = 0 := Matrix.det_zero
      have h := cayOp_linSub (n := m + 1) (R := R) 0 1
      simp only [map_one, hd, map_zero, zero_mul] at h
      rw [pow_zero, h, Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.succ_pos m)) (zero_add 0),
        zero_smul]
  · rw [← cayDet_map (n := n) (R := R), ← map_pow, cayOp_map, cayley_int_succ,
      eval_one_cayOp_pow, map_mul, map_pow, cayDet_map, map_C]
    simp [nsmul_eq_mul]

end ReciprocityTheory.PGsh
