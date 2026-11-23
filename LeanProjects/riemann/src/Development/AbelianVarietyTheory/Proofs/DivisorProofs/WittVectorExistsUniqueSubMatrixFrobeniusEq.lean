import Mathlib

namespace GlobalTheory.WittSolve

open WittVector

variable {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R] [CharP R p] [PerfectRing R p]
  {ι : Type} [Fintype ι]

noncomputable def F (M : Matrix ι ι (WittVector p R)) (v : ι → WittVector p R) :
    ι → WittVector p R :=
  v - M.mulVec (fun k => WittVector.frobenius (v k))

lemma F_add (M : Matrix ι ι (WittVector p R)) (v w : ι → WittVector p R) :
    F M (v + w) = F M v + F M w := by
  have : (fun k => WittVector.frobenius ((v + w) k)) =
      (fun k => WittVector.frobenius (v k)) + (fun k => WittVector.frobenius (w k)) := by
    funext k; simp [map_add]
  simp only [F, this, Matrix.mulVec_add]; abel

lemma F_zero (M : Matrix ι ι (WittVector p R)) : F M 0 = 0 := by
  simp only [F, Pi.zero_apply, map_zero, sub_eq_zero]
  exact (Matrix.mulVec_zero M).symm

lemma F_sub (M : Matrix ι ι (WittVector p R)) (v w : ι → WittVector p R) :
    F M (v - w) = F M v - F M w := by
  have := F_add M (v - w) w
  rw [sub_add_cancel] at this
  rw [this]; abel

lemma F_smul (M : Matrix ι ι (WittVector p R)) (n : ℕ) (v : ι → WittVector p R) :
    F M (((p : WittVector p R) ^ n) • v) = ((p : WittVector p R) ^ n) • F M v := by
  have : (fun k => WittVector.frobenius ((((p : WittVector p R) ^ n) • v) k)) =
      ((p : WittVector p R) ^ n) • (fun k => WittVector.frobenius (v k)) := by
    funext k; simp [map_mul, map_pow, map_natCast]
  simp only [F, this, Matrix.mulVec_smul, smul_sub]

lemma constantCoeff_F (M : Matrix ι ι (WittVector p R)) (v : ι → WittVector p R) (k : ι) :
    WittVector.constantCoeff (F M v k) =
      ((fun j => WittVector.constantCoeff (v j)) - (M.map WittVector.constantCoeff).mulVec
        (fun j => frobenius R p (WittVector.constantCoeff (v j)))) k := by
  simp only [F, Pi.sub_apply, map_sub, RingHom.map_mulVec]
  congr 2
  funext j
  simp [Function.comp_def, WittVector.constantCoeff_apply, WittVector.coeff_frobenius_charP,
    frobenius_def]

lemma p_dvd_iff (x : WittVector p R) :
    (p : WittVector p R) ∣ x ↔ WittVector.constantCoeff x = 0 := by
  rw [← Ideal.mem_span_singleton, WittVector.mem_span_p_iff_coeff_zero_eq_zero,
    WittVector.constantCoeff_apply]

lemma smod_iff (x y : WittVector p R) (n : ℕ) :
    x ≡ y [SMOD (Ideal.span {(p : WittVector p R)}) ^ n •
      (⊤ : Submodule (WittVector p R) (WittVector p R))] ↔ (p : WittVector p R) ^ n ∣ x - y := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top,
    Ideal.mem_span_singleton]

variable {M : Matrix ι ι (WittVector p R)}

lemma inj_step
    (hU : ∀ c : ι → R, ∃! x : ι → R, x - (M.map WittVector.constantCoeff).mulVec
      (fun k => frobenius R p (x k)) = c)
    (v : ι → WittVector p R) (hv : F M v = 0) :
    ∃ w : ι → WittVector p R, v = (p : WittVector p R) • w ∧ F M w = 0 := by
  have hx : (fun j => WittVector.constantCoeff (v j)) - (M.map WittVector.constantCoeff).mulVec
      (fun j => frobenius R p (WittVector.constantCoeff (v j))) = 0 := by
    funext k
    rw [← constantCoeff_F, hv]; simp
  have h0 : (0 : ι → R) - (M.map WittVector.constantCoeff).mulVec
      (fun j => frobenius R p ((0 : ι → R) j)) = 0 := by
    simp only [Pi.zero_apply, map_zero, zero_sub, neg_eq_zero]
    exact Matrix.mulVec_zero _
  have hx0 := (hU 0).unique hx h0
  have hd : ∀ k, ∃ w, v k = (p : WittVector p R) * w := by
    intro k
    exact (p_dvd_iff (v k)).2 (congrFun hx0 k)
  choose w hw using hd
  refine ⟨w, funext fun k => by simp [hw k], ?_⟩
  have h1 : F M ((p : WittVector p R) ^ 1 • w) = 0 := by
    rw [pow_one]; convert hv; funext k; simp [hw k]
  rw [F_smul, pow_one] at h1
  funext k
  have := congrFun h1 k
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  exact WittVector.eq_zero_of_p_mul_eq_zero _ (by rw [mul_comm]; exact this)

lemma inj
    (hU : ∀ c : ι → R, ∃! x : ι → R, x - (M.map WittVector.constantCoeff).mulVec
      (fun k => frobenius R p (x k)) = c)
    (v : ι → WittVector p R) (hv : F M v = 0) : v = 0 := by
  have key : ∀ n : ℕ, ∀ v : ι → WittVector p R, F M v = 0 → ∀ k, (p : WittVector p R) ^ n ∣ v k := by
    intro n
    induction n with
    | zero => intro v _ k; simp
    | succ n ih =>
      intro v hv k
      obtain ⟨w, rfl, hw⟩ := inj_step hU v hv
      simp only [Pi.smul_apply, smul_eq_mul, pow_succ']
      exact mul_dvd_mul_left _ (ih w hw k)
  funext k
  refine IsHausdorff.haus (I := Ideal.span {(p : WittVector p R)}) inferInstance (v k) fun n => ?_
  rw [smod_iff, sub_zero]
  exact key n v hv k

lemma modp
    (hU : ∀ c : ι → R, ∃! x : ι → R, x - (M.map WittVector.constantCoeff).mulVec
      (fun k => frobenius R p (x k)) = c)
    (d : ι → WittVector p R) :
    ∃ u e : ι → WittVector p R, d = F M u + (p : WittVector p R) • e := by
  obtain ⟨x, hx, -⟩ := hU (fun k => WittVector.constantCoeff (d k))
  set u : ι → WittVector p R := fun k => WittVector.teichmuller p (x k) with hu
  have hc : (fun j => WittVector.constantCoeff (u j)) = x := by
    funext j; simp [hu, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
  have hd : ∀ k, ∃ e, d k - F M u k = (p : WittVector p R) * e := by
    intro k
    apply (p_dvd_iff _).2
    have hc' : ∀ j, WittVector.constantCoeff (u j) = x j := fun j => congrFun hc j
    rw [map_sub, constantCoeff_F]
    simp only [hc']
    rw [hx, sub_self]
  choose e he using hd
  refine ⟨u, e, funext fun k => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← he k, add_sub_cancel]

lemma exists_sol
    (hU : ∀ c : ι → R, ∃! x : ι → R, x - (M.map WittVector.constantCoeff).mulVec
      (fun k => frobenius R p (x k)) = c)
    (c : ι → WittVector p R) : ∃ v, F M v = c := by
  choose U E hUE using modp hU
  obtain ⟨seq, seq_zero, seq_succ⟩ : ∃ seq : ℕ → (ι → WittVector p R) × (ι → WittVector p R),
      seq 0 = (0, c) ∧ ∀ n, seq (n + 1) =
        ((seq n).1 + ((p : WittVector p R) ^ n) • U (seq n).2, E (seq n).2) :=
    ⟨fun n => Nat.rec ((0 : ι → WittVector p R), c)
      (fun n q => (q.1 + ((p : WittVector p R) ^ n) • U q.2, E q.2)) n, rfl, fun _ => rfl⟩
  have inv : ∀ n, c = F M (seq n).1 + ((p : WittVector p R) ^ n) • (seq n).2 := by
    intro n
    induction n with
    | zero => rw [seq_zero, F_zero, pow_zero, one_smul, zero_add]
    | succ n ih =>
      have h2 := hUE (seq n).2
      rw [seq_succ, F_add, F_smul]
      funext k
      have a := congrFun ih k
      have b := congrFun h2 k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at a b ⊢
      linear_combination a + (p : WittVector p R) ^ n * b
  have compat : ∀ m n, m ≤ n → ∀ k, (p : WittVector p R) ^ m ∣ (seq n).1 k - (seq m).1 k := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => intro k; simp
    | succ n hmn ih =>
      intro k
      rw [seq_succ]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have : (seq n).1 k + (p : WittVector p R) ^ n * U (seq n).2 k - (seq m).1 k =
          ((seq n).1 k - (seq m).1 k) + (p : WittVector p R) ^ n * U (seq n).2 k := by ring
      rw [this]
      exact dvd_add (ih k) (dvd_mul_of_dvd_left (pow_dvd_pow _ hmn) _)
  have hlim : ∀ k, ∃ L : WittVector p R, ∀ n, (seq n).1 k ≡ L [SMOD (Ideal.span
      {(p : WittVector p R)}) ^ n • (⊤ : Submodule (WittVector p R) (WittVector p R))] := by
    intro k
    refine IsPrecomplete.prec inferInstance ?_
    intro m n hmn
    rw [smod_iff]
    exact dvd_sub_comm.1 (compat m n hmn k)
  choose L hL using hlim
  refine ⟨L, ?_⟩
  have hdiff : ∀ n, ∃ w : ι → WittVector p R, L - (seq n).1 = ((p : WittVector p R) ^ n) • w := by
    intro n
    have : ∀ k, ∃ w, L k - (seq n).1 k = (p : WittVector p R) ^ n * w := fun k =>
      dvd_sub_comm.1 ((smod_iff _ _ n).1 (hL k n))
    choose w hw using this
    exact ⟨w, funext fun k => by simp [hw k]⟩
  have hzero : F M L - c = 0 := by
    funext k
    show (F M L - c) k = 0
    refine IsHausdorff.haus (I := Ideal.span {(p : WittVector p R)}) inferInstance _ fun n => ?_
    rw [smod_iff, sub_zero]
    obtain ⟨w, hw⟩ := hdiff n
    have e1 : F M L = F M (seq n).1 + ((p : WittVector p R) ^ n) • F M w := by
      rw [← F_smul, ← hw, ← F_add, add_sub_cancel]
    have e2 := inv n
    refine ⟨F M w k - (seq n).2 k, ?_⟩
    have a := congrFun e1 k
    have b := congrFun e2 k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at a b
    simp only [Pi.sub_apply]
    linear_combination a - b
  exact sub_eq_zero.1 hzero

end GlobalTheory.WittSolve

namespace GlobalTheory

theorem wittSolve_unique : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
    [PerfectRing R p] (ι : Type) [Fintype ι] (M : Matrix ι ι (WittVector p R)),
    (∀ c : ι → R, ∃! x : ι → R,
      x - (M.map WittVector.constantCoeff).mulVec (fun k => frobenius R p (x k)) = c) →
    ∀ c : ι → WittVector p R, ∃! v : ι → WittVector p R,
      v - M.mulVec (fun k => WittVector.frobenius (v k)) = c := by
  intro p _ R _ _ _ ι _ M hU c
  obtain ⟨v, hv⟩ := WittSolve.exists_sol hU c
  refine ⟨v, hv, fun y hy => ?_⟩
  have h : WittSolve.F M (y - v) = 0 := by
    rw [WittSolve.F_sub]
    exact sub_eq_zero.2 (hy.trans hv.symm)
  exact sub_eq_zero.1 (WittSolve.inj hU _ h)

end GlobalTheory
