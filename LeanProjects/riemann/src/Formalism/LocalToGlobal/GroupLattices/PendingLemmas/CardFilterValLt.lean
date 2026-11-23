import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.DetYtMatNeZero
import Formalism.GradedWeylDivisibility.FinalC

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

noncomputable section

namespace Formalism.L2.G.Pend

section Mat

variable {R : Type*} [CommRing R]

def catM {n : ℕ} (l : ℕ) (A : Matrix (Fin n) (Fin n) R) (x : Fin n → ℕ → R) : Matrix (Fin n) (Fin n) R :=
  fun a t => if t.val < n - l then A a t else x a (t.val - (n - l))

def mulC {n n' : ℕ} (B : Matrix (Fin n') (Fin n) R) (x : Fin n → ℕ → R) : Fin n' → ℕ → R :=
  fun a i => ∑ b, B a b * x b i

theorem mul_catM {n : ℕ} (l : ℕ) (B A : Matrix (Fin n) (Fin n) R) (x : Fin n → ℕ → R) :
    B * catM l A x = catM l (B * A) (mulC B x) := by
  ext a t
  simp only [Matrix.mul_apply, catM, mulC]
  split_ifs <;> rfl

theorem mulC_mul {n n' n'' : ℕ} (A : Matrix (Fin n'') (Fin n') R) (B : Matrix (Fin n') (Fin n) R) (x : Fin n → ℕ → R) :
    mulC (A * B) x = mulC A (mulC B x) := by
  funext a i
  simp only [mulC, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  ring

def lastMinor {n : ℕ} (l : ℕ) (hl : l ≤ n) (z : Fin n → ℕ → R) : R :=
  Matrix.det (Matrix.of fun r i : Fin l => z ⟨n - l + r.val, by have := r.isLt; omega⟩ i.val)

theorem det_catM_smul_one {n : ℕ} (l : ℕ) (hl : l ≤ n) (c : R) (z : Fin n → ℕ → R) :
    (catM l (c • (1 : Matrix (Fin n) (Fin n) R)) z).det = c ^ (n - l) * lastMinor l hl z := by
  let e : Fin (n - l) ⊕ Fin l ≃ Fin n := finSumFinEquiv.trans (finCongr (by omega))
  have e1 : ∀ i : Fin (n - l), (e (Sum.inl i)).val = i.val := fun i => by simp [e]
  have e2 : ∀ r : Fin l, (e (Sum.inr r)).val = n - l + r.val := fun r => by simp [e]
  rw [← Matrix.det_submatrix_equiv_self e]
  have hb : (catM l (c • (1 : Matrix (Fin n) (Fin n) R)) z).submatrix e e =
      Matrix.fromBlocks (c • (1 : Matrix (Fin (n - l)) (Fin (n - l)) R))
        (Matrix.of fun (i : Fin (n - l)) (r : Fin l) => z (e (Sum.inl i)) r.val) 0
        (Matrix.of fun r i : Fin l => z ⟨n - l + r.val, by have := r.isLt; omega⟩ i.val) := by
    ext a t
    rcases a with a | a <;> rcases t with t | t
    · simp only [Matrix.submatrix_apply, catM, Matrix.fromBlocks_apply₁₁, e1, t.isLt, if_true, Matrix.smul_apply,
        Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq]
    · have h : ¬ (n - l + t.val < n - l) := by omega
      simp only [Matrix.submatrix_apply, catM, Matrix.fromBlocks_apply₁₂, e2, h, if_false, Nat.add_sub_cancel_left,
        Matrix.of_apply]
    · simp only [Matrix.submatrix_apply, catM, Matrix.fromBlocks_apply₂₁, e1, t.isLt, if_true, Matrix.smul_apply,
        Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq, reduceCtorEq, if_false, smul_zero, Matrix.zero_apply]
    · have h : ¬ (n - l + t.val < n - l) := by omega
      simp only [Matrix.submatrix_apply, catM, Matrix.fromBlocks_apply₂₂, e2, h, if_false, Nat.add_sub_cancel_left,
        Matrix.of_apply]
      rw [show e (Sum.inr a) = ⟨n - l + a.val, by have := a.isLt; omega⟩ from Fin.ext (e2 a)]
  rw [hb, Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  rfl

theorem colA {n : ℕ} (l : ℕ) (hl : l ≤ n) (M : Matrix (Fin n) (Fin n) R) (x : Fin n → ℕ → R) :
    M.det * (catM l M.adjugate x).det = M.det ^ (n - l) * lastMinor l hl (mulC M x) := by
  rw [← Matrix.det_mul, mul_catM, Matrix.mul_adjugate, det_catM_smul_one l hl]

theorem colB {n : ℕ} (l : ℕ) (hl : l ≤ n) (Y : Matrix (Fin n) (Fin n) R) (z : Fin n → ℕ → R) :
    Y.det ^ (n - 1) * (catM l Y z).det = Y.det ^ (n - l) * lastMinor l hl (mulC Y.adjugate z) := by
  have h := Matrix.det_adjugate Y
  rw [Fintype.card_fin] at h
  rw [← h, ← Matrix.det_mul, mul_catM, Matrix.adjugate_mul, det_catM_smul_one l hl]

theorem col_id {N N' : ℕ} (hN : N ≤ N') (y : Matrix (Fin N') (Fin N') R) (d : Matrix (Fin N) (Fin N') R)
    (sh : Fin N → Fin N') (hsh : ∀ t, (sh t).val = N' - N + t.val) (x : Fin N → ℕ → R) (l : ℕ) (hl : l ≤ N) :
    (y.adjugate.submatrix sh id * d.transpose).det * y.det ^ (N' - l) *
        (catM l (y.adjugate.submatrix sh id * d.transpose).adjugate x).det =
      (y.adjugate.submatrix sh id * d.transpose).det ^ (N - l) * y.det ^ (N' - 1) *
        (catM l y (mulC d.transpose x)).det := by
  have hA := colA l hl (y.adjugate.submatrix sh id * d.transpose) x
  have hB := colB l (hl.trans hN) y (mulC d.transpose x)
  have hm : lastMinor l hl (mulC (y.adjugate.submatrix sh id * d.transpose) x) =
      lastMinor l (hl.trans hN) (mulC y.adjugate (mulC d.transpose x)) := by
    unfold lastMinor
    congr 1
    ext r i
    rw [mulC_mul]
    simp only [Matrix.of_apply]
    simp only [mulC, Matrix.submatrix_apply, id]
    have : sh ⟨N - l + r.val, by have := r.isLt; omega⟩ = ⟨N' - l + r.val, by have := r.isLt; omega⟩ := by
      apply Fin.ext
      rw [hsh]
      show N' - N + (N - l + r.val) = N' - l + r.val
      omega
    rw [this]
  rw [hm] at hA
  calc _ = y.det ^ (N' - l) * ((y.adjugate.submatrix sh id * d.transpose).det *
        (catM l (y.adjugate.submatrix sh id * d.transpose).adjugate x).det) := by ring
    _ = (y.adjugate.submatrix sh id * d.transpose).det ^ (N - l) *
        (y.det ^ (N' - l) * lastMinor l (hl.trans hN) (mulC y.adjugate (mulC d.transpose x))) := by rw [hA]; ring
    _ = _ := by rw [← hB]; ring

theorem cols_id {N N' : ℕ} (hN : N ≤ N') (y : Matrix (Fin N') (Fin N') R) (d : Matrix (Fin N) (Fin N') R)
    (sh : Fin N → Fin N') (hsh : ∀ t, (sh t).val = N' - N + t.val) (x : Fin N → ℕ → R) (c : ℕ) (h : Fin c → ℕ)
    (hh : ∀ k, h k ≤ N) :
    (y.adjugate.submatrix sh id * d.transpose).det ^ c * y.det ^ (∑ k, (N' - h k)) *
        ∏ k, (catM (h k) (y.adjugate.submatrix sh id * d.transpose).adjugate x).det =
      (y.adjugate.submatrix sh id * d.transpose).det ^ (∑ k, (N - h k)) * y.det ^ (c * (N' - 1)) *
        ∏ k, (catM (h k) y (mulC d.transpose x)).det := by
  have := Finset.prod_congr rfl fun k (_ : k ∈ (Finset.univ : Finset (Fin c))) => col_id hN y d sh hsh x (h k) (hh k)
  simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.sum_const, smul_eq_mul] at this
  exact this

theorem cancel_exp [IsDomain R] {ε δ P Q : R} (hε : ε ≠ 0) (hδ : δ ≠ 0) {A B C D : ℕ}
    (h : ε ^ A * δ ^ B * P = ε ^ C * δ ^ D * Q) (eY eT : ℤ) (hY : eY = (B : ℤ) - D) (hT : eT = (A : ℤ) - C) :
    P * (δ ^ eY.toNat * ε ^ eT.toNat) = δ ^ (-eY).toNat * ε ^ (-eT).toNat * Q := by
  have h1 : eY.toNat + D = (-eY).toNat + B := by omega
  have h2 : eT.toNat + C = (-eT).toNat + A := by omega
  apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero C hε) (pow_ne_zero D hδ))
  calc ε ^ C * δ ^ D * (P * (δ ^ eY.toNat * ε ^ eT.toNat))
      = δ ^ (eY.toNat + D) * ε ^ (eT.toNat + C) * P := by rw [pow_add, pow_add]; ring
    _ = δ ^ (-eY).toNat * ε ^ (-eT).toNat * (ε ^ A * δ ^ B * P) := by rw [h1, h2, pow_add, pow_add]; ring
    _ = _ := by rw [h]; ring

theorem map_catM {S : Type*} [CommRing S] (f : R →+* S) {n : ℕ} (l : ℕ) (A : Matrix (Fin n) (Fin n) R)
    (x : Fin n → ℕ → R) : (catM l A x).map f = catM l (A.map f) (fun a i => f (x a i)) := by
  ext a t
  simp only [Matrix.map_apply, catM]
  split_ifs <;> rfl

end Mat

section Block

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc]

theorem YtMat_eq (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    YtMat X Kc j v s = (yMat X Kc j v s).adjugate.submatrix (shiftI X j) id * (dMat X Kc j v s).transpose := rfl

theorem odd_block (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) (x : Fin (NN X.G.P.m X.t j) → ℕ → DA X Kc j)
    (c : ℕ) (h : Fin c → ℕ) (hh : ∀ k, h k ≤ NN X.G.P.m X.t j) (hc : (c : ℤ) = cMu X j v s)
    (hs : ((∑ k, h k : ℕ) : ℤ) = szMu X j v s) :
    (∏ k, (catM (h k) (YtMat X Kc j v s).adjugate x).det) *
        ((yMat X Kc j v s).det ^ (exY X j v s).toNat * (YtMat X Kc j v s).det ^ (exT X j v s).toNat) =
      (yMat X Kc j v s).det ^ (-exY X j v s).toNat * (YtMat X Kc j v s).det ^ (-exT X j v s).toNat *
        ∏ k, (catM (h k) (yMat X Kc j v s) (mulC (dMat X Kc j v s).transpose x)).det := by
  have key := cols_id (NN_le X j) (yMat X Kc j v s) (dMat X Kc j v s) (shiftI X j) (fun _ => rfl) x c h hh
  rw [← YtMat_eq] at key
  have hN1 : 1 ≤ NN X.G.P.m X.t (j + 1) := by unfold NN; omega
  have s1 : ((∑ k, (NN X.G.P.m X.t (j + 1) - h k) : ℕ) : ℤ) = (c : ℤ) * NN X.G.P.m X.t (j + 1) - (∑ k, h k : ℕ) := by
    push_cast
    rw [Finset.sum_congr rfl fun k _ => Nat.cast_sub ((hh k).trans (NN_le X j)), Finset.sum_sub_distrib]
    simp
  have s2 : ((∑ k, (NN X.G.P.m X.t j - h k) : ℕ) : ℤ) = (c : ℤ) * NN X.G.P.m X.t j - (∑ k, h k : ℕ) := by
    push_cast
    rw [Finset.sum_congr rfl fun k _ => Nat.cast_sub (hh k), Finset.sum_sub_distrib]
    simp
  refine cancel_exp (det_YtMat_ne_zero X Kc j v s) (det_yMat_ne_zero X Kc j v s) key _ _ ?_ ?_
  · rw [s1, hs]
    push_cast
    rw [Nat.cast_sub hN1, hc]
    unfold exY
    push_cast
    ring
  · rw [s2, hs, hc]
    unfold exT
    ring

end Block

section Hv

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc]

def idxI : (j : ℕ) → YI X j →
    (Σ v : Fin (X.Fl.Pj j).nV, Fin ((X.Fl.Pj j).n' v) × (Fin ((X.Fl.Pj j).m + 1) × Fin ((X.Fl.Pj j).m + 1)))
  | 0, x => ⟨x.1, (x.2.1, (Fin.cast (rankJ X 0).symm x.2.2.1, Fin.cast (rankJ X 0).symm x.2.2.2))⟩
  | j + 1, x => ⟨x.1, (x.2.1, (Fin.cast (rankJ X (j + 1)).symm x.2.2.1, Fin.cast (rankJ X (j + 1)).symm x.2.2.2))⟩

theorem idxJ_idxI (j : ℕ) (x : YI X j) : idxJ X j (idxI X j x) = x := by
  cases j <;> rfl

def yL (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    Matrix (Fin (NN X.G.P.m X.t j)) (Fin (NN X.G.P.m X.t j)) (X.Pj j).Xsp :=
  fun a t => MvPolynomial.X (idxI X j ⟨v, (s, (a, t))⟩)

theorem subD_yL (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    (yL X j v s).map (subD X Kc j) = ySub X Kc j v s := by
  ext a t
  simp only [Matrix.map_apply, yL]
  rw [subD_X, idxJ_idxI]

def numB (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) : DA X Kc j :=
  if IsOddPos s then (yMat X Kc j v s).det ^ (exY X j v s).toNat * (YtMat X Kc j v s).det ^ (exT X j v s).toNat
  else (dyMat X Kc j v s).det ^ (X.nuv v (j + 1) s (NN X.G.P.m X.t j)).toNat

def denB (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) : DA X Kc j :=
  if IsOddPos s then (yMat X Kc j v s).det ^ (-exY X j v s).toNat * (YtMat X Kc j v s).det ^ (-exT X j v s).toNat
  else 1

theorem polDel_prod (j : ℕ) (B : ∀ v : X.Pl, Fin (X.G.P.n' v) → (X.Pj j).Xsp) (B' : ∀ v : X.Pl, Fin (X.G.P.n' v) → DA X Kc j)
    (hB : ∀ v s, subD X Kc j (B v s) * numB X Kc j v s = denB X Kc j v s * B' v s) :
    polDel X Kc j (∏ v, ∏ s, B v s) = ∏ v, ∏ s, B' v s := by
  apply polDel_eq
  have hn : numD X Kc j = ∏ v, ∏ s, numB X Kc j v s := rfl
  have hd : denD X Kc j = ∏ v, ∏ s, denB X Kc j v s := rfl
  rw [hn, hd, map_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun s _ => hB v s

def hvOdd (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) (x : Fin (NN X.G.P.m X.t j) → ℕ → X.G.Kf) (c : ℕ) (h : Fin c → ℕ) :
    (X.Pj j).Xsp :=
  ∏ k, (catM (h k) (yL X j v s) fun a i => MvPolynomial.C (x a i)).det

def xd (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) (x : Fin (NN X.G.P.m X.t j) → ℕ → X.G.Kf) :
    Fin (NN X.G.P.m X.t (j + 1)) → ℕ → DA X Kc j :=
  mulC (dMat X Kc j v s).transpose fun a i => algebraMap X.G.Kf (DA X Kc j) (x a i)

def hvOdd' (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) (x : Fin (NN X.G.P.m X.t j) → ℕ → X.G.Kf) (c : ℕ) (h : Fin c → ℕ) :
    DA X Kc j :=
  ∏ k, (catM (h k) (yMat X Kc j v s) (xd X Kc j v s x)).det

theorem subD_hvOdd (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) (hs : IsOddPos s)
    (x : Fin (NN X.G.P.m X.t j) → ℕ → X.G.Kf) (c : ℕ) (h : Fin c → ℕ) :
    subD X Kc j (hvOdd X j v s x c h) =
      ∏ k, (catM (h k) (YtMat X Kc j v s).adjugate fun a i => algebraMap X.G.Kf (DA X Kc j) (x a i)).det := by
  unfold hvOdd
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [AlgHom.map_det]
  congr 1
  have := map_catM (subD X Kc j : (X.Pj j).Xsp →+* DA X Kc j) (h k) (yL X j v s) fun a i => MvPolynomial.C (x a i)
  rw [show (subD X Kc j).mapMatrix (catM (h k) (yL X j v s) fun a i => MvPolynomial.C (x a i)) =
    (catM (h k) (yL X j v s) fun a i => MvPolynomial.C (x a i)).map (subD X Kc j : (X.Pj j).Xsp →+* DA X Kc j) from rfl,
    this]
  congr 1
  · exact (subD_yL X Kc j v s).trans (ySub_odd X Kc j v s hs)
  · funext a i
    exact (subD X Kc j).commutes (x a i)

theorem polDel_hv (j : ℕ) (x : ∀ v : X.Pl, Fin (X.G.P.n' v) → Fin (NN X.G.P.m X.t j) → ℕ → X.G.Kf)
    (c : ∀ v : X.Pl, Fin (X.G.P.n' v) → ℕ) (h : ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)), Fin (c v s) → ℕ)
    (Ge : ∀ v : X.Pl, Fin (X.G.P.n' v) → (X.Pj j).Xsp)
    (hh : ∀ v s, IsOddPos s → ∀ k, h v s k ≤ NN X.G.P.m X.t j)
    (hc : ∀ v s, IsOddPos s → (c v s : ℤ) = cMu X j v s)
    (hs : ∀ v s, IsOddPos s → ((∑ k, h v s k : ℕ) : ℤ) = szMu X j v s) :
    polDel X Kc j (∏ v, ∏ s, if IsOddPos s then hvOdd X j v s (x v s) (c v s) (h v s) else Ge v s) =
      ∏ v, ∏ s, if IsOddPos s then hvOdd' X Kc j v s (x v s) (c v s) (h v s)
        else subD X Kc j (Ge v s) * (dyMat X Kc j v s).det ^ (X.nuv v (j + 1) s (NN X.G.P.m X.t j)).toNat := by
  apply polDel_prod
  intro v s
  unfold numB denB
  by_cases ho : IsOddPos s
  · rw [if_pos ho, if_pos ho, if_pos ho, if_pos ho, subD_hvOdd X Kc j v s ho]
    exact odd_block X Kc j v s _ (c v s) (h v s) (hh v s ho) (hc v s ho) (hs v s ho)
  · rw [if_neg ho, if_neg ho, if_neg ho, if_neg ho, one_mul]

end Hv

section Shape

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

theorem w_le (v : X.Pl) (s : Fin (X.G.P.n' v)) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) : X.Fl.w v a s ≤ X.Fl.w v b s := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hb ih => exact ih.trans (X.Fl.w_mono v s b (ha.trans hb))

theorem blk_le (k1 t j i : ℕ) (h1 : k1 + 1 < i) (h2 : i ≤ NN k1 t (j + 1)) : (i - (k1 + 2)) / (t + 1) + 1 ≤ j + 1 := by
  have : (i - (k1 + 2)) / (t + 1) < j + 1 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.succ_pos t)]
    unfold NN at h2
    show i - (k1 + 2) < (j + 1) * (t + 1)
    omega
  omega

theorem blk_eq (k1 t j i : ℕ) (h0 : NN k1 t j < i) (h2 : i ≤ NN k1 t (j + 1)) : (i - (k1 + 2)) / (t + 1) + 1 = j + 1 := by
  have h1 : k1 + 1 < i := by unfold NN at h0; omega
  have hle := blk_le k1 t j i h1 h2
  have : j ≤ (i - (k1 + 2)) / (t + 1) := by
    rw [Nat.le_div_iff_mul_le (Nat.succ_pos t)]
    unfold NN at h0
    show j * (t + 1) ≤ i - (k1 + 2)
    omega
  omega

theorem neg_last_le_w (v : X.Pl) (s : Fin (X.G.P.n' v)) {b : ℕ} (hb : 1 ≤ b) :
    -(X.G.P.lam0 v s (Fin.last X.G.P.m)) ≤ X.Fl.w v b s :=
  ((le_max_right _ _).trans (X.Fl.w_ge v s)).trans (w_le X v s le_rfl hb)

theorem nuv_nonneg (v : X.Pl) (j : ℕ) (s : Fin (X.G.P.n' v)) (i : ℕ) : 0 ≤ X.nuv v (j + 1) s i := by
  unfold Sys.nuv nu
  split_ifs with h1 h2
  · unfold lamI
    rw [dif_pos h1]
    have a := X.G.P.dom v s (Fin.le_last (⟨i - 1, by omega⟩ : Fin (X.G.P.m + 1)))
    have b := neg_last_le_w X v s (Nat.succ_le_succ (Nat.zero_le j) : 1 ≤ j + 1)
    show 0 ≤ X.G.P.lam0 v s ⟨i - 1, _⟩ + X.Fl.w v (j + 1) s
    linarith
  · have := w_le X v s (Nat.succ_le_succ (Nat.zero_le _) : 1 ≤ (i - (X.G.P.m + 2)) / (X.t + 1) + 1)
      (blk_le X.G.P.m X.t j i h2.1 h2.2)
    show 0 ≤ -X.Fl.w v _ s + X.Fl.w v (j + 1) s
    linarith
  · exact le_rfl

theorem nuv_le_first (v : X.Pl) (j : ℕ) (s : Fin (X.G.P.n' v)) (i : ℕ) : X.nuv v (j + 1) s i ≤ X.nuv v (j + 1) s 1 := by
  have h11 : X.nuv v (j + 1) s 1 = X.G.P.lam0 v s 0 + X.Fl.w v (j + 1) s := by
    unfold Sys.nuv nu
    rw [if_pos ⟨le_rfl, by omega⟩]
    unfold lamI
    rw [dif_pos ⟨le_rfl, by omega⟩]
    rfl
  have hl : X.G.P.lam0 v s (Fin.last X.G.P.m) ≤ X.G.P.lam0 v s 0 := X.G.P.dom v s (Fin.zero_le _)
  have h0 := nuv_nonneg X v j s 1
  rw [h11] at h0 ⊢
  unfold Sys.nuv nu
  split_ifs with h1 h2
  · unfold lamI
    rw [dif_pos h1]
    have a := X.G.P.dom v s (Fin.zero_le (⟨i - 1, by omega⟩ : Fin (X.G.P.m + 1)))
    show X.G.P.lam0 v s ⟨i - 1, _⟩ + X.Fl.w v (j + 1) s ≤ _
    linarith
  · have := neg_last_le_w X v s (Nat.succ_le_succ (Nat.zero_le _) : 1 ≤ (i - (X.G.P.m + 2)) / (X.t + 1) + 1)
    show -X.Fl.w v _ s + X.Fl.w v (j + 1) s ≤ _
    linarith
  · exact h0

theorem nuv_zero (v : X.Pl) (j : ℕ) (s : Fin (X.G.P.n' v)) (i : ℕ) (h0 : NN X.G.P.m X.t j < i) :
    X.nuv v (j + 1) s i = 0 := by
  unfold Sys.nuv nu
  have hk : X.G.P.m + 1 < i := by unfold NN at h0; omega
  rw [if_neg (by omega)]
  split_ifs with h2
  · rw [blk_eq X.G.P.m X.t j i h0 h2.2]
    show -X.Fl.w v (j + 1) s + X.Fl.w v (j + 1) s = 0
    ring
  · rfl

theorem colHt_le (v : X.Pl) (j : ℕ) (s : Fin (X.G.P.n' v)) (k : ℕ) : X.colHt v (j + 1) s k ≤ NN X.G.P.m X.t j := by
  unfold Sys.colHt
  calc _ ≤ (Icc 1 (NN X.G.P.m X.t j)).card := by
        refine Finset.card_le_card fun i hi => ?_
        rw [Finset.mem_filter, Finset.mem_Icc] at hi
        rw [Finset.mem_Icc]
        refine ⟨hi.1.1, ?_⟩
        by_contra hc
        have := nuv_zero X v j s i (not_le.1 hc)
        rw [this] at hi
        have := hi.2
        omega
    _ = _ := by simp

theorem cMu_toNat (v : X.Pl) (j : ℕ) (s : Fin (X.G.P.n' v)) : (((cMu X j v s).toNat : ℕ) : ℤ) = cMu X j v s :=
  Int.toNat_of_nonneg (nuv_nonneg X v j s 1)

theorem sum_colHt (v : X.Pl) (j : ℕ) (s : Fin (X.G.P.n' v)) :
    ((∑ k : Fin (cMu X j v s).toNat, X.colHt v (j + 1) s k.val : ℕ) : ℤ) = szMu X j v s := by
  unfold szMu Sys.colHt
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  have h0 := nuv_nonneg X v j s i
  have h1 : X.nuv v (j + 1) s i ≤ cMu X j v s := nuv_le_first X v j s i
  obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le h0
  have hc := cMu_toNat X v j s
  rw [ha] at h1 ⊢
  have hac : a ≤ (cMu X j v s).toNat := by omega
  rw [Fin.sum_univ_eq_sum_range (fun k => if ((k : ℕ) : ℤ) < (a : ℤ) then (1 : ℤ) else 0) (cMu X j v s).toNat]
  simp only [Nat.cast_lt]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  have : (Finset.range (cMu X j v s).toNat).filter (fun k => k < a) = Finset.range a := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [this, Finset.card_range]

end Shape

section Rule

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc]

def hvEven (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) (x : Fin (NN X.G.P.m X.t j) → ℕ → X.G.Kf) (c : ℕ) (h : Fin c → ℕ)
    (hh : ∀ k, h k ≤ NN X.G.P.m X.t j) : (X.Pj j).Xsp :=
  ∏ k, (Matrix.of fun i t : Fin (h k) => ∑ a, MvPolynomial.C (x a i.val) * yL X j v s a (Fin.castLE (hh k) t)).det

def hvEven' (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) (x : Fin (NN X.G.P.m X.t j) → ℕ → X.G.Kf) (c : ℕ) (h : Fin c → ℕ)
    (hh : ∀ k, h k ≤ NN X.G.P.m X.t j) : DA X Kc j :=
  ∏ k, (Matrix.of fun i t : Fin (h k) =>
    ∑ b, xd X Kc j v s x b i.val * yMat X Kc j v s b (Fin.castLE ((hh k).trans (NN_le X j)) t)).det

theorem pair_dy (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) (x : Fin (NN X.G.P.m X.t j) → ℕ → X.G.Kf) (i : ℕ)
    (t : Fin (NN X.G.P.m X.t j)) :
    ∑ a, algebraMap X.G.Kf (DA X Kc j) (x a i) * dyMat X Kc j v s a t =
      ∑ b, xd X Kc j v s x b i * yMat X Kc j v s b (Fin.castLE (NN_le X j) t) := by
  simp only [dyMat, xd, mulC, Matrix.submatrix_apply, id, Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  ring

theorem subD_hvEven (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) (hs : ¬ IsOddPos s)
    (x : Fin (NN X.G.P.m X.t j) → ℕ → X.G.Kf) (c : ℕ) (h : Fin c → ℕ) (hh : ∀ k, h k ≤ NN X.G.P.m X.t j) :
    subD X Kc j (hvEven X j v s x c h hh) = hvEven' X Kc j v s x c h hh := by
  unfold hvEven hvEven'
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [AlgHom.map_det]
  congr 1
  refine Matrix.ext fun i t => ?_
  have hy : ∀ a t', subD X Kc j (yL X j v s a t') = dyMat X Kc j v s a t' := by
    intro a t'
    have := congrFun (congrFun (subD_yL X Kc j v s) a) t'
    rw [Matrix.map_apply] at this
    rw [this]
    unfold ySub
    rw [if_neg hs]
  show subD X Kc j (∑ a, MvPolynomial.C (x a i.val) * yL X j v s a (Fin.castLE (hh k) t)) = _
  rw [map_sum]
  simp only [map_mul, hy]
  rw [Matrix.of_apply, ← show Fin.castLE (NN_le X j) (Fin.castLE (hh k) t) = Fin.castLE ((hh k).trans (NN_le X j)) t from rfl,
    ← pair_dy]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  exact (subD X Kc j).commutes (x a i.val)

theorem full_col (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) (x : Fin (NN X.G.P.m X.t j) → ℕ → X.G.Kf) :
    (Matrix.of fun i t : Fin (NN X.G.P.m X.t j) =>
      ∑ b, xd X Kc j v s x b i.val * yMat X Kc j v s b (Fin.castLE (NN_le X j) t)).det =
      algebraMap X.G.Kf (DA X Kc j) (Matrix.of fun a i : Fin (NN X.G.P.m X.t j) => x a i.val).det *
        (dyMat X Kc j v s).det := by
  have : (Matrix.of fun i t : Fin (NN X.G.P.m X.t j) =>
      ∑ b, xd X Kc j v s x b i.val * yMat X Kc j v s b (Fin.castLE (NN_le X j) t)) =
      ((Matrix.of fun a i : Fin (NN X.G.P.m X.t j) => x a i.val).map (algebraMap X.G.Kf (DA X Kc j))).transpose *
        dyMat X Kc j v s := by
    refine Matrix.ext fun i t => ?_
    rw [Matrix.of_apply, ← pair_dy, Matrix.mul_apply]
    rfl
  rw [this, Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]

theorem polDel_hv_nu (j : ℕ) (x : ∀ v : X.Pl, Fin (X.G.P.n' v) → Fin (NN X.G.P.m X.t j) → ℕ → X.G.Kf)
    (c : ∀ v : X.Pl, Fin (X.G.P.n' v) → ℕ) (h : ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)), Fin (c v s) → ℕ)
    (hh : ∀ v s k, h v s k ≤ NN X.G.P.m X.t j) :
    polDel X Kc j (∏ v, ∏ s, if IsOddPos s
        then hvOdd X j v s (x v s) (cMu X j v s).toNat (fun k => X.colHt v (j + 1) s k.val)
        else hvEven X j v s (x v s) (c v s) (h v s) (hh v s)) =
      ∏ v, ∏ s, if IsOddPos s
        then hvOdd' X Kc j v s (x v s) (cMu X j v s).toNat (fun k => X.colHt v (j + 1) s k.val)
        else hvEven' X Kc j v s (x v s) (c v s) (h v s) (hh v s) *
          (dyMat X Kc j v s).det ^ (X.nuv v (j + 1) s (NN X.G.P.m X.t j)).toNat := by
  have key := polDel_hv X Kc j x (fun v s => (cMu X j v s).toNat) (fun v s k => X.colHt v (j + 1) s k.val)
    (fun v s => hvEven X j v s (x v s) (c v s) (h v s) (hh v s))
    (fun v s _ k => colHt_le X v j s k.val) (fun v s _ => cMu_toNat X v j s) (fun v s _ => sum_colHt X v j s)
  rw [key]
  refine Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun s _ => ?_
  by_cases ho : IsOddPos s
  · rw [if_pos ho, if_pos ho]
  · rw [if_neg ho, if_neg ho, subD_hvEven X Kc j v s ho]

theorem delF_hv_nu (j : ℕ) (x : ∀ v : X.Pl, Fin (X.G.P.n' v) → Fin (NN X.G.P.m X.t j) → ℕ → X.G.Kf)
    (c : ∀ v : X.Pl, Fin (X.G.P.n' v) → ℕ) (h : ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)), Fin (c v s) → ℕ)
    (hh : ∀ v s k, h v s k ≤ NN X.G.P.m X.t j) (f : MvPowerSeries (X.ZA j) Kc) :
    delF X Kc j (∏ v, ∏ s, if IsOddPos s
        then hvOdd X j v s (x v s) (cMu X j v s).toNat (fun k => X.colHt v (j + 1) s k.val)
        else hvEven X j v s (x v s) (c v s) (h v s) (hh v s)) f =
      pairD X Kc j (∏ v, ∏ s, if IsOddPos s
        then hvOdd' X Kc j v s (x v s) (cMu X j v s).toNat (fun k => X.colHt v (j + 1) s k.val)
        else hvEven' X Kc j v s (x v s) (c v s) (h v s) (hh v s) *
          (dyMat X Kc j v s).det ^ (X.nuv v (j + 1) s (NN X.G.P.m X.t j)).toNat) f := by
  rw [delF_apply, polDel_hv_nu]

end Rule

section Minor

variable {R : Type*} [CommRing R]

theorem det_unit_cols {n m : ℕ} (hm : m ≤ n) (W : Matrix (Fin n) (Fin n) R)
    (hW : ∀ a t : Fin n, m ≤ t.val → W a t = if a = t then 1 else 0) :
    W.det = (Matrix.of fun p q : Fin m => W (Fin.castLE hm p) (Fin.castLE hm q)).det := by
  let e : Fin m ⊕ Fin (n - m) ≃ Fin n := finSumFinEquiv.trans (finCongr (by omega))
  have e1 : ∀ i : Fin m, e (Sum.inl i) = Fin.castLE hm i := fun i => Fin.ext (by simp [e])
  have e2 : ∀ r : Fin (n - m), (e (Sum.inr r)).val = m + r.val := fun r => by simp [e]
  rw [← Matrix.det_submatrix_equiv_self e]
  have hb : W.submatrix e e = Matrix.fromBlocks (Matrix.of fun p q : Fin m => W (Fin.castLE hm p) (Fin.castLE hm q)) 0
      (Matrix.of fun (r : Fin (n - m)) (q : Fin m) => W (e (Sum.inr r)) (Fin.castLE hm q)) 1 := by
    ext a t
    rcases a with a | a <;> rcases t with t | t
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, e1, Matrix.of_apply]
    · rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, hW _ _ (by rw [e2]; omega), if_neg (by simp)]
      rfl
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, e1, Matrix.of_apply]
    · rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, hW _ _ (by rw [e2]; omega), Matrix.one_apply]
      simp only [EmbeddingLike.apply_eq_iff_eq, Sum.inr.injEq]
  rw [hb, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]

open Classical in

theorem initMinor_cat {n m : ℕ} (hm : m ≤ n) (I : Fin m → Fin n) :
    ∃ (u : R) (x : Fin n → ℕ → R), ∀ y : Matrix (Fin n) (Fin n) R,
      (Matrix.of fun p q : Fin m => y (I p) (Fin.castLE hm q)).det = u * (catM (n - m) y x).det := by
  by_cases hI : Function.Injective I
  · let e0 : {a : Fin n // a.val < m} ≃ {b : Fin n // b ∈ Set.range I} :=
      Equiv.ofBijective (fun a => ⟨I ⟨a.1.val, a.2⟩, ⟨_, rfl⟩⟩)
        ⟨fun a b h => by
          have := hI (congrArg Subtype.val h)
          exact Subtype.ext (Fin.ext (by simpa using congrArg Fin.val this)),
         fun b => by
          obtain ⟨b, ⟨q, rfl⟩⟩ := b
          exact ⟨⟨Fin.castLE hm q, q.isLt⟩, rfl⟩⟩
    let π : Equiv.Perm (Fin n) := e0.extendSubtype
    have hπ : ∀ q : Fin m, π (Fin.castLE hm q) = I q := fun q =>
      e0.extendSubtype_apply_of_mem (Fin.castLE hm q) q.isLt
    refine ⟨((Equiv.Perm.sign π : ℤ) : R),
      fun a i => if h : m + i < n then (if a = π ⟨m + i, h⟩ then 1 else 0) else 0, fun y => ?_⟩
    rw [← Matrix.det_permute]
    rw [det_unit_cols hm]
    · congr 1
      ext p q
      have : (Fin.castLE hm q).val < n - (n - m) := by have := q.isLt; simp only [Fin.val_castLE]; omega
      simp only [Matrix.of_apply, Matrix.submatrix_apply, id, catM, this, if_true, hπ]
    · intro a t ht
      have h1 : ¬ t.val < n - (n - m) := by omega
      have h2 : m + (t.val - (n - (n - m))) < n := by have := t.isLt; omega
      simp only [Matrix.submatrix_apply, id, catM, h1, if_false, dif_pos h2, EmbeddingLike.apply_eq_iff_eq]
      congr 1
      apply propext
      constructor
      · rintro rfl; exact Fin.ext (by simp only []; omega)
      · intro h; rw [h]; exact Fin.ext (by simp only []; omega)
  · refine ⟨0, fun _ _ => 0, fun y => ?_⟩
    rw [zero_mul]
    simp only [Function.Injective, not_forall] at hI
    obtain ⟨a, b, hab, hne⟩ := hI
    exact Matrix.det_zero_of_row_eq hne (by funext q; simp only [Matrix.of_apply, hab])

theorem cols_idS {N N' : ℕ} (hN : N ≤ N') (y : Matrix (Fin N') (Fin N') R) (d : Matrix (Fin N) (Fin N') R)
    (sh : Fin N → Fin N') (hsh : ∀ t, (sh t).val = N' - N + t.val) {ι : Type*} (T : Finset ι)
    (x : ι → Fin N → ℕ → R) (h : ι → ℕ) (hh : ∀ k, h k ≤ N) :
    (y.adjugate.submatrix sh id * d.transpose).det ^ T.card * y.det ^ (∑ k ∈ T, (N' - h k)) *
        ∏ k ∈ T, (catM (h k) (y.adjugate.submatrix sh id * d.transpose).adjugate (x k)).det =
      (y.adjugate.submatrix sh id * d.transpose).det ^ (∑ k ∈ T, (N - h k)) * y.det ^ (T.card * (N' - 1)) *
        ∏ k ∈ T, (catM (h k) y (mulC d.transpose (x k))).det := by
  have := Finset.prod_congr (s₁ := T) rfl fun k _ => col_id hN y d sh hsh (x k) (h k) (hh k)
  simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_const, Finset.sum_const,
    smul_eq_mul] at this
  exact this

end Minor

section OddBidet

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc]

theorem catM_full {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    catM n A (fun a i => if a.val = i then (1 : R) else 0) = 1 := by
  ext a t
  simp only [catM, Nat.sub_self, Nat.not_lt_zero, if_false, Nat.sub_zero, Matrix.one_apply, Fin.ext_iff]

theorem odd_bidet (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) (K : ℕ) (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ NN X.G.P.m X.t j) (I : ∀ k, Fin (sz k) → Fin (NN X.G.P.m X.t j))
    (h1 : ((∑ k, sz k : ℕ) : ℤ) = (NN X.G.P.m X.t j : ℤ) * cMu X j v s - szMu X j v s)
    (h2 : (((Finset.univ.filter fun k => 0 < sz k).card : ℕ) : ℤ) ≤ cMu X j v s) :
    (yMat X Kc j v s).det ^ (-exY X j v s).toNat * (YtMat X Kc j v s).det ^ (-exT X j v s).toNat ∣
      (∏ k, (Matrix.of fun p q : Fin (sz k) => (YtMat X Kc j v s).adjugate (I k p) (Fin.castLE (hsz k) q)).det) *
        ((yMat X Kc j v s).det ^ (exY X j v s).toNat * (YtMat X Kc j v s).det ^ (exT X j v s).toNat) := by
  classical
  have hNN : (NN X.G.P.m X.t j) ≤ (NN X.G.P.m X.t (j + 1)) := NN_le X j
  have hN1 : 1 ≤ (NN X.G.P.m X.t (j + 1)) := by unfold NN; omega
  choose u x hux using fun k => initMinor_cat (R := DA X Kc j) (hsz k) (I k)
  set T := Finset.univ.filter fun k : Fin K => 0 < sz k with hT
  obtain ⟨r, hr⟩ : ∃ r : ℕ, (r : ℤ) = cMu X j v s - (T.card : ℤ) := ⟨(cMu X j v s - T.card).toNat, by omega⟩
  have hprod : (∏ k, (Matrix.of fun p q : Fin (sz k) =>
      (YtMat X Kc j v s).adjugate (I k p) (Fin.castLE (hsz k) q)).det) =
      (∏ k ∈ T, u k) * ∏ k ∈ T, (catM ((NN X.G.P.m X.t j) - sz k) (YtMat X Kc j v s).adjugate (x k)).det := by
    rw [← Finset.prod_mul_distrib, hT, Finset.prod_filter]
    refine Finset.prod_congr rfl fun k _ => ?_
    split_ifs with hk
    · exact hux k _
    · have h0 : sz k = 0 := by omega
      have : IsEmpty (Fin (sz k)) := by rw [h0]; infer_instance
      exact Matrix.det_isEmpty
  have key := cols_idS hNN (yMat X Kc j v s) (dMat X Kc j v s) (shiftI X j) (fun _ => rfl) T x (fun k => (NN X.G.P.m X.t j) - sz k)
    (fun k => Nat.sub_le _ _)
  have full := col_id hNN (yMat X Kc j v s) (dMat X Kc j v s) (shiftI X j) (fun _ => rfl)
    (fun a i => if a.val = i then (1 : DA X Kc j) else 0) (NN X.G.P.m X.t j) le_rfl
  rw [← YtMat_eq] at key full
  rw [catM_full, Matrix.det_one, mul_one, Nat.sub_self, pow_zero, one_mul] at full
  set ε := (YtMat X Kc j v s).det with hε
  set δ := (yMat X Kc j v s).det with hδ
  set Qf := (catM (NN X.G.P.m X.t j) (yMat X Kc j v s) (mulC (dMat X Kc j v s).transpose
    fun a i => if a.val = i then (1 : DA X Kc j) else 0)).det with hQf
  set P := ∏ k ∈ T, (catM ((NN X.G.P.m X.t j) - sz k) (YtMat X Kc j v s).adjugate (x k)).det with hP
  set Q := ∏ k ∈ T, (catM ((NN X.G.P.m X.t j) - sz k) (yMat X Kc j v s) (mulC (dMat X Kc j v s).transpose (x k))).det with hQ
  have comb : ε ^ (T.card + r) * δ ^ ((∑ k ∈ T, ((NN X.G.P.m X.t (j + 1)) - ((NN X.G.P.m X.t j) - sz k))) + r * ((NN X.G.P.m X.t (j + 1)) - (NN X.G.P.m X.t j))) * P =
      ε ^ (∑ k ∈ T, ((NN X.G.P.m X.t j) - ((NN X.G.P.m X.t j) - sz k))) * δ ^ (T.card * ((NN X.G.P.m X.t (j + 1)) - 1) + r * ((NN X.G.P.m X.t (j + 1)) - 1)) * (Q * Qf ^ r) := by
    have fr : (ε * δ ^ ((NN X.G.P.m X.t (j + 1)) - (NN X.G.P.m X.t j))) ^ r = (δ ^ ((NN X.G.P.m X.t (j + 1)) - 1) * Qf) ^ r := by rw [full]
    calc _ = (ε ^ T.card * δ ^ (∑ k ∈ T, ((NN X.G.P.m X.t (j + 1)) - ((NN X.G.P.m X.t j) - sz k))) * P) * (ε * δ ^ ((NN X.G.P.m X.t (j + 1)) - (NN X.G.P.m X.t j))) ^ r := by
          rw [pow_add, pow_add, mul_pow, ← pow_mul, mul_comm ((NN X.G.P.m X.t (j + 1)) - (NN X.G.P.m X.t j)) r]; ring
      _ = _ := by rw [key, fr, pow_add, mul_pow, ← pow_mul, mul_comm ((NN X.G.P.m X.t (j + 1)) - 1) r]; ring
  have sT : (∑ k ∈ T, sz k) = ∑ k, sz k := by
    rw [hT, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hk
    · rfl
    · omega
  have c1 : ((∑ k ∈ T, ((NN X.G.P.m X.t j) - ((NN X.G.P.m X.t j) - sz k)) : ℕ) : ℤ) = ((NN X.G.P.m X.t j) : ℤ) * cMu X j v s - szMu X j v s := by
    rw [← h1, ← sT]
    congr 1
    exact Finset.sum_congr rfl fun k _ => Nat.sub_sub_self (hsz k)
  have c2 : ((∑ k ∈ T, ((NN X.G.P.m X.t (j + 1)) - ((NN X.G.P.m X.t j) - sz k)) : ℕ) : ℤ) =
      (T.card : ℤ) * (((NN X.G.P.m X.t (j + 1)) : ℤ) - (NN X.G.P.m X.t j)) + (((NN X.G.P.m X.t j) : ℤ) * cMu X j v s - szMu X j v s) := by
    rw [← h1, ← sT]
    push_cast
    rw [Finset.sum_congr rfl fun k _ => show ((((NN X.G.P.m X.t (j + 1)) - ((NN X.G.P.m X.t j) - sz k) : ℕ)) : ℤ) = (((NN X.G.P.m X.t (j + 1)) : ℤ) - (NN X.G.P.m X.t j)) + sz k by
      have := hsz k; omega]
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have fin := cancel_exp (det_YtMat_ne_zero X Kc j v s) (det_yMat_ne_zero X Kc j v s) comb (exY X j v s) (exT X j v s)
    (by
      rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, c2, Nat.cast_sub hNN, Nat.cast_sub hN1, hr]
      unfold exY
      push_cast
      ring)
    (by
      rw [Nat.cast_add, c1, hr]
      unfold exT
      ring)
  rw [hprod]
  exact ⟨(∏ k ∈ T, u k) * (Q * Qf ^ r), by rw [mul_assoc, fin]; ring⟩

end OddBidet

section Vt

open MvPolynomial Formalism.GradedWeylDivisibility

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc]

theorem card_filter_val_lt {n a : ℕ} (ha : a ≤ n) : (Finset.univ.filter fun t : Fin n => t.val < a).card = a := by
  rw [Finset.card_filter, Fin.sum_univ_eq_sum_range (fun t => if t < a then 1 else 0) n, ← Finset.card_filter]
  have : (Finset.range n).filter (fun t => t < a) = Finset.range a := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [this, Finset.card_range]

theorem sum_shapeDeg {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) : ∑ t : Fin n, shapeDeg sz t = ∑ k, sz k := by
  unfold shapeDeg
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.card_filter, card_filter_val_lt (hsz k)]

variable (j m₀ : ℕ) (hm : m₀ + 1 = NN X.G.P.m X.t j)
  (lam : ∀ v : X.Pl, Fin (X.G.P.n' v) → Fin (m₀ + 1) → ℤ)
  (hlam : ∀ v s (i : Fin (m₀ + 1)), X.nuv v (j + 1) s (i.val + 1) = lam v s i + X.Fl.w v (j + 1) s)

include hlam in
theorem kap_eq (v : X.Pl) (s : Fin (X.G.P.n' v)) (ho : IsOddPos s) (t : Fin (m₀ + 1)) :
    ((nuOf (lamAt (lam v) s) t : ℕ) : ℤ) = cMu X j v s - X.nuv v (j + 1) s (t.rev.val + 1) := by
  have hne : ¬ Even s.val := by
    rw [Nat.not_even_iff]
    exact ho
  have h1 : cMu X j v s = lam v s 0 + X.Fl.w v (j + 1) s := hlam v s 0
  have h2 := nuv_le_first X v j s (t.rev.val + 1)
  unfold nuOf lamAt
  rw [if_neg hne, Int.toNat_of_nonneg]
  · rw [h1, hlam, Fin.rev_last]
    ring
  · rw [Fin.rev_last]
    have : X.nuv v (j + 1) s 1 = cMu X j v s := rfl
    rw [this, h1, hlam] at h2
    linarith

include hm in
theorem sum_nuv (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    ∑ i : Fin (m₀ + 1), X.nuv v (j + 1) s (i.val + 1) = szMu X j v s := by
  unfold szMu
  rw [Fin.sum_univ_eq_sum_range (fun i => X.nuv v (j + 1) s (i + 1)) (m₀ + 1), hm]
  have hsub : Finset.Icc 1 (NN X.G.P.m X.t j) ⊆ Finset.Icc 1 (NN X.G.P.m X.t (j + 1)) :=
    Finset.Icc_subset_Icc le_rfl (NN_le X j)
  rw [← Finset.sum_subset hsub]
  · rw [Finset.range_eq_Ico, Finset.sum_Ico_add' (fun i => X.nuv v (j + 1) s i) 0 (NN X.G.P.m X.t j) 1]
    rfl
  · intro i _ hi
    apply nuv_zero
    rw [Finset.mem_Icc] at hi
    rename_i h1
    rw [Finset.mem_Icc] at h1
    omega

variable (φ : MvPolynomial (Σ v : X.Pl, Fin (X.G.P.n' v) × (Fin (m₀ + 1) × Fin (m₀ + 1))) X.G.Kf →ₐ[X.G.Kf] DA X Kc j)
  (hφ : ∀ v s a t, φ (MvPolynomial.X ⟨v, (s, (a, t))⟩) = ySub X Kc j v s (Fin.cast hm a) (Fin.cast hm t))

theorem dvd_smul' {A : Type*} [CommRing A] [Algebra X.G.Kf A] {a b : A} (c : X.G.Kf) (h : a ∣ b) : a ∣ c • b := by
  rw [Algebra.smul_def]
  exact Dvd.dvd.mul_left h _

include hm hlam hφ in

theorem block_good (v : X.Pl) (s : Fin (X.G.P.n' v)) (F : MvPolynomial (Fin (m₀ + 1) × Fin (m₀ + 1)) X.G.Kf)
    (hF : F ∈ dualWeyl X.G.Kf (m₀ + 1) (m₀ + 1) (nuOf (lamAt (lam v) s))) :
    denB X Kc j v s ∣ φ (rename (fun x => (⟨v, (s, x)⟩ :
      Σ v : X.Pl, Fin (X.G.P.n' v) × (Fin (m₀ + 1) × Fin (m₀ + 1)))) F) * numB X Kc j v s := by
  by_cases ho : IsOddPos s
  swap
  · unfold denB
    rw [if_neg ho]
    exact one_dvd _
  rw [standardMonomialSpanDomain X.G.Kf (m₀ + 1) (m₀ + 1) (nuOf (lamAt (lam v) s))] at hF
  induction hF using Submodule.span_induction with
  | zero => rw [map_zero, map_zero, zero_mul]; exact dvd_zero _
  | add a b _ _ ha hb => rw [map_add, map_add, add_mul]; exact dvd_add ha hb
  | smul c a _ ha => rw [map_smul, map_smul, smul_mul_assoc]; exact dvd_smul' X c ha
  | mem F hF =>
    obtain ⟨K, sz, hsz, I, hshape, rfl⟩ := hF
    unfold denB numB
    rw [if_pos ho, if_pos ho]
    have hsz' : ∀ k, sz k ≤ NN X.G.P.m X.t j := fun k => hm ▸ hsz k
    have himg : φ (rename (fun x => (⟨v, (s, x)⟩ :
        Σ v : X.Pl, Fin (X.G.P.n' v) × (Fin (m₀ + 1) × Fin (m₀ + 1)))) (bideterminant X.G.Kf sz hsz I)) =
        ∏ k, (Matrix.of fun p q : Fin (sz k) =>
          (YtMat X Kc j v s).adjugate (Fin.cast hm (I k p)) (Fin.castLE (hsz' k) q)).det := by
      unfold bideterminant initMinor
      rw [map_prod, map_prod]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [AlgHom.map_det, AlgHom.map_det]
      congr 1
      refine Matrix.ext fun a b => ?_
      show φ (rename _ (MvPolynomial.X (I k a, Fin.castLE (hsz k) b))) = _
      rw [rename_X, hφ, ySub_odd X Kc j v s ho]
      rfl
    rw [himg]
    refine odd_bidet X Kc j v s K sz hsz' (fun k p => Fin.cast hm (I k p)) ?_ ?_
    · rw [← sum_shapeDeg sz hsz, hshape]
      push_cast
      rw [Finset.sum_congr rfl fun t _ => kap_eq X j m₀ lam hlam v s ho t, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        show (∑ x : Fin (m₀ + 1), X.nuv v (j + 1) s (x.rev.val + 1)) = ∑ i : Fin (m₀ + 1), X.nuv v (j + 1) s (i.val + 1) from
          Equiv.sum_comp Fin.revPerm (fun i : Fin (m₀ + 1) => X.nuv v (j + 1) s (i.val + 1)),
        sum_nuv X j m₀ hm v s, hm]
    · have h0 : (Finset.univ.filter fun k => 0 < sz k).card = nuOf (lamAt (lam v) s) 0 := by
        rw [← hshape]
        rfl
      rw [h0, kap_eq X j m₀ lam hlam v s ho 0]
      have := nuv_nonneg X v j s ((0 : Fin (m₀ + 1)).rev.val + 1)
      linarith

def VtG : Submodule X.G.Kf (MvPolynomial (Σ v : X.Pl, Fin (X.G.P.n' v) × (Fin (m₀ + 1) × Fin (m₀ + 1))) X.G.Kf) :=
  Submodule.span X.G.Kf {Z | ∃ F : ∀ v : X.Pl, MvPolynomial (Fin (X.G.P.n' v) × (Fin (m₀ + 1) × Fin (m₀ + 1))) X.G.Kf,
    (∀ v, F v ∈ Vsp X.G.Kf (lam v)) ∧ Z = ∏ v, rename (fun x => (⟨v, x⟩ :
      Σ v : X.Pl, Fin (X.G.P.n' v) × (Fin (m₀ + 1) × Fin (m₀ + 1)))) (F v)}

include hm hlam hφ in

theorem place_good (v : X.Pl) (P : MvPolynomial (Fin (X.G.P.n' v) × (Fin (m₀ + 1) × Fin (m₀ + 1))) X.G.Kf)
    (hP : P ∈ Vsp X.G.Kf (lam v)) :
    (∏ s, denB X Kc j v s) ∣ φ (rename (fun x => (⟨v, x⟩ :
      Σ v : X.Pl, Fin (X.G.P.n' v) × (Fin (m₀ + 1) × Fin (m₀ + 1)))) P) * ∏ s, numB X Kc j v s := by
  unfold Vsp tensorLat at hP
  induction hP using Submodule.span_induction with
  | zero => rw [map_zero, map_zero, zero_mul]; exact dvd_zero _
  | add a b _ _ ha hb => rw [map_add, map_add, add_mul]; exact dvd_add ha hb
  | smul c a _ ha => rw [map_smul, map_smul, smul_mul_assoc]; exact dvd_smul' X c ha
  | mem P hP =>
    obtain ⟨F, hF, rfl⟩ := hP
    rw [map_prod, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_dvd_prod_of_dvd _ _ fun s _ => ?_
    have hFs : F s ∈ (if Antitone (lamAt (lam v) s) then dualWeyl X.G.Kf (m₀ + 1) (m₀ + 1) (nuOf (lamAt (lam v) s))
      else ⊥) := hF s
    unfold blockEmb
    rw [rename_rename]
    split_ifs at hFs with ha
    · exact block_good X Kc j m₀ hm lam hlam φ hφ v s (F s) hFs
    · rw [(Submodule.mem_bot _).1 hFs, map_zero, map_zero, zero_mul]
      exact dvd_zero _

include hm hlam hφ in

theorem vtG_good (G : MvPolynomial (Σ v : X.Pl, Fin (X.G.P.n' v) × (Fin (m₀ + 1) × Fin (m₀ + 1))) X.G.Kf)
    (hG : G ∈ VtG X m₀ lam) : denD X Kc j ∣ φ G * numD X Kc j := by
  unfold VtG at hG
  induction hG using Submodule.span_induction with
  | zero => rw [map_zero, zero_mul]; exact dvd_zero _
  | add a b _ _ ha hb => rw [map_add, add_mul]; exact dvd_add ha hb
  | smul c a _ ha => rw [map_smul, smul_mul_assoc]; exact dvd_smul' X c ha
  | mem G hG =>
    obtain ⟨F, hF, rfl⟩ := hG
    have hn : numD X Kc j = ∏ v, ∏ s, numB X Kc j v s := rfl
    have hd : denD X Kc j = ∏ v, ∏ s, denB X Kc j v s := rfl
    rw [hn, hd, map_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_dvd_prod_of_dvd _ _ fun v _ => place_good X Kc j m₀ hm lam hlam φ hφ v (F v) (hF v)

theorem nuv_low (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) (i : ℕ) (h : i < X.G.P.m + 1) :
    X.nuv v (j + 1) s (i + 1) = X.G.P.lam0 v s ⟨i, h⟩ + X.Fl.w v (j + 1) s := by
  unfold Sys.nuv nu
  rw [if_pos ⟨by omega, by omega⟩]
  unfold lamI
  rw [dif_pos ⟨by omega, by omega⟩]
  rfl

theorem nuv_high (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) (i : ℕ) (h : ¬ i < X.G.P.m + 1)
    (h2 : i + 1 ≤ NN X.G.P.m X.t (j + 1)) :
    X.nuv v (j + 1) s (i + 1) = -X.Fl.w v ((i - (X.G.P.m + 1)) / (X.Fl.t + 1) + 1) s + X.Fl.w v (j + 1) s := by
  unfold Sys.nuv nu
  rw [if_neg (by omega), if_pos ⟨by omega, h2⟩]
  have : i + 1 - (X.G.P.m + 2) = i - (X.G.P.m + 1) := by omega
  rw [this]

theorem vtGood (j : ℕ) (G : (X.Pj j).Xsp) (hG : G ∈ (X.Pj j).Vtup) :
    denD X Kc j ∣ subD X Kc j G * numD X Kc j := by
  cases j with
  | zero =>
    exact vtG_good X Kc 0 X.G.P.m (rankJ X 0) X.G.P.lam0 (fun v s i => nuv_low X 0 v s i.val i.isLt) (subD X Kc 0)
      (fun v s a t => subD_X X Kc 0 _) G hG
  | succ j =>
    refine vtG_good X Kc (j + 1) (X.G.P.m + (j + 1) * (X.Fl.t + 1)) (rankJ X (j + 1))
      (fun v s => liftWt X.Fl.t X.G.P.m (X.G.P.lam0 v s) (fun i => X.Fl.w v i s) (j + 1)) ?_ (subD X Kc (j + 1))
      (fun v s a t => subD_X X Kc (j + 1) _) G hG
    intro v s i
    unfold liftWt
    split_ifs with h
    · exact nuv_low X (j + 1) v s i.val h
    · refine nuv_high X (j + 1) v s i.val h ?_
      have := i.isLt
      have h2 := NN_le X (j + 1)
      have h3 : (X.Fl.Pj (j + 1)).m + 1 = NN X.G.P.m X.t (j + 1) := rankJ X (j + 1)
      have h4 : (X.Fl.Pj (j + 1)).m = X.G.P.m + (j + 1) * (X.Fl.t + 1) := rfl
      omega

theorem polDel_spec (j : ℕ) (G : (X.Pj j).Xsp) (hG : G ∈ (X.Pj j).Vtup) :
    denD X Kc j * polDel X Kc j G = subD X Kc j G * numD X Kc j := by
  obtain ⟨R, hR⟩ := vtGood X Kc j G hG
  rw [polDel_eq X Kc j G R hR, hR]

end Vt

section Deg

open MvPolynomial Formalism.GradedWeylDivisibility Classical

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

theorem wh_rename {σ τ R : Type*} [CommSemiring R] (f : τ → σ) (w : σ → ℕ) {F : MvPolynomial τ R} {d : ℕ}
    (h : IsWeightedHomogeneous (w ∘ f) F d) : IsWeightedHomogeneous w (rename f F) d := by
  intro e he
  obtain ⟨u, rfl, hu⟩ := coeff_rename_ne_zero f F e he
  rw [← h hu]
  show Finsupp.linearCombination ℕ w (u.mapDomain f) = Finsupp.linearCombination ℕ (w ∘ f) u
  rw [Finsupp.linearCombination_mapDomain]

theorem wh_dualWeyl {K : Type*} [CommRing K] (r n : ℕ) (ν : Fin n → ℕ) (c : ℕ) {F : MvPolynomial (Fin r × Fin n) K}
    (hF : F ∈ dualWeyl K r n ν) : IsWeightedHomogeneous (fun _ : Fin r × Fin n => c) F (c * ∑ t, ν t) := by
  intro d hd
  have h1 : Finsupp.weight (colW r n) d = ν := (Submodule.mem_inf.1 hF).1 hd
  rw [← h1, Finsupp.weight_eq_sum, Finsupp.weight_eq_sum]
  simp only [Finset.sum_apply, Pi.smul_apply, colW, smul_eq_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.mul_sum, Finset.sum_pi_single']
  simp [mul_comm]

variable (m₀ : ℕ) (lam : ∀ v : X.Pl, Fin (X.G.P.n' v) → Fin (m₀ + 1) → ℤ)

def wG (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    (Σ v : X.Pl, Fin (X.G.P.n' v) × (Fin (m₀ + 1) × Fin (m₀ + 1))) → ℕ :=
  fun x => if (⟨x.1, x.2.1⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) = ⟨v, s⟩ then 1 else 0

theorem vtG_deg (v : X.Pl) (s : Fin (X.G.P.n' v))
    (G : MvPolynomial (Σ v : X.Pl, Fin (X.G.P.n' v) × (Fin (m₀ + 1) × Fin (m₀ + 1))) X.G.Kf) (hG : G ∈ VtG X m₀ lam) :
    IsWeightedHomogeneous (wG X m₀ v s) G (∑ t, nuOf (lamAt (lam v) s) t) := by
  have hd : (∑ t, nuOf (lamAt (lam v) s) t) = ∑ v' : X.Pl, ∑ s' : Fin (X.G.P.n' v'),
      (if (⟨v', s'⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) = ⟨v, s⟩ then 1 else 0) * ∑ t, nuOf (lamAt (lam v') s') t := by
    rw [Finset.sum_sigma' (Finset.univ : Finset X.Pl) (fun v' => (Finset.univ : Finset (Fin (X.G.P.n' v'))))
      (fun v' s' => (if (⟨v', s'⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) = ⟨v, s⟩ then 1 else 0) *
        ∑ t, nuOf (lamAt (lam v') s') t)]
    rw [Finset.sum_eq_single (⟨v, s⟩ : Σ v : X.Pl, Fin (X.G.P.n' v))]
    · simp
    · intro b _ hb
      have : ¬ ((⟨b.1, b.2⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) = ⟨v, s⟩) := hb
      rw [if_neg this, zero_mul]
    · intro h
      exact absurd (by simp) h
  rw [hd, ← mem_weightedHomogeneousSubmodule]
  unfold VtG at hG
  refine Submodule.span_le.2 ?_ hG
  rintro _ ⟨F, hF, rfl⟩
  rw [SetLike.mem_coe, mem_weightedHomogeneousSubmodule]
  refine IsWeightedHomogeneous.prod _ _ _ fun v' _ => ?_
  have hv := hF v'
  unfold Vsp tensorLat at hv
  rw [← mem_weightedHomogeneousSubmodule]
  refine (Submodule.span_le (p := Submodule.comap (rename (fun x => (⟨v', x⟩ :
      Σ v : X.Pl, Fin (X.G.P.n' v) × (Fin (m₀ + 1) × Fin (m₀ + 1)))) :
        MvPolynomial _ X.G.Kf →ₐ[X.G.Kf] MvPolynomial _ X.G.Kf).toLinearMap
      (weightedHomogeneousSubmodule X.G.Kf (wG X m₀ v s) _))).2 ?_ hv
  rintro _ ⟨Fs, hFs, rfl⟩
  show rename _ (∏ s', blockEmb X.G.Kf s' (Fs s')) ∈ weightedHomogeneousSubmodule X.G.Kf (wG X m₀ v s) _
  rw [mem_weightedHomogeneousSubmodule, map_prod]
  refine IsWeightedHomogeneous.prod _ _ _ fun s' _ => ?_
  unfold blockEmb
  rw [rename_rename]
  apply wh_rename
  have hw : (wG X m₀ v s ∘ ((fun x => (⟨v', x⟩ : Σ v : X.Pl, Fin (X.G.P.n' v) × (Fin (m₀ + 1) × Fin (m₀ + 1)))) ∘
      fun y : Fin (m₀ + 1) × Fin (m₀ + 1) => (s', y))) =
      fun _ => (if (⟨v', s'⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) = ⟨v, s⟩ then 1 else 0) := rfl
  rw [hw]
  have h1 : Fs s' ∈ (if Antitone (lamAt (lam v') s') then dualWeyl X.G.Kf (m₀ + 1) (m₀ + 1) (nuOf (lamAt (lam v') s'))
      else ⊥) := hFs s'
  split_ifs at h1 with ha
  · exact wh_dualWeyl (m₀ + 1) (m₀ + 1) (nuOf (lamAt (lam v') s'))
      (if (⟨v', s'⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) = ⟨v, s⟩ then 1 else 0) h1
  · rw [(Submodule.mem_bot _).1 h1]
    exact isWeightedHomogeneous_zero _ _ _

theorem sum_kap (j : ℕ) (hm : m₀ + 1 = NN X.G.P.m X.t j)
    (hlam : ∀ v s (i : Fin (m₀ + 1)), X.nuv v (j + 1) s (i.val + 1) = lam v s i + X.Fl.w v (j + 1) s)
    (v : X.Pl) (s : Fin (X.G.P.n' v)) (ho : IsOddPos s) :
    ((∑ t, nuOf (lamAt (lam v) s) t : ℕ) : ℤ) = (NN X.G.P.m X.t j : ℤ) * cMu X j v s - szMu X j v s := by
  push_cast
  rw [Finset.sum_congr rfl fun t _ => kap_eq X j m₀ lam hlam v s ho t, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    show (∑ x : Fin (m₀ + 1), X.nuv v (j + 1) s (x.rev.val + 1)) = ∑ i : Fin (m₀ + 1), X.nuv v (j + 1) s (i.val + 1) from
      Equiv.sum_comp Fin.revPerm (fun i : Fin (m₀ + 1) => X.nuv v (j + 1) s (i.val + 1)),
    sum_nuv X j m₀ hm v s, hm]

def wBk (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    (Σ v : Fin (X.Fl.Pj j).nV, Fin ((X.Fl.Pj j).n' v) × (Fin ((X.Fl.Pj j).m + 1) × Fin ((X.Fl.Pj j).m + 1))) → ℕ :=
  fun x => if (⟨(idxJ X j x).1, (idxJ X j x).2.1⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) = ⟨v, s⟩ then 1 else 0

theorem vtOddDeg (j : ℕ) (G : (X.Pj j).Xsp) (hG : G ∈ (X.Pj j).Vtup) (v : X.Pl) (s : Fin (X.G.P.n' v)) (ho : IsOddPos s) :
    ∃ d : ℕ, (d : ℤ) = (NN X.G.P.m X.t j : ℤ) * cMu X j v s - szMu X j v s ∧
      IsWeightedHomogeneous (wBk X j v s) G d := by
  cases j with
  | zero =>
    exact ⟨_, sum_kap X X.G.P.m X.G.P.lam0 0 (rankJ X 0) (fun v s i => nuv_low X 0 v s i.val i.isLt) v s ho,
      vtG_deg X X.G.P.m X.G.P.lam0 v s G hG⟩
  | succ j =>
    have hlam : ∀ v s (i : Fin (X.G.P.m + (j + 1) * (X.Fl.t + 1) + 1)), X.nuv v (j + 1 + 1) s (i.val + 1) =
        liftWt X.Fl.t X.G.P.m (X.G.P.lam0 v s) (fun i => X.Fl.w v i s) (j + 1) i + X.Fl.w v (j + 1 + 1) s := by
      intro v s i
      unfold liftWt
      split_ifs with h
      · exact nuv_low X (j + 1) v s i.val h
      · refine nuv_high X (j + 1) v s i.val h ?_
        have := i.isLt
        have h2 := NN_le X (j + 1)
        have h3 : (X.Fl.Pj (j + 1)).m + 1 = NN X.G.P.m X.t (j + 1) := rankJ X (j + 1)
        have h4 : (X.Fl.Pj (j + 1)).m = X.G.P.m + (j + 1) * (X.Fl.t + 1) := rfl
        omega
    exact ⟨_, sum_kap X (X.G.P.m + (j + 1) * (X.Fl.t + 1))
        (fun v s => liftWt X.Fl.t X.G.P.m (X.G.P.lam0 v s) (fun i => X.Fl.w v i s) (j + 1)) (j + 1) (rankJ X (j + 1)) hlam v s ho,
      vtG_deg X (X.G.P.m + (j + 1) * (X.Fl.t + 1))
        (fun v s => liftWt X.Fl.t X.G.P.m (X.G.P.lam0 v s) (fun i => X.Fl.w v i s) (j + 1)) v s G hG⟩

end Deg

end Formalism.L2.G.Pend
