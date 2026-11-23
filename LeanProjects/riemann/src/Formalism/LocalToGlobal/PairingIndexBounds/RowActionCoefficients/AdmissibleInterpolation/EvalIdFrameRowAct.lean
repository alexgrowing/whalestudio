import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.WeylComplementInDetCoeffSpan

open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.L2.G.Model.TS Formalism.L2.G.Pend

namespace BidetPairing

section Heights

variable {n : ℕ} {ν : Fin n → ℕ}

theorem colH_ge (hν : Antitone ν) {k : ℕ} (t : Fin n) (h : k < ν t) : t.val + 1 ≤ colH ν k := by
  unfold colH
  have hsub : Finset.Iic t ⊆ Finset.univ.filter fun u : Fin n => k < ν u := by
    intro u hu
    rw [Finset.mem_Iic] at hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact lt_of_lt_of_le h (hν hu)
  have := Finset.card_le_card hsub
  rwa [Fin.card_Iic] at this

theorem colH_le_of (hν : Antitone ν) {k : ℕ} (t : Fin n) (h : ν t ≤ k) : colH ν k ≤ t.val := by
  unfold colH
  have hsub : (Finset.univ.filter fun u : Fin n => k < ν u) ⊆ Finset.Iio t := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    rw [Finset.mem_Iio]
    by_contra hut
    push Not at hut
    have := hν hut
    omega
  have := Finset.card_le_card hsub
  rwa [Fin.card_Iio] at this

theorem lt_colH_iff (hν : Antitone ν) (k : ℕ) (t : Fin n) : t.val < colH ν k ↔ k < ν t := by
  constructor
  · intro h
    by_contra h'
    push Not at h'
    have := colH_le_of hν t h'
    omega
  · intro h
    have := colH_ge hν t h
    omega

theorem succ_lt_colH_iff (hν : Antitone ν) (k : ℕ) (s : Fin n) : s.val + 1 < colH ν k ↔ k < nuNext ν s := by
  unfold nuNext
  split_ifs with h
  · exact lt_colH_iff hν k ⟨s.val + 1, h⟩
  · have := colH_le ν k
    constructor
    · intro h'; omega
    · intro h'; omega

theorem colH_eq_iff (hν : Antitone ν) (k : ℕ) (s : Fin n) : colH ν k = s.val + 1 ↔ nuNext ν s ≤ k ∧ k < ν s := by
  have h1 := lt_colH_iff hν k s
  have h2 := succ_lt_colH_iff hν k s
  constructor
  · intro h
    refine ⟨?_, h1.1 (by omega)⟩
    by_contra h'
    push Not at h'
    have := h2.2 h'
    omega
  · rintro ⟨ha, hb⟩
    have := h1.2 hb
    have : ¬ (s.val + 1 < colH ν k) := fun h' => by have := h2.1 h'; omega
    omega

theorem nuNext_le (hν : Antitone ν) (s : Fin n) : nuNext ν s ≤ ν s := by
  unfold nuNext
  split_ifs with h
  · exact hν (Fin.le_def.2 (by simp))
  · exact Nat.zero_le _

end Heights

theorem card_fin_filter (c : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (Finset.univ.filter fun k : Fin c => p k.val).card = ((Finset.range c).filter p).card := by
  rw [← Finset.card_map Fin.valEmbedding]
  congr 1
  ext a
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.isLt, hk⟩
  · rintro ⟨ha, hp⟩
    exact ⟨⟨a, ha⟩, hp, rfl⟩

theorem card_fin_Ico (c a b : ℕ) (hb : b ≤ c) :
    (Finset.univ.filter fun k : Fin c => a ≤ k.val ∧ k.val < b).card = b - a := by
  rw [card_fin_filter c (fun k => a ≤ k ∧ k < b)]
  have : (Finset.range c).filter (fun k => a ≤ k ∧ k < b) = Finset.Ico a b := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [this, Nat.card_Ico]

theorem card_fin_lt (c m : ℕ) (hm : m ≤ c) : (Finset.univ.filter fun k : Fin c => k.val < m).card = m := by
  have := card_fin_Ico c 0 m hm
  simp only [Nat.zero_le, true_and, Nat.sub_zero] at this
  exact this

theorem card_colH_eq {n : ℕ} {ν : Fin n → ℕ} (hν : Antitone ν) (c : ℕ) (hc : ∀ t, ν t ≤ c) (s : Fin n) :
    (Finset.univ.filter fun k : Fin c => colH ν k.val = s.val + 1).card = ν s - nuNext ν s := by
  have : (Finset.univ.filter fun k : Fin c => colH ν k.val = s.val + 1) =
      Finset.univ.filter fun k : Fin c => nuNext ν s ≤ k.val ∧ k.val < ν s := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact colH_eq_iff hν k.val s
  rw [this, card_fin_Ico c _ _ (hc s)]

theorem prod_colH {M : Type*} [CommMonoid M] {n : ℕ} {ν : Fin n → ℕ} (hν : Antitone ν) (c : ℕ) (hc : ∀ t, ν t ≤ c)
    (F : ℕ → M) (hF : F 0 = 1) :
    ∏ k : Fin c, F (colH ν k.val) = ∏ s : Fin n, F (s.val + 1) ^ (ν s - nuNext ν s) := by
  classical
  let g : Fin c → Fin (n + 1) := fun k => ⟨colH ν k.val, Nat.lt_succ_of_le (colH_le ν k.val)⟩
  have h1 : ∏ k : Fin c, F (colH ν k.val) = ∏ j : Fin (n + 1), ∏ k ∈ Finset.univ.filter (fun k => g k = j), F j.val := by
    rw [← Finset.prod_fiberwise Finset.univ g (fun k => F (colH ν k.val))]
    refine Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun k hk => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    rw [← hk]
  rw [h1, Fin.prod_univ_succ]
  simp only [Finset.prod_const, Fin.val_zero, hF, one_pow, one_mul, Fin.val_succ]
  refine Finset.prod_congr rfl fun s _ => ?_
  congr 1
  rw [← card_colH_eq hν c hc s]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, g, Fin.ext_iff, Fin.val_succ]

theorem rowAct_X' {R : Type*} [CommRing R] {r n : ℕ} (g : Matrix (Fin r) (Fin r) R) (v : Fin r × Fin n) :
    rowAct R g (X v) = ∑ b : Fin r, C (g v.1 b) * X (b, v.2) := by
  unfold rowAct
  rw [aeval_X]

theorem rowAct_lpMinor {R : Type*} [CommRing R] {n : ℕ} (g : Matrix (Fin n) (Fin n) R) (s : ℕ) (hs : s ≤ n) :
    rowAct R g (lpMinor R s hs hs) =
      (Matrix.of fun p q : Fin s => ∑ b : Fin n, C (g (Fin.castLE hs p) b) * X (b, Fin.castLE hs q)).det := by
  unfold lpMinor
  rw [AlgHom.map_det]
  congr 1
  ext p q
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rowAct_X']

theorem eval_idFrame_rowAct {R : Type*} [CommRing R] {n : ℕ} (g : Matrix (Fin n) (Fin n) R)
    (F : MvPolynomial (Fin n × Fin n) R) :
    eval (idFrame R n n) (rowAct R g F) = eval (fun v => g v.1 v.2) F := by
  have h : (aeval (idFrame R n n) : MvPolynomial (Fin n × Fin n) R →ₐ[R] R).comp (rowAct R g) =
      aeval (fun v : Fin n × Fin n => g v.1 v.2) := by
    unfold rowAct
    rw [comp_aeval]
    congr 1
    funext v
    simp only [map_sum, map_mul, aeval_C, aeval_X, idFrame, Fin.val_inj,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  exact congrArg (fun φ : MvPolynomial (Fin n × Fin n) R →ₐ[R] R => φ F) h

theorem hvE_eq (K : Type) [CommRing K] (n : ℕ) (ν : Fin n → ℕ) (hν : Antitone ν) (c : ℕ) (hc : ∀ t, ν t ≤ c)
    (x : Fin n → ℕ → K) :
    hvE (fun a i => C (x a i)) (yV K n) c (fun k => colH ν k.val) (fun k => colH_le ν k.val) =
      rowAct K (Matrix.of fun i a : Fin n => x a i.val) (hw K le_rfl ν) := by
  let F : ℕ → MvPolynomial (Fin n × Fin n) K := fun m => if h : m ≤ n then lpMinor K m h h else 1
  have hF : F 0 = 1 := by simp only [F, Nat.zero_le, dif_pos]; unfold lpMinor; exact Matrix.det_isEmpty
  have hhw : hw K le_rfl ν = ∏ k : Fin c, F (colH ν k.val) := by
    rw [prod_colH hν c hc F hF]
    unfold hw
    refine Finset.prod_congr rfl fun s _ => ?_
    simp only [F, dif_pos (show s.val + 1 ≤ n from s.isLt)]
  rw [hhw, map_prod]
  unfold hvE
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [F, dif_pos (colH_le ν k.val)]
  rw [rowAct_lpMinor]
  rfl

section Compl

variable {n : ℕ} {μ : Fin n → ℕ}

theorem kap_antitone (hμ : Antitone μ) (c : ℕ) : Antitone fun t : Fin n => c - μ t.rev := by
  intro a b hab
  have h1 : b.rev ≤ a.rev := Fin.rev_le_rev.2 hab
  have h2 := hμ h1
  show c - μ b.rev ≤ c - μ a.rev
  omega

theorem colH_kap (c : ℕ) (hc : ∀ t, μ t ≤ c) (k : Fin c) :
    n - colH μ k.val = colH (fun t : Fin n => c - μ t.rev) (Fin.rev k).val := by
  have h1 : colH (fun t : Fin n => c - μ t.rev) (Fin.rev k).val =
      (Finset.univ.filter fun u : Fin n => ¬ k.val < μ u).card := by
    unfold colH
    apply Finset.card_equiv Fin.revPerm
    intro t
    have := hc t.rev
    have := k.isLt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.revPerm_apply, Fin.val_rev]
    constructor
    · intro h; omega
    · intro h; omega
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun u : Fin n => k.val < μ u)
  rw [Finset.card_univ, Fintype.card_fin] at h2
  rw [h1]
  unfold colH
  omega

theorem prod_kap {M : Type*} [CommMonoid M] (hμ : Antitone μ) (c : ℕ) (hc : ∀ t, μ t ≤ c) (F : ℕ → M)
    (hF : F 0 = 1) :
    ∏ k : Fin c, F (n - colH μ k.val) =
      ∏ s : Fin n, F (s.val + 1) ^ ((fun t : Fin n => c - μ t.rev) s - nuNext (fun t : Fin n => c - μ t.rev) s) := by
  refine Eq.trans ?_ (prod_colH (kap_antitone hμ c) c (fun t => Nat.sub_le _ _) F hF)
  exact Fintype.prod_equiv Fin.revPerm _ _ fun k => by rw [colH_kap c hc k, Fin.revPerm_apply]

end Compl

theorem shape_odd_holds : ShapeO := by
  intro n μ hμ c hc
  funext t
  unfold shapeDeg
  rw [← card_fin_lt c (c - μ t.rev) (Nat.sub_le _ _)]
  apply Finset.card_equiv Fin.revPerm
  intro k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.revPerm_apply]
  rw [colH_kap c hc k, lt_colH_iff (kap_antitone hμ c)]

theorem catM_congr {A : Type*} [CommRing A] {n : ℕ} (l : ℕ) (Y : Matrix (Fin n) (Fin n) A) (x x' : Fin n → ℕ → A)
    (hx : ∀ a i, i < n → x a i = x' a i) : catM l Y x = catM l Y x' := by
  ext a t
  have := t.isLt
  unfold catM
  split_ifs
  · rfl
  · exact hx a _ (by omega)

theorem det_catM_block {A : Type*} [CommRing A] {n : ℕ} (h : ℕ) (hh : h ≤ n) (W : Matrix (Fin n) (Fin n) A)
    (z : Fin n → ℕ → A) (hz : ∀ (a : Fin n) (i : ℕ), a.val < n - h → i < h → z a i = 0) :
    (catM h W z).det =
      (Matrix.of fun p q : Fin (n - h) => W (Fin.castLE (Nat.sub_le n h) p) (Fin.castLE (Nat.sub_le n h) q)).det *
        (Matrix.of fun r s : Fin h => z ⟨n - h + r.val, by have := r.isLt; omega⟩ s.val).det := by
  let e : Fin (n - h) ⊕ Fin h ≃ Fin n := finSumFinEquiv.trans (finCongr (by omega))
  have e1 : ∀ i : Fin (n - h), e (Sum.inl i) = Fin.castLE (Nat.sub_le n h) i := fun i => Fin.ext (by simp [e])
  have e2 : ∀ r : Fin h, e (Sum.inr r) = ⟨n - h + r.val, by have := r.isLt; omega⟩ := fun r => Fin.ext (by simp [e])
  rw [← Matrix.det_submatrix_equiv_self e]
  have hb : (catM h W z).submatrix e e = Matrix.fromBlocks
      (Matrix.of fun p q : Fin (n - h) => W (Fin.castLE (Nat.sub_le n h) p) (Fin.castLE (Nat.sub_le n h) q)) 0
      (Matrix.of fun (r : Fin h) (q : Fin (n - h)) => W (e (Sum.inr r)) (Fin.castLE (Nat.sub_le n h) q))
      (Matrix.of fun r s : Fin h => z ⟨n - h + r.val, by have := r.isLt; omega⟩ s.val) := by
    ext a t
    rcases a with a | a <;> rcases t with t | t
    · rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, e1, e1, Matrix.of_apply]
      unfold catM
      rw [if_pos (by simp)]
    · rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, e1, e2, Matrix.zero_apply]
      unfold catM
      rw [if_neg (by simp)]
      exact hz _ _ (by simp) (by simp)
    · rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, e1, Matrix.of_apply]
      unfold catM
      rw [if_pos (by simp)]
    · rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, e2, e2, Matrix.of_apply]
      unfold catM
      rw [if_neg (by simp)]
      simp
  rw [hb, Matrix.det_fromBlocks_zero₁₂]

theorem mulC_one' {A : Type*} [CommRing A] {n : ℕ} (x : Fin n → ℕ → A) :
    mulC (1 : Matrix (Fin n) (Fin n) A) x = x := by
  funext a i
  simp [mulC, Matrix.one_apply]

theorem det_catM_inv {A : Type*} [CommRing A] {n : ℕ} (h : ℕ) (hh : h ≤ n) (x : Fin n → ℕ → A)
    (Xm Z : Matrix (Fin n) (Fin n) A) (hXm : ∀ a t, Xm a t = x a (n - 1 - t.val)) (hZX : Z * Xm = 1)
    (hXZ : Xm * Z = 1) (Y : Matrix (Fin n) (Fin n) A) :
    (catM h Y x).det = (catM h Xm x).det *
      (Matrix.of fun p q : Fin (n - h) =>
        (Z * Y) (Fin.castLE (Nat.sub_le n h) p) (Fin.castLE (Nat.sub_le n h) q)).det := by
  have hz : ∀ (a : Fin n) (i : ℕ), a.val < n - h → i < h → mulC Z x a i = 0 := by
    intro a i ha hi
    have h1 : mulC Z x a i = (Z * Xm) a ⟨n - 1 - i, by omega⟩ := by
      simp only [mulC, Matrix.mul_apply, hXm]
      refine Finset.sum_congr rfl fun b _ => ?_
      congr 2
      omega
    rw [h1, hZX, Matrix.one_apply, if_neg]
    intro hEq
    have h2 := congrArg Fin.val hEq
    simp only at h2
    omega
  have key : ∀ Y : Matrix (Fin n) (Fin n) A, (catM h Y x).det = Xm.det *
      ((Matrix.of fun p q : Fin (n - h) =>
        (Z * Y) (Fin.castLE (Nat.sub_le n h) p) (Fin.castLE (Nat.sub_le n h) q)).det *
        (Matrix.of fun r s : Fin h => mulC Z x ⟨n - h + r.val, by have := r.isLt; omega⟩ s.val).det) := by
    intro Y
    have hc : catM h Y x = Xm * catM h (Z * Y) (mulC Z x) := by
      rw [mul_catM, ← Matrix.mul_assoc, hXZ, Matrix.one_mul, ← mulC_mul, hXZ, mulC_one']
    rw [hc, Matrix.det_mul, det_catM_block h hh _ _ hz]
  have h1 : (Matrix.of fun p q : Fin (n - h) =>
      (Z * Xm) (Fin.castLE (Nat.sub_le n h) p) (Fin.castLE (Nat.sub_le n h) q)).det = 1 := by
    rw [hZX]
    have : (Matrix.of fun p q : Fin (n - h) =>
        (1 : Matrix (Fin n) (Fin n) A) (Fin.castLE (Nat.sub_le n h) p) (Fin.castLE (Nat.sub_le n h) q)) = 1 := by
      ext p q
      simp [Matrix.one_apply, Fin.castLE_inj]
    rw [this, Matrix.det_one]
  rw [key Y, key Xm, h1]
  ring

theorem minor_mul_unitM {R : Type*} [CommRing R] {n m : ℕ} (hm : m ≤ n) (Z : Matrix (Fin n) (Fin n) R)
    (I : Fin m → Fin n) :
    (Matrix.of fun p q : Fin m => (Z * unitM R I) (Fin.castLE hm p) (Fin.castLE hm q)) =
      Matrix.of fun p q : Fin m => Z (Fin.castLE hm p) (I q) := by
  ext p q
  simp [Matrix.mul_apply, unitM]

theorem eval_bidet {R : Type*} [CommRing R] {n c : ℕ} (sz : Fin c → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin n) (f : Fin n × Fin n → R) :
    eval f (bideterminant R sz hsz I) = ∏ k, (Matrix.of fun p q : Fin (sz k) => f (I k p, Fin.castLE (hsz k) q)).det := by
  unfold bideterminant initMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp [eval_X]

def lhsO (A : Type) [CommRing A] (n : ℕ) (μ : Fin n → ℕ) (c : ℕ) (x : Fin n → ℕ → A)
    (I : ∀ k : Fin c, Fin (n - colH μ k.val) → Fin n) : A :=
  fockR (hvO (fun a i => C (x a i)) (yV A n) c (fun k => colH μ k.val))
    (bideterminant A (fun k : Fin c => n - colH μ k.val) (fun _ => Nat.sub_le _ _) I)

def rhsO (A : Type) [CommRing A] (n : ℕ) (μ : Fin n → ℕ) (c : ℕ) (x : Fin n → ℕ → A)
    (I : ∀ k : Fin c, Fin (n - colH μ k.val) → Fin n) : A :=
  (∏ k : Fin c, (catM (colH μ k.val) (unitM A (I k)) x).det) *
    fockR (hw A le_rfl fun t : Fin n => c - μ t.rev) (hw A le_rfl fun t : Fin n => c - μ t.rev)

theorem hvO_eq_inv (L : Type) [CommRing L] (n : ℕ) (μ : Fin n → ℕ) (hμ : Antitone μ) (c : ℕ)
    (hc : ∀ t, μ t ≤ c) (x : Fin n → ℕ → L) (Z : Matrix (Fin n) (Fin n) L)
    (hZX : Z * Matrix.of (fun a t : Fin n => x a (n - 1 - t.val)) = 1)
    (hXZ : Matrix.of (fun a t : Fin n => x a (n - 1 - t.val)) * Z = 1) :
    hvO (fun a i => C (x a i)) (yV L n) c (fun k => colH μ k.val) =
      C (∏ k : Fin c, (catM (colH μ k.val) (Matrix.of fun a t : Fin n => x a (n - 1 - t.val)) x).det) *
        rowAct L Z (hw L le_rfl fun t : Fin n => c - μ t.rev) := by
  let F : ℕ → MvPolynomial (Fin n × Fin n) L := fun m => if h : m ≤ n then lpMinor L m h h else 1
  have hF : F 0 = 1 := by simp only [F, Nat.zero_le, dif_pos]; unfold lpMinor; exact Matrix.det_isEmpty
  have hhw : hw L le_rfl (fun t : Fin n => c - μ t.rev) = ∏ k : Fin c, F (n - colH μ k.val) := by
    rw [prod_kap hμ c hc F hF]
    unfold hw
    refine Finset.prod_congr rfl fun s _ => ?_
    simp only [F, dif_pos (show s.val + 1 ≤ n from s.isLt)]
  have hZX' : Z.map (C (σ := Fin n × Fin n)) * (Matrix.of (fun a t : Fin n => x a (n - 1 - t.val))).map (C (σ := Fin n × Fin n)) = 1 := by
    rw [← Matrix.map_mul, hZX, Matrix.map_one _ (map_zero _) (map_one _)]
  have hXZ' : (Matrix.of (fun a t : Fin n => x a (n - 1 - t.val))).map (C (σ := Fin n × Fin n)) * Z.map (C (σ := Fin n × Fin n)) = 1 := by
    rw [← Matrix.map_mul, hXZ, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [hhw, map_prod, map_prod, ← Finset.prod_mul_distrib]
  unfold hvO
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [F, dif_pos (Nat.sub_le n (colH μ k.val))]
  rw [rowAct_lpMinor, det_catM_inv (colH μ k.val) (colH_le μ k.val) (fun a i => C (x a i)) _ (Z.map (C (σ := Fin n × Fin n)))
    (fun a t => rfl) hZX' hXZ' (yV L n)]
  congr 1
  · rw [RingHom.map_det, RingHom.mapMatrix_apply, map_catM]
    rfl

theorem fockR_smul' {σ R : Type} [CommRing R] (a : R) (f g : MvPolynomial σ R) : fockR (a • f) g = a * fockR f g :=
  (Top.fockRBilin σ R f 0 g a).2.1

theorem pairO_inv (L : Type) [Field L] [CharZero L] (n : ℕ) (μ : Fin n → ℕ) (hμ : Antitone μ) (c : ℕ)
    (hc : ∀ t, μ t ≤ c) (x : Fin n → ℕ → L) (Z : Matrix (Fin n) (Fin n) L)
    (hZX : Z * Matrix.of (fun a t : Fin n => x a (n - 1 - t.val)) = 1)
    (hXZ : Matrix.of (fun a t : Fin n => x a (n - 1 - t.val)) * Z = 1)
    (I : ∀ k : Fin c, Fin (n - colH μ k.val) → Fin n) : lhsO L n μ c x I = rhsO L n μ c x I := by
  have hB : bideterminant L (fun k : Fin c => n - colH μ k.val) (fun _ => Nat.sub_le _ _) I ∈
      dualWeyl L n n (fun t : Fin n => c - μ t.rev) := by
    have := bidetMem L n n c _ (fun _ => Nat.sub_le _ _) I
    rwa [shape_odd_holds n μ hμ c hc] at this
  unfold lhsO rhsO
  rw [hvO_eq_inv L n μ hμ c hc x Z hZX hXZ, C_mul', fockR_smul', Top.fockRRowAct,
    Top.fock_pairing_highest_weight L n n le_rfl _ (kap_antitone hμ c) _ (dualWeylRowStable L n n _ _ _ hB), eval_idFrame_rowAct,
    eval_bidet]
  have hR : ∀ k : Fin c, (catM (colH μ k.val) (unitM L (I k)) x).det =
      (catM (colH μ k.val) (Matrix.of fun a t : Fin n => x a (n - 1 - t.val)) x).det *
        (Matrix.of fun p q : Fin (n - colH μ k.val) => Z (Fin.castLE (Nat.sub_le _ _) q) (I k p)).det := by
    intro k
    rw [det_catM_inv _ (colH_le μ k.val) x _ Z (fun a t => rfl) hZX hXZ, minor_mul_unitM]
    congr 1
    rw [← Matrix.det_transpose]
    rfl
  rw [Finset.prod_congr rfl fun k _ => hR k, Finset.prod_mul_distrib]
  simp only [Matrix.transpose_apply]
  ring

section Maps

variable {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)

theorem map_lpMinor' {r n : ℕ} (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    map f (lpMinor A s hr hn) = lpMinor B s hr hn := by
  unfold lpMinor
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp [map_X]

theorem map_hw' {n : ℕ} (ν : Fin n → ℕ) : map f (hw A le_rfl ν) = hw B le_rfl ν := by
  unfold hw
  simp only [map_prod, map_pow, map_lpMinor']

theorem map_bidet' {n c : ℕ} (sz : Fin c → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin n) :
    map f (bideterminant A sz hsz I) = bideterminant B sz hsz I := by
  unfold bideterminant initMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp [map_X]

theorem map_hvO' {n : ℕ} (x : Fin n → ℕ → A) (c : ℕ) (h : Fin c → ℕ) :
    map f (hvO (fun a i => C (x a i)) (yV A n) c h) = hvO (fun a i => C (f (x a i))) (yV B n) c h := by
  unfold hvO
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hy : (yV A n).map (map f) = yV B n := by
    ext a t
    simp [yV, map_X]
  rw [RingHom.map_det, RingHom.mapMatrix_apply, map_catM, hy]
  simp only [map_C]

theorem map_unitM' {n m : ℕ} (I : Fin m → Fin n) : (unitM A I).map f = unitM B I := by
  ext a t
  simp only [Matrix.map_apply, unitM]
  split_ifs <;> simp

theorem map_lhsO {n : ℕ} (μ : Fin n → ℕ) (c : ℕ) (x : Fin n → ℕ → A)
    (I : ∀ k : Fin c, Fin (n - colH μ k.val) → Fin n) :
    f (lhsO A n μ c x I) = lhsO B n μ c (fun a i => f (x a i)) I := by
  unfold lhsO
  rw [← Top.fockRMap, map_hvO', map_bidet']

theorem map_rhsO {n : ℕ} (μ : Fin n → ℕ) (c : ℕ) (x : Fin n → ℕ → A)
    (I : ∀ k : Fin c, Fin (n - colH μ k.val) → Fin n) :
    f (rhsO A n μ c x I) = rhsO B n μ c (fun a i => f (x a i)) I := by
  unfold rhsO
  rw [map_mul, map_prod, ← Top.fockRMap, map_hw']
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [RingHom.map_det, RingHom.mapMatrix_apply, map_catM, map_unitM']

end Maps

theorem lhsO_congr (A : Type) [CommRing A] (n : ℕ) (μ : Fin n → ℕ) (c : ℕ) (x x' : Fin n → ℕ → A)
    (I : ∀ k : Fin c, Fin (n - colH μ k.val) → Fin n) (hx : ∀ a i, i < n → x a i = x' a i) :
    lhsO A n μ c x I = lhsO A n μ c x' I := by
  unfold lhsO
  have : hvO (fun a i => C (x a i)) (yV A n) c (fun k => colH μ k.val) =
      hvO (fun a i => C (x' a i)) (yV A n) c (fun k => colH μ k.val) := by
    unfold hvO
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [catM_congr _ _ _ (fun a i => C (x' a i)) fun a i hi => by rw [hx a i hi]]
  rw [this]

theorem rhsO_congr (A : Type) [CommRing A] (n : ℕ) (μ : Fin n → ℕ) (c : ℕ) (x x' : Fin n → ℕ → A)
    (I : ∀ k : Fin c, Fin (n - colH μ k.val) → Fin n) (hx : ∀ a i, i < n → x a i = x' a i) :
    rhsO A n μ c x I = rhsO A n μ c x' I := by
  unfold rhsO
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [catM_congr _ _ x x' hx]

end BidetPairing

open BidetPairing

theorem pairing_even_holds : PairE := by
  intro K _ _ n ν hν c hc x Q hQ
  rw [hvE_eq K n ν hν c hc x, Top.fockRRowAct,
    Top.fock_pairing_highest_weight K n n le_rfl ν hν _ (dualWeylRowStable K n n ν _ Q hQ), eval_idFrame_rowAct]
  rfl

theorem pairing_odd_holds : PairO := by
  intro K _ _ n μ hμ c hc x I
  show lhsO K n μ c x I = rhsO K n μ c x I
  have hι : Function.Injective (algebraMap (MvPolynomial (Fin n × Fin n) K)
      (FractionRing (MvPolynomial (Fin n × Fin n) K))) :=
    IsFractionRing.injective _ _

  let xg : Fin n → ℕ → MvPolynomial (Fin n × Fin n) K :=
    fun a i => if h : i < n then X (a, ⟨n - 1 - i, by omega⟩) else 0
  have hXg : (Matrix.of fun a t : Fin n => xg a (n - 1 - t.val)) = Matrix.mvPolynomialX (Fin n) (Fin n) K := by
    ext a t
    have := t.isLt
    simp only [Matrix.of_apply, xg, Matrix.mvPolynomialX_apply, dif_pos (show n - 1 - t.val < n by omega)]
    congr 2
    refine Prod.ext rfl (Fin.ext ?_)
    show n - 1 - (n - 1 - t.val) = t.val
    omega
  let XL : Matrix (Fin n) (Fin n) (FractionRing (MvPolynomial (Fin n × Fin n) K)) :=
    Matrix.of fun a t : Fin n => algebraMap _ _ (xg a (n - 1 - t.val))
  have hdet : XL.det ≠ 0 := by
    have hXL : XL = (Matrix.mvPolynomialX (Fin n) (Fin n) K).map
        (algebraMap (MvPolynomial (Fin n × Fin n) K) (FractionRing (MvPolynomial (Fin n × Fin n) K))) := by
      rw [← hXg]
      rfl
    rw [hXL, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    intro h0
    exact Matrix.det_mvPolynomialX_ne_zero (Fin n) K (hι (by rw [h0, map_zero]))
  have hU : IsUnit XL.det := isUnit_iff_ne_zero.2 hdet
  have h1 := pairO_inv (FractionRing (MvPolynomial (Fin n × Fin n) K)) n μ hμ c hc
    (fun a i => algebraMap _ _ (xg a i)) XL⁻¹ (Matrix.nonsing_inv_mul XL hU) (Matrix.mul_nonsing_inv XL hU) I
  rw [← map_lhsO, ← map_rhsO] at h1
  have h2 := hι h1
  have h3 := congrArg (eval fun v : Fin n × Fin n => x v.1 (n - 1 - v.2.val)) h2
  rw [map_lhsO, map_rhsO] at h3
  have hx : ∀ a i, i < n → (fun a i => eval (fun v : Fin n × Fin n => x v.1 (n - 1 - v.2.val)) (xg a i)) a i = x a i := by
    intro a i hi
    simp only [xg, dif_pos hi, eval_X]
    congr 1
    omega
  rwa [lhsO_congr K n μ c _ x I hx, rhsO_congr K n μ c _ x I hx] at h3

end Formalism.L2.PairingIndexBounds.Ent
