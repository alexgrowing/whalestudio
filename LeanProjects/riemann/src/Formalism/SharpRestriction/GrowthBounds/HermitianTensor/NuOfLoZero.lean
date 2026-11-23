import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.CoeffSumMonomialLinear
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.MemInvariantSectionsIffIntegral

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem midI_val (r : ℕ) (j : Fin r) : (midI r j).val = j.val + 1 := by simp [midI]

theorem midI_ne_zero (r : ℕ) (j : Fin r) : midI r j ≠ 0 := by
  unfold midI
  exact Fin.succ_ne_zero _

theorem midI_ne_last (r : ℕ) (j : Fin r) : midI r j ≠ Fin.last (r + 1) := by
  intro h
  have := congrArg Fin.val h
  rw [midI_val, Fin.val_last] at this
  have := j.isLt
  omega

theorem midI_rev (r : ℕ) (j : Fin r) : (midI r j).rev = midI r j.rev := by
  have h2 := j.isLt
  ext
  simp only [Fin.val_rev, midI_val]
  omega

theorem midI_mono (r : ℕ) : Monotone (midI r) := by
  intro a b h
  rw [Fin.le_iff_val_le_val] at h ⊢
  rw [midI_val, midI_val]
  omega

theorem midOf_midI (r : ℕ) (j : Fin r) : midOf (midI r j) = some j := by
  have hv := midI_val r j
  have h2 := j.isLt
  unfold midOf
  split_ifs with h
  · exact Option.some_inj.mpr (Fin.ext (by show (midI r j).val - 1 = j.val; omega))
  · exact absurd ⟨by omega, by omega⟩ h

theorem midOf_last (r : ℕ) : midOf (Fin.last (r + 1)) = none := by
  unfold midOf
  split_ifs with h
  · exact absurd h.2 (by simp)
  · rfl

theorem fin_cases3 (r : ℕ) (t : Fin (r + 1 + 1)) : t = 0 ∨ t = Fin.last (r + 1) ∨ ∃ j, t = midI r j := by
  by_cases h0 : t.val = 0
  · left; exact Fin.ext h0
  · by_cases h1 : t.val = r + 1
    · right; left; exact Fin.ext h1
    · right; right
      have := t.isLt
      refine ⟨⟨t.val - 1, by omega⟩, Fin.ext ?_⟩
      rw [midI_val]
      show t.val = t.val - 1 + 1
      omega

theorem nuOf_last {m : ℕ} (mu : Fin (m + 1) → ℤ) : nuOf mu (Fin.last m) = 0 := by
  simp [nuOf]

theorem wtPQ_mid (mm a b : ℕ) (j : Fin mm) : wtPQ (mm + 1) a b (midI mm j) = 0 := by
  simp only [wtPQ, if_neg (midI_ne_zero _ _), if_neg (midI_ne_last _ _)]

theorem nuOf_wt_zero (mm a b : ℕ) : nuOf (wtPQ (mm + 1) a b) 0 = a + b := by
  have hne : (Fin.last (mm + 1)) ≠ 0 := by simp [Fin.ext_iff]
  simp only [nuOf, wtPQ, if_pos rfl, if_neg hne, if_true]
  omega

theorem nuOf_wt_mid (mm a b : ℕ) (j : Fin mm) : nuOf (wtPQ (mm + 1) a b) (midI mm j) = b := by
  have hne : (Fin.last (mm + 1)) ≠ 0 := by simp [Fin.ext_iff]
  simp only [nuOf]
  rw [wtPQ_mid]
  simp only [wtPQ, if_neg hne, if_true]
  omega

theorem nuOf_wt_add (mm a b a' b' : ℕ) :
    nuOf (wtPQ (mm + 1) (a + a') (b + b')) = nuOf (wtPQ (mm + 1) a b) + nuOf (wtPQ (mm + 1) a' b') := by
  funext t
  have hne : (Fin.last (mm + 1)) ≠ 0 := by simp [Fin.ext_iff]
  simp only [Pi.add_apply, nuOf, wtPQ, if_neg hne, if_pos rfl]
  split_ifs <;> push_cast <;> omega

section Data

variable (mm ccl P Q : ℕ) (lam : Fin (mm + 1 + 1) → ℤ) (h0 : lam 0 = (P : ℤ) + ccl)
  (hl : lam (Fin.last (mm + 1)) = -((Q : ℤ) + ccl))
  (hmid : ∀ i : Fin (mm + 1 + 1), 0 < i.val → i.val < mm + 1 → |lam i| ≤ ccl)

include hmid in
theorem lam_mid_bd (j : Fin mm) : -(ccl : ℤ) ≤ lam (midI mm j) ∧ lam (midI mm j) ≤ ccl := by
  have hv := midI_val mm j
  have h2 := j.isLt
  exact abs_le.mp (hmid _ (by omega) (by omega))

include h0 hl in
theorem lo_zero : (lam - wtPQ (mm + 1) P Q) 0 = ccl := by
  simp only [Pi.sub_apply, wtPQ, ↓reduceIte, h0]
  ring

include h0 hl in
theorem lo_last : (lam - wtPQ (mm + 1) P Q) (Fin.last (mm + 1)) = -(ccl : ℤ) := by
  have hne : (Fin.last (mm + 1)) ≠ 0 := by simp [Fin.ext_iff]
  simp only [Pi.sub_apply, wtPQ, if_neg hne, ↓reduceIte, hl]
  ring

include h0 hl in
theorem lo_mid (j : Fin mm) : (lam - wtPQ (mm + 1) P Q) (midI mm j) = lam (midI mm j) := by
  simp only [Pi.sub_apply, wtPQ_mid, sub_zero]

include h0 hl in
theorem nuOf_lam_zero : nuOf lam 0 = P + Q + 2 * ccl := by
  simp only [nuOf, h0, hl]
  omega

include hl hmid in
theorem nuOf_lam_mid (j : Fin mm) : ((nuOf lam (midI mm j) : ℕ) : ℤ) = lam (midI mm j) + Q + ccl := by
  have hb := lam_mid_bd mm ccl lam hmid j
  simp only [nuOf, hl]
  omega

include h0 hl in
theorem nuOf_lo_zero : nuOf (lam - wtPQ (mm + 1) P Q) 0 = 2 * ccl := by
  unfold nuOf
  rw [lo_zero mm ccl P Q lam h0 hl, lo_last mm ccl P Q lam h0 hl]
  omega

include h0 hl hmid in
theorem nuOf_lo_mid (j : Fin mm) :
    ((nuOf (lam - wtPQ (mm + 1) P Q) (midI mm j) : ℕ) : ℤ) = lam (midI mm j) + ccl := by
  have := lam_mid_bd mm ccl lam hmid j
  unfold nuOf
  rw [lo_mid mm ccl P Q lam h0 hl, lo_last mm ccl P Q lam h0 hl]
  omega

include h0 hl in
theorem nuOf_lo'_zero : nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) 0 = 2 * ccl := by
  simp only [nuOf, dualWt, Fin.rev_zero, Fin.rev_last]
  rw [lo_zero mm ccl P Q lam h0 hl, lo_last mm ccl P Q lam h0 hl]
  omega

include h0 hl hmid in
theorem nuOf_lo'_mid (j : Fin mm) :
    ((nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) (midI mm j) : ℕ) : ℤ) = ccl - lam (midI mm j.rev) := by
  have hb := lam_mid_bd mm ccl lam hmid j.rev
  simp only [nuOf, dualWt, Fin.rev_last]
  rw [midI_rev, lo_mid mm ccl P Q lam h0 hl j.rev, lo_zero mm ccl P Q lam h0 hl]
  omega

include h0 hl in
theorem shapeC_lo : shapeC (2 * ccl) (fun j => nuOf (lam - wtPQ (mm + 1) P Q) (midI mm j)) =
    nuOf (lam - wtPQ (mm + 1) P Q) := by
  funext t
  rcases fin_cases3 mm t with rfl | rfl | ⟨j, rfl⟩
  · simp only [shapeC, ↓reduceIte]
    rw [nuOf_lo_zero mm ccl P Q lam h0 hl]
  · have hne : (Fin.last (mm + 1)) ≠ 0 := by simp [Fin.ext_iff]
    simp only [shapeC, if_neg hne, midOf_last]
    rw [nuOf_last]
  · simp only [shapeC, if_neg (midI_ne_zero _ _), midOf_midI]

include h0 hl in
theorem shapeC_lo' : shapeC (2 * ccl) (fun j => nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) (midI mm j)) =
    nuOf (dualWt (lam - wtPQ (mm + 1) P Q)) := by
  funext t
  rcases fin_cases3 mm t with rfl | rfl | ⟨j, rfl⟩
  · simp only [shapeC, ↓reduceIte]
    rw [nuOf_lo'_zero mm ccl P Q lam h0 hl]
  · have hne : (Fin.last (mm + 1)) ≠ 0 := by simp [Fin.ext_iff]
    simp only [shapeC, if_neg hne, midOf_last]
    rw [nuOf_last]
  · simp only [shapeC, if_neg (midI_ne_zero _ _), midOf_midI]

end Data

theorem qsDualWt_anti {m : ℕ} (mu : Fin (m + 1) → ℤ) (h : Antitone mu) : Antitone (dualWt mu) := by
  intro i j hij
  exact neg_le_neg (h (Fin.rev_le_rev.mpr hij))

theorem rowDeg_add {k n : ℕ} (u v : Fin k × Fin n →₀ ℕ) (a : Fin k) : rowDeg (u + v) a = rowDeg u a + rowDeg v a := by
  simp only [rowDeg, Finsupp.add_apply, Finset.sum_add_distrib]

theorem rowA_mul {K : Type} [CommRing K] {k n : ℕ} (a : Fin k) (f g : MvPolynomial (Fin k × Fin n) K) (d d' : ℕ)
    (hf : RowA a f d) (hg : RowA a g d') : RowA a (f * g) (d + d') := by
  classical
  intro u hu
  rw [coeff_mul] at hu
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hu
  have h1 : coeff x.1 f ≠ 0 := fun h => hne (by rw [h, zero_mul])
  have h2 : coeff x.2 g ≠ 0 := fun h => hne (by rw [h, mul_zero])
  rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hx, rowDeg_add, hf _ h1, hg _ h2]

theorem rowA_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {k n : ℕ} (a : Fin k)
    (f : MvPolynomial (Fin k × Fin n) A) (d : ℕ) (hf : RowA a f d) : RowA a (map φ f) d := by
  intro u hu
  rw [coeff_map] at hu
  exact hf u (fun h => hu (by rw [h, map_zero]))

private theorem rowA_zero_lemma {K : Type} [CommRing K] {k n : ℕ} (a : Fin k) (d : ℕ) :
    RowA a (0 : MvPolynomial (Fin k × Fin n) K) d := by
  intro u hu
  simp at hu

private theorem rowA_C_lemma_2 {K : Type} [CommRing K] {k n : ℕ} (a : Fin k) (c : K) :
    RowA a (C c : MvPolynomial (Fin k × Fin n) K) 0 := by
  intro u hu
  rw [coeff_C] at hu
  split_ifs at hu with h
  · subst h
    simp [rowDeg]
  · exact absurd rfl hu

private theorem rowA_X_lemma_3 {K : Type} [CommRing K] {k n : ℕ} (a : Fin k) (v : Fin k × Fin n) :
    RowA a (X v : MvPolynomial (Fin k × Fin n) K) (if v.1 = a then 1 else 0) := by
  intro u hu
  rw [coeff_X'] at hu
  split_ifs at hu with h
  · subst h
    obtain ⟨b, t⟩ := v
    by_cases hb : b = a
    · subst hb
      simp [rowDeg, Finsupp.single_apply, Prod.mk.injEq]
    · simp [rowDeg, Finsupp.single_apply, Prod.mk.injEq, hb]
  · exact absurd rfl hu

private theorem rowA_add_lemma_4 {K : Type} [CommRing K] {k n : ℕ} (a : Fin k)
    (f g : MvPolynomial (Fin k × Fin n) K) (d : ℕ) (hf : RowA a f d) (hg : RowA a g d) :
    RowA a (f + g) d := by
  intro u hu
  rw [coeff_add] at hu
  by_cases h : coeff u f = 0
  · rw [h, zero_add] at hu
    exact hg u hu
  · exact hf u h

private theorem rowA_sum_lemma_5 {K : Type} [CommRing K] {k n : ℕ} {ι : Type} (a : Fin k) (s : Finset ι)
    (f : ι → MvPolynomial (Fin k × Fin n) K) (d : ℕ) (hf : ∀ i ∈ s, RowA a (f i) d) :
    RowA a (∑ i ∈ s, f i) d :=
  Finset.sum_induction f (fun g => RowA a g d) (fun g h hg hh => rowA_add_lemma_4 a g h d hg hh)
    (rowA_zero_lemma a d) hf

private theorem rowA_prod_lemma_6 {K : Type} [CommRing K] {k n : ℕ} {ι : Type} (a : Fin k) (s : Finset ι)
    (f : ι → MvPolynomial (Fin k × Fin n) K) (d : ι → ℕ) (hf : ∀ i ∈ s, RowA a (f i) (d i)) :
    RowA a (∏ i ∈ s, f i) (∑ i ∈ s, d i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using rowA_C_lemma_2 (K := K) (n := n) a 1
  | cons i s hi ih =>
    rw [Finset.prod_cons, Finset.sum_cons]
    exact rowA_mul a _ _ _ _ (hf i (Finset.mem_cons_self i s)) (ih (fun j hj => hf j (Finset.mem_cons_of_mem hj)))

private theorem rowA_pow_lemma_7 {K : Type} [CommRing K] {k n : ℕ} (a : Fin k)
    (f : MvPolynomial (Fin k × Fin n) K) (d m : ℕ) (hf : RowA a f d) : RowA a (f ^ m) (m * d) := by
  induction m with
  | zero => simpa using rowA_C_lemma_2 (K := K) (n := n) a 1
  | succ m ih =>
    rw [pow_succ, Nat.succ_mul]
    exact rowA_mul a _ _ _ _ ih hf

private theorem rowA_minor_lemma_8 (K : Type) [CommRing K] {k : ℕ} (a : Fin k) (s : ℕ) (hr hn : s ≤ k) :
    RowA a (lpMinor K s hr hn) (∑ p : Fin s, if Fin.castLE hr p = a then 1 else 0) := by
  unfold lpMinor
  rw [Matrix.det_apply']
  apply rowA_sum_lemma_5
  intro σ _
  have hσ : (∑ p : Fin s, if Fin.castLE hr p = a then 1 else 0) =
      0 + ∑ i : Fin s, if Fin.castLE hr (σ i) = a then 1 else 0 := by
    rw [zero_add]
    exact (Equiv.sum_comp σ (fun p => if Fin.castLE hr p = a then 1 else 0)).symm
  rw [hσ]
  apply rowA_mul
  · rw [← map_intCast (C : K →+* MvPolynomial (Fin k × Fin k) K)]
    exact rowA_C_lemma_2 a _
  · apply rowA_prod_lemma_6
    intro i _
    exact rowA_X_lemma_3 a _

private theorem cnt_lemma_9 {k : ℕ} (a : Fin k) (s : ℕ) (hr : s ≤ k) :
    (∑ p : Fin s, if Fin.castLE hr p = a then 1 else 0) = if a.val < s then 1 else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨a.val, h⟩]
    · simp [Fin.ext_iff]
    · intro b _ hb
      rw [if_neg]
      intro hc
      apply hb
      ext
      have := congrArg Fin.val hc
      simpa using this
    · simp
  · apply Finset.sum_eq_zero
    intro p _
    have hp := p.isLt
    rw [if_neg]
    intro hc
    have := congrArg Fin.val hc
    simp at this
    omega

private theorem tele_lemma_10 {k : ℕ} (ν : Fin k → ℕ) (hν : Antitone ν) (a : Fin k) :
    ν a = ∑ s : Fin k, (ν s - nuNext ν s) * (if a.val < s.val + 1 then 1 else 0) := by
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℕ, g = fun n => if h : n < k then ν ⟨n, h⟩ else 0 := ⟨_, rfl⟩
  have hgν : ∀ s : Fin k, ν s = g s.val := fun s => by simp [hg, s.isLt]
  have hgn : ∀ s : Fin k, nuNext ν s = g (s.val + 1) := fun s => by simp only [nuNext, hg]
  have hanti : ∀ m n, m ≤ n → g n ≤ g m := by
    intro m n hmn
    simp only [hg]
    split_ifs <;> first | exact hν (Fin.mk_le_mk.mpr hmn) | omega | exact Nat.zero_le _
  have key : ∀ n, n ≤ k → (∑ i ∈ Finset.range n, (g i - g (i + 1)) * (if a.val < i + 1 then 1 else 0)) =
      if a.val < n then g a.val - g n else 0 := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [Finset.sum_range_succ, ih (by omega)]
      have h1 := hanti n (n + 1) (by omega)
      have h2 := hanti a.val n
      by_cases ha : a.val < n
      · have h3 := h2 (le_of_lt ha)
        have ha' : a.val < n + 1 := by omega
        simp only [if_pos ha, if_pos ha']
        omega
      · by_cases hb : a.val = n
        · have ha' : a.val < n + 1 := by omega
          simp only [if_neg ha, if_pos ha']
          rw [hb]
          omega
        · have ha' : ¬ a.val < n + 1 := by omega
          simp only [if_neg ha, if_neg ha']
          omega
  have hk := key k le_rfl
  rw [if_pos a.isLt] at hk
  have hgk : g k = 0 := by simp [hg]
  rw [hgk, Nat.sub_zero] at hk
  rw [hgν a, ← hk, ← Fin.sum_univ_eq_sum_range (fun i => (g i - g (i + 1)) * (if a.val < i + 1 then 1 else 0)) k]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  show (g s.val - g (s.val + 1)) * _ = _
  rw [hgν s, hgn s]

theorem rowA_hw (K : Type) [CommRing K] (k : ℕ) (ν : Fin k → ℕ) (hν : Antitone ν) (a : Fin k) :
    RowA a (hw K (le_refl k) ν) (ν a) := by
  rw [tele_lemma_10 ν hν a]
  unfold hw
  apply rowA_prod_lemma_6
  intro s _
  have hm := rowA_minor_lemma_8 K a (s.val + 1) s.isLt s.isLt
  rw [cnt_lemma_9] at hm
  exact rowA_pow_lemma_7 a _ _ _ hm

theorem rowA_lam (hC : LamCoeffP) (hR : SubRowP) (K : Type) [Field K] (r : ℕ)
    (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K) (a : Fin (r + 1 + 1))
    (v t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K) (d d' : ℕ) (hv : RowA a v d) (ht : RowA a t d') :
    RowA a (lamOf K r L (blockEmb K true v * blockEmb K false t)) (d + d') := by
  classical
  intro u hu
  rw [hC] at hu
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hu
  have h1 : coeff x.1 (subY K r v) ≠ 0 := fun h => hne (by rw [h, map_zero, zero_mul, map_zero])
  have h2 : coeff x.2 (subY K r t) ≠ 0 := fun h => hne (by rw [h, map_zero, mul_zero, map_zero])
  rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hx, rowDeg_add, hR K r a d v hv _ h1, hR K r a d' t ht _ h2]

theorem evalId_map {A B : Type} [CommRing A] [CommRing B] (ψ : A →+* B) (k n : ℕ) (h : MvPolynomial (Fin k × Fin n) A) :
    eval (idPoint B k n) (map ψ h) = ψ (eval (idPoint A k n) h) := by
  induction h using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, map_X, eval_X, hp]
    unfold idPoint
    split_ifs <;> simp

theorem detY_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (r : ℕ) : map φ (detY A r) = detY B r := by
  unfold detY
  have h := RingHom.map_det (map φ) (Matrix.of fun i j : Fin r => (X (i, j) : MvPolynomial (Fin r × Fin r) A))
  refine h.trans ?_
  congr 1
  ext i j
  simp

theorem resY_mul (A : Type) [CommRing A] (r : ℕ) (s t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A) :
    resY A r (s * t) = resY A r s * resY A r t := by
  unfold resY
  rw [map_mul, map_mul]

theorem resY_map (hM : SubMapP) {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (r : ℕ)
    (s : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) A) : resY B r (map φ s) = map φ (resY A r s) := by
  simp only [resY]
  rw [hM A B φ r s]
  exact evalId_map (map φ) (r + 1 + 1) (r + 1 + 1) _

end Formalism.MainNotions.flipOneThree.Pf

end
