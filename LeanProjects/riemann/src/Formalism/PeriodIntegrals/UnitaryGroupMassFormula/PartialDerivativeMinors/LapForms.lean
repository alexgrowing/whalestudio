import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.PMinorAff
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MsMul

noncomputable section

open scoped BigOperators

namespace PI.EntAtD.W

open PI.EntAtD MvPolynomial

section LapFormsSec

variable {H : Type} {N0 N1 : ℕ}

lemma der_sum_apply {ι : Type} (s : Finset ι)
    (D : ι → Derivation ℤ (PolyXZ H N0 N1) (PolyXZ H N0 N1)) (x : PolyXZ H N0 N1) :
    (∑ i ∈ s, D i) x = ∑ i ∈ s, D i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Derivation.add_apply, ih]

lemma pderiv_comm' (i j : XZ (Bool × H) N0 N1) (P : PolyXZ H N0 N1) :
    pderiv i (pderiv j P) = pderiv j (pderiv i P) := by
  have h : ⁅(pderiv (R := ℤ) i : Derivation ℤ (PolyXZ H N0 N1) (PolyXZ H N0 N1)), pderiv (R := ℤ) j⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    rw [Derivation.commutator_apply, Derivation.zero_apply]
    by_cases hj : k = j
    · subst hj
      by_cases hi : k = i
      · subst hi; simp
      · simp [pderiv_X_of_ne hi]
    · by_cases hi : k = i
      · subst hi; simp [pderiv_X_of_ne hj]
      · simp [pderiv_X_of_ne hi, pderiv_X_of_ne hj]
  have h2 := congrArg (fun D : Derivation ℤ (PolyXZ H N0 N1) (PolyXZ H N0 N1) => D P) h
  simp only [Derivation.commutator_apply, Derivation.zero_apply] at h2
  exact sub_eq_zero.mp h2

lemma pd_inr_X_inl (v : (Bool × H) × Fin N0 × Fin N1) (u : (Bool × H) × ℕ × Fin N0) :
    pderiv (Sum.inr v : XZ (Bool × H) N0 N1) (X (Sum.inl u) : PolyXZ H N0 N1) = 0 :=
  pderiv_X_of_ne Sum.inl_ne_inr

def lfo (t : H) (c : ℕ × Fin N1) : PolyXZ H N0 N1 :=
  ∑ a : Fin N0, X (Sum.inl ((false, t), c.1, a)) * X (Sum.inr ((false, t), a, c.2))

def tmL (t : H) (L : List (ℕ × Fin N1)) (h : PolyXZ H N0 N1) : PolyXZ H N0 N1 :=
  (L.map (lfo (N0 := N0) t)).prod * h

def nzc (L : List (ℕ × Fin N1)) : ℕ := (L.map fun c => if c.1 = 0 then 0 else 1).sum

def z0c (L : List (ℕ × Fin N1)) : ℕ := (L.map fun c => if c.1 = 0 then 1 else 0).sum

lemma nzc_cons (c : ℕ × Fin N1) (L : List (ℕ × Fin N1)) :
    nzc (c :: L) = (if c.1 = 0 then 0 else 1) + nzc L := by
  simp [nzc]

lemma zeroCount_cons (c : ℕ × Fin N1) (L : List (ℕ × Fin N1)) :
    z0c (c :: L) = (if c.1 = 0 then 1 else 0) + z0c L := by
  simp [z0c]

lemma nonzeroCount_add_zeroCount (L : List (ℕ × Fin N1)) : nzc L + z0c L = L.length := by
  induction L with
  | nil => simp [nzc, z0c]
  | cons c L ih =>
    rw [nzc_cons, zeroCount_cons, List.length_cons]
    split_ifs <;> omega

lemma dRow_apply (t : H) (r : ℕ) (b : Fin N1) (P : PolyXZ H N0 N1) :
    dRow (N0 := N0) t r b P =
      ∑ a : Fin N0, X (Sum.inl ((false, t), r, a)) * pderiv (Sum.inr ((true, t), a, b)) P := by
  unfold dRow
  rw [der_sum_apply]
  simp only [Derivation.smul_apply, smul_eq_mul]

lemma lap_apply (t : H) (P : PolyXZ H N0 N1) :
    lapT N0 N1 t P = ∑ a : Fin N0, ∑ b : Fin N1,
      pderiv (Sum.inr ((false, t), a, b)) (pderiv (Sum.inr ((true, t), a, b)) P) := by
  simp only [lapT, LinearMap.sum_apply, Module.End.mul_apply]
  rfl

lemma pw_lfo (t : H) (c : ℕ × Fin N1) (a : Fin N0) (b : Fin N1) :
    pderiv (Sum.inr ((true, t), a, b)) (lfo (N0 := N0) t c) = 0 := by
  unfold lfo
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro a' _
  rw [Derivation.leibniz, pd_inr_X_inl, pderiv_X_of_ne (by simp), smul_zero, smul_zero, add_zero]

lemma pz_lfo (t : H) (c : ℕ × Fin N1) (a : Fin N0) (b : Fin N1) :
    pderiv (Sum.inr ((false, t), a, b)) (lfo (N0 := N0) t c) =
      if b = c.2 then X (Sum.inl ((false, t), c.1, a)) else 0 := by
  have key : ∀ a' : Fin N0, pderiv (Sum.inr ((false, t), a, b))
      (X (Sum.inl ((false, t), c.1, a')) * X (Sum.inr ((false, t), a', c.2)) : PolyXZ H N0 N1) =
      if a' = a ∧ c.2 = b then X (Sum.inl ((false, t), c.1, a')) else 0 := by
    intro a'
    rw [Derivation.leibniz, pd_inr_X_inl, smul_zero, add_zero, smul_eq_mul]
    split_ifs with h
    · obtain ⟨rfl, hb⟩ := h
      rw [hb, pderiv_X_self, mul_one]
    · rw [pderiv_X_of_ne, mul_zero]
      intro e
      simp only [Sum.inr.injEq, Prod.mk.injEq] at e
      exact h ⟨e.2.1, e.2.2⟩
  unfold lfo
  rw [map_sum, Finset.sum_congr rfl (fun a' _ => key a')]
  by_cases hb : b = c.2
  · subst hb
    simp
  · have hb' : c.2 ≠ b := fun h => hb h.symm
    simp [hb, hb']

lemma pw_prod (t : H) (L : List (ℕ × Fin N1)) (a : Fin N0) (b : Fin N1) :
    pderiv (Sum.inr ((true, t), a, b)) ((L.map (lfo (N0 := N0) t)).prod) = 0 := by
  induction L with
  | nil => simp
  | cons c L ih =>
    rw [List.map_cons, List.prod_cons, Derivation.leibniz, ih, pw_lfo, smul_zero, smul_zero, add_zero]

lemma lap_mul (t : H) (f h : PolyXZ H N0 N1)
    (hf : ∀ a b, pderiv (Sum.inr ((true, t), a, b)) f = 0)
    (hh : ∀ a b, pderiv (Sum.inr ((false, t), a, b)) h = 0) :
    lapT N0 N1 t (f * h) = ∑ a : Fin N0, ∑ b : Fin N1,
      pderiv (Sum.inr ((false, t), a, b)) f * pderiv (Sum.inr ((true, t), a, b)) h := by
  rw [lap_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have e1 : pderiv (Sum.inr ((true, t), a, b)) (f * h) = f * pderiv (Sum.inr ((true, t), a, b)) h := by
    rw [Derivation.leibniz, hf, smul_zero, add_zero, smul_eq_mul]
  rw [e1, Derivation.leibniz, pderiv_comm' (Sum.inr ((false, t), a, b)), hh, map_zero, smul_zero, zero_add,
    smul_eq_mul, mul_comm]

def Gf (t : H) (f h : PolyXZ H N0 N1) : PolyXZ H N0 N1 :=
  ∑ a : Fin N0, ∑ b : Fin N1,
    pderiv (Sum.inr ((false, t), a, b)) f * pderiv (Sum.inr ((true, t), a, b)) h

lemma Gf_cons (t : H) (c : ℕ × Fin N1) (P h : PolyXZ H N0 N1) :
    Gf t (lfo t c * P) h = P * dRow (N0 := N0) t c.1 c.2 h + lfo t c * Gf t P h := by
  have h1 : ∀ a : Fin N0, ∑ b : Fin N1, P * (if b = c.2 then X (Sum.inl ((false, t), c.1, a)) else 0) *
      pderiv (Sum.inr ((true, t), a, b)) h =
      P * (X (Sum.inl ((false, t), c.1, a)) * pderiv (Sum.inr ((true, t), a, c.2)) h) := by
    intro a
    rw [Finset.sum_eq_single c.2]
    · simp [mul_assoc]
    · intro b _ hb
      simp [hb]
    · simp
  simp only [Gf, Derivation.leibniz, smul_eq_mul, pz_lfo, add_mul, Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun a _ => h1 a), dRow_apply]
  simp only [Finset.mul_sum, mul_assoc]
  rw [add_comm]

lemma zf_dRow (t : H) (r : ℕ) (b : Fin N1) (h : PolyXZ H N0 N1)
    (hh : ∀ a b, pderiv (Sum.inr ((false, t), a, b)) h = 0) :
    ∀ a b', pderiv (Sum.inr ((false, t), a, b')) (dRow (N0 := N0) t r b h) = 0 := by
  intro a b'
  rw [dRow_apply, map_sum]
  apply Finset.sum_eq_zero
  intro a' _
  rw [Derivation.leibniz, pderiv_comm' (Sum.inr ((false, t), a, b')), hh, map_zero, smul_zero, zero_add,
    pd_inr_X_inl, smul_zero]

lemma dRow_comm (t : H) (r : ℕ) (b : Fin N1) (r' : ℕ) (b' : Fin N1) (P : PolyXZ H N0 N1) :
    dRow (N0 := N0) t r b (dRow t r' b' P) = dRow t r' b' (dRow t r b P) := by
  simp only [dRow_apply, map_sum, Derivation.leibniz, pd_inr_X_inl, smul_eq_mul, mul_zero,
    Finset.sum_const_zero, add_zero, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro a' _
  rw [pderiv_comm' (Sum.inr ((true, t), a, b))]
  ring

lemma sdeg_comm {A : Type} [CommRing A] {ι : Type} (d : ι → Derivation ℤ A A) (E : A → A)
    (hE : ∀ j x, d j (E x) = E (d j x)) (hE0 : E 0 = 0) :
    ∀ (k : ℕ) (h : A), SDegD d k h → SDegD d k (E h) := by
  intro k
  induction k with
  | zero =>
    intro h hk
    simp only [SDegD] at hk ⊢
    intro j
    rw [hE, hk j, hE0]
  | succ k ih =>
    intro h hk
    simp only [SDegD] at hk ⊢
    intro j
    rw [hE]
    exact ih _ (hk j)

def RelL (L' : List (ℕ × Fin N1)) (k' : ℕ) (L : List (ℕ × Fin N1)) (k : ℕ) : Prop :=
  (nzc L' + 1 ≤ nzc L ∧ z0c L' ≤ z0c L ∧ k' ≤ k) ∨
    (nzc L' ≤ nzc L ∧ z0c L' + 1 ≤ z0c L ∧ k' + 1 ≤ k)

lemma relL_lt {L' : List (ℕ × Fin N1)} {k' : ℕ} {L : List (ℕ × Fin N1)} {k : ℕ} (h : RelL L' k' L k) :
    nzc L' + min (z0c L') k' < nzc L + min (z0c L) k := by
  unfold RelL at h
  omega

def GS (t : H) (L : List (ℕ × Fin N1)) (k : ℕ) : Set (PolyXZ H N0 N1) :=
  {Q | ∃ (L' : List (ℕ × Fin N1)) (h' : PolyXZ H N0 N1) (k' : ℕ), Q = tmL t L' h' ∧
    (∀ a b, pderiv (Sum.inr ((false, t), a, b)) h' = 0) ∧
    SDegD (fun b : Fin N1 => dRow (N0 := N0) t 0 b) k' h' ∧ RelL L' k' L k}

lemma gf_mem (t : H) (L : List (ℕ × Fin N1)) :
    ∀ (h : PolyXZ H N0 N1) (k : ℕ), (∀ a b, pderiv (Sum.inr ((false, t), a, b)) h = 0) →
      SDegD (fun b : Fin N1 => dRow (N0 := N0) t 0 b) k h →
      Gf t (L.map (lfo (N0 := N0) t)).prod h ∈ Submodule.span ℤ (GS t L k) := by
  induction L with
  | nil =>
    intro h k _ _
    simp [Gf]
  | cons c L ih =>
    intro h k hh hk
    rw [List.map_cons, List.prod_cons, Gf_cons]
    apply add_mem
    · by_cases hc : c.1 = 0
      · cases k with
        | zero =>
          have e : dRow (N0 := N0) t c.1 c.2 h = 0 := by
            rw [hc]
            simp only [SDegD] at hk
            exact hk c.2
          rw [e, mul_zero]
          exact zero_mem _
        | succ k =>
          apply Submodule.subset_span
          refine ⟨L, dRow (N0 := N0) t c.1 c.2 h, k, rfl, zf_dRow t _ _ h hh, ?_, ?_⟩
          · rw [hc]
            simp only [SDegD] at hk
            exact hk c.2
          · unfold RelL
            rw [nzc_cons, zeroCount_cons, if_pos hc, if_pos hc]
            omega
      · apply Submodule.subset_span
        refine ⟨L, dRow (N0 := N0) t c.1 c.2 h, k, rfl, zf_dRow t _ _ h hh,
          sdeg_comm _ (dRow (N0 := N0) t c.1 c.2) (fun j x => dRow_comm t 0 j c.1 c.2 x) (map_zero _) k h hk, ?_⟩
        unfold RelL
        rw [nzc_cons, zeroCount_cons, if_neg hc, if_neg hc]
        omega
    · have key : ∀ x ∈ Submodule.span ℤ (GS (N0 := N0) t L k),
          lfo t c * x ∈ Submodule.span ℤ (GS (N0 := N0) t (c :: L) k) := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨L', h', k', rfl, h1, h2, h3⟩ := hx
          apply Submodule.subset_span
          refine ⟨c :: L', h', k', ?_, h1, h2, ?_⟩
          · simp only [tmL, List.map_cons, List.prod_cons, mul_assoc]
          · unfold RelL at h3 ⊢
            rw [nzc_cons, nzc_cons, zeroCount_cons, zeroCount_cons]
            split_ifs <;> omega
        | zero => rw [mul_zero]; exact zero_mem _
        | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
        | smul a x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ a hx
      exact key _ (ih h k hh hk)

lemma lap_tm_zero (t : H) (n : ℕ) :
    ∀ (L : List (ℕ × Fin N1)) (h : PolyXZ H N0 N1) (k : ℕ),
      (∀ a b, pderiv (Sum.inr ((false, t), a, b)) h = 0) →
      SDegD (fun b : Fin N1 => dRow (N0 := N0) t 0 b) k h →
      nzc L + min (z0c L) k < n → (lapT N0 N1 t ^ n) (tmL t L h) = 0 := by
  induction n with
  | zero => intro L h k _ _ hb; omega
  | succ n ih =>
    intro L h k hh hk hb
    rw [pow_succ, Module.End.mul_apply]
    have e : lapT N0 N1 t (tmL t L h) = Gf t (L.map (lfo (N0 := N0) t)).prod h :=
      lap_mul t _ h (pw_prod t L) hh
    rw [e]
    have key : ∀ x ∈ Submodule.span ℤ (GS (N0 := N0) t L k), (lapT N0 N1 t ^ n) x = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨L', h', k', rfl, h1, h2, h3⟩ := hx
        exact ih L' h' k' h1 h2 (by have := relL_lt h3; omega)
      | zero => exact map_zero _
      | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
      | smul a x _ hx => rw [map_smul, hx, smul_zero]
    exact key _ (gf_mem t L h k hh hk)

def MS (t : H) (a b : ℕ) : Submodule ℤ (PolyXZ H N0 N1) :=
  Submodule.span ℤ {Q | ∃ L : List (ℕ × Fin N1), Q = tmL t L 1 ∧ nzc L = a ∧ z0c L = b}

lemma ms_mul (t : H) {a b a' b' : ℕ} {P Q : PolyXZ H N0 N1} (hP : P ∈ MS t a b) (hQ : Q ∈ MS t a' b') :
    P * Q ∈ MS t (a + a') (b + b') := by
  first | exact UpperTheory.Reformulated.B.Qj21.ms_mul .. | (apply UpperTheory.Reformulated.B.Qj21.ms_mul <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qj21.ms_mul <;> assumption) | (apply @UpperTheory.Reformulated.B.Qj21.ms_mul <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qj21.ms_mul <;> assumption) | (apply @UpperTheory.Reformulated.B.Qj21.ms_mul <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qj21.ms_mul H N0 N1 t a b a' b' P Q hP hQ | exact @UpperTheory.Reformulated.B.Qj21.ms_mul H N0 N1 t a b a' b' P Q hP | exact @UpperTheory.Reformulated.B.Qj21.ms_mul H N0 N1 t a b a' b' P Q | exact @UpperTheory.Reformulated.B.Qj21.ms_mul H N0 N1 t a b a' b' P | exact @UpperTheory.Reformulated.B.Qj21.ms_mul H N0 N1 t a b a' b' | exact @UpperTheory.Reformulated.B.Qj21.ms_mul H N0 N1 t a b a' | exact @UpperTheory.Reformulated.B.Qj21.ms_mul H N0 N1 t a b | exact @UpperTheory.Reformulated.B.Qj21.ms_mul H N0 N1 t a | exact @UpperTheory.Reformulated.B.Qj21.ms_mul H N0 N1 t | exact @UpperTheory.Reformulated.B.Qj21.ms_mul H N0 N1 | exact @UpperTheory.Reformulated.B.Qj21.ms_mul H N0 | exact @UpperTheory.Reformulated.B.Qj21.ms_mul H

lemma ms_prod (t : H) {ι : Type} (s : Finset ι) (f : ι → PolyXZ H N0 N1) (a b : ι → ℕ)
    (h : ∀ i ∈ s, f i ∈ MS t (a i) (b i)) :
    ∏ i ∈ s, f i ∈ MS t (∑ i ∈ s, a i) (∑ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    apply Submodule.subset_span
    exact ⟨[], by simp [tmL], by simp [nzc], by simp [z0c]⟩
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.sum_insert hi]
    exact ms_mul t (h i (Finset.mem_insert_self i s)) (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

lemma zeroCount_ofFn {p : ℕ} (g : Fin p → ℕ × Fin N1) :
    z0c (List.ofFn g) = ∑ i : Fin p, (if (g i).1 = 0 then 1 else 0) := by
  simp [z0c, List.map_ofFn, List.sum_ofFn]

lemma minor_mem (t : H) (p : ℕ) (hp : 0 < p) (I : Fin p ↪o Fin N1) :
    minorXZ (Lt := Bool × H) N0 N1 (false, t) p I ∈ MS t (p - 1) 1 := by
  unfold minorXZ
  rw [Matrix.det_apply]
  apply Submodule.sum_mem
  intro σ _
  rw [Units.smul_def]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  have hz : z0c (List.ofFn fun i : Fin p => (((σ i : Fin p) : ℕ), I i)) = 1 := by
    rw [zeroCount_ofFn]
    rw [Equiv.sum_comp σ (fun j : Fin p => if (j : ℕ) = 0 then 1 else 0)]
    rw [Finset.sum_eq_single ⟨0, hp⟩]
    · simp
    · intro j _ hj
      have : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
      simp [this]
    · simp
  refine ⟨List.ofFn fun i : Fin p => (((σ i : Fin p) : ℕ), I i), ?_, ?_, hz⟩
  · simp only [tmL, List.map_ofFn, List.prod_ofFn, mul_one, Matrix.of_apply]
    rfl
  · have := nonzeroCount_add_zeroCount (List.ofFn fun i : Fin p => (((σ i : Fin p) : ℕ), I i))
    rw [List.length_ofFn, hz] at this
    omega

lemma colLen_pos (α : YoungDiagram) (c : Fin (α.rowLen 0)) : 0 < α.colLen c := by
  rw [← YoungDiagram.mem_iff_lt_colLen]
  exact YoungDiagram.mem_iff_lt_rowLen.mpr c.2

lemma sum_colLen_le (α : YoungDiagram) : ∑ c : Fin (α.rowLen 0), α.colLen c ≤ α.cells.card := by
  have e : ∑ c : Fin (α.rowLen 0), α.colLen c =
      (Finset.univ.sigma fun c : Fin (α.rowLen 0) => Finset.range (α.colLen c)).card := by
    rw [Finset.card_sigma]
    simp
  rw [e]
  apply Finset.card_le_card_of_injOn (fun x => (x.2, (x.1 : ℕ)))
  · intro x hx
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_univ, Set.mem_univ, Finset.coe_range,
      Set.mem_Iio, true_and, Finset.mem_coe] at hx ⊢
    rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_colLen]
    exact hx
  · rintro ⟨c, i⟩ _ ⟨c', i'⟩ _ hxy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨rfl, h2⟩ := hxy
    have : c = c' := Fin.ext h2
    subst this
    rfl

theorem pLapForms : PLapForms := by
  intro H _ _ N0 N1 α I t g d n hg hd hn
  have hF := ms_prod (N0 := N0) t (Finset.univ : Finset (Fin (α.rowLen 0)))
    (fun c => minorXZ (Lt := Bool × H) N0 N1 (false, t) (α.colLen c) (I c))
    (fun c => α.colLen c - 1) (fun _ => 1)
    (fun c _ => minor_mem t _ (colLen_pos α c) (I c))
  have hsum : ∑ c : Fin (α.rowLen 0), (α.colLen c - 1) + α.rowLen 0 ≤ α.cells.card := by
    calc ∑ c : Fin (α.rowLen 0), (α.colLen c - 1) + α.rowLen 0
        = ∑ c : Fin (α.rowLen 0), (α.colLen c - 1) + ∑ _c : Fin (α.rowLen 0), 1 := by simp
      _ = ∑ c : Fin (α.rowLen 0), (α.colLen c - 1 + 1) := (Finset.sum_add_distrib).symm
      _ = ∑ c : Fin (α.rowLen 0), α.colLen c := by
          apply Finset.sum_congr rfl
          intro c _
          have := colLen_pos α c
          omega
      _ ≤ α.cells.card := sum_colLen_le α
  have h1 : ∑ _c : Fin (α.rowLen 0), 1 = α.rowLen 0 := by simp
  rw [h1] at hF
  have key : ∀ x ∈ MS (N0 := N0) t (∑ c : Fin (α.rowLen 0), (α.colLen c - 1)) (α.rowLen 0),
      (lapT N0 N1 t ^ n) (x * g) = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨L, rfl, e1, e2⟩ := hx
      have e : tmL t L 1 * g = tmL t L g := by simp [tmL]
      rw [e]
      exact lap_tm_zero t n L g d (fun a b => hg a b) hd (by rw [e1, e2]; omega)
    | zero => rw [zero_mul, map_zero]
    | add x y _ _ hx hy => rw [add_mul, map_add, hx, hy, add_zero]
    | smul r x _ hx => rw [smul_mul_assoc, map_smul, hx, smul_zero]
  exact key _ hF

end LapFormsSec

end PI.EntAtD.W
