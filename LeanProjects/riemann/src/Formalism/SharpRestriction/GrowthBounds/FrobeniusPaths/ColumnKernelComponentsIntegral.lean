import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.LiftSubstitutionCoeffDivisible

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.LemmaBAlt

section Gen

variable {R : Type*} [CommRing R] {N k : ℕ}

def KKs (p : ℕ) (x : Fin N → Fin k → R) (pos : Fin N → ℤ) (mu : Fin (N + 1) → Fin k → ℤ) (c : ℤ) :
    ℕ → (Finset (Fin k) → R) × Option ℤ
  | 0 => (extOne, none)
  | j + 1 =>
    if h : j < N then
      let st := KKs p x pos mu c j
      let hP := colH (mu ⟨j, by omega⟩) c
      let hN := colH (mu ⟨j + 1, by omega⟩) c
      if hP = hN then st else
        let P := match st.2 with
          | none => 1
          | some sl => p ^ (pos ⟨j, h⟩ - sl).toNat
        (colStep c hP hN (x ⟨j, h⟩) (powC P st.1), some (pos ⟨j, h⟩))
    else KKs p x pos mu c j

def ZZ (p : ℕ) (x : Fin N → Fin k → R) (pos : Fin N → ℤ) (mu : Fin (N + 1) → Fin k → ℤ) (c : ℤ) (j : ℕ) (s : ℤ) :
    Finset (Fin k) → R :=
  match (KKs p x pos mu c j).2 with
  | none => (KKs p x pos mu c j).1
  | some sl => powC (p ^ (s - sl).toNat) (KKs p x pos mu c j).1

lemma powC_one (Kv : Finset (Fin k) → R) : powC 1 Kv = Kv := by
  funext J; simp [powC]

lemma ZZ_zero (p : ℕ) (x : Fin N → Fin k → R) (pos : Fin N → ℤ) (mu : Fin (N + 1) → Fin k → ℤ) (c : ℤ) (s : ℤ) :
    ZZ p x pos mu c 0 s = extOne := rfl

lemma ZZ_unused (p : ℕ) (x : Fin N → Fin k → R) (pos : Fin N → ℤ) (mu : Fin (N + 1) → Fin k → ℤ) (c : ℤ) (s : ℤ)
    (j : ℕ) (h : j < N) (hu : colH (mu ⟨j, by omega⟩) c = colH (mu ⟨j + 1, by omega⟩) c) :
    ZZ p x pos mu c (j + 1) s = ZZ p x pos mu c j s := by
  unfold ZZ; simp only [KKs, dif_pos h, if_pos hu]

lemma ZZ_used (p : ℕ) (x : Fin N → Fin k → R) (pos : Fin N → ℤ) (mu : Fin (N + 1) → Fin k → ℤ) (c : ℤ) (s : ℤ)
    (j : ℕ) (h : j < N) (hu : colH (mu ⟨j, by omega⟩) c ≠ colH (mu ⟨j + 1, by omega⟩) c) :
    ZZ p x pos mu c (j + 1) s = powC (p ^ (s - pos ⟨j, h⟩).toNat)
      (colStep c (colH (mu ⟨j, by omega⟩) c) (colH (mu ⟨j + 1, by omega⟩) c) (x ⟨j, h⟩)
        (ZZ p x pos mu c j (pos ⟨j, h⟩))) := by
  unfold ZZ; simp only [KKs, dif_pos h, if_neg hu]
  cases hst : (KKs p x pos mu c j).2 with
  | none => simp only [powC_one]
  | some sl => rfl

end Gen

section Link

variable (p f : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF p f) O] {N k : ℕ}

lemma KKstate_eq (LL : LiftLetters (Fin N)) (g : Matrix (Fin k) (Fin k) (WF p f)) (mu : Fin (N + 1) → Fin k → ℤ)
    (c : ℤ) (j : ℕ) :
    KKstate p f (O := O) LL g mu c j = KKs p (letG p f (O := O) LL g) LL.pos mu c j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [KKstate, KKs, ih]
    generalize KKs p (letG p f (O := O) LL g) LL.pos mu c j = st
    rcases st with ⟨a, _ | sl⟩ <;> rfl

lemma KKc_eq (LL : LiftLetters (Fin N)) (g : Matrix (Fin k) (Fin k) (WF p f)) (z : ℤ)
    (mu : Fin (N + 1) → Fin k → ℤ) (c : ℤ) :
    KKc p f (O := O) LL g z mu c = ZZ p (letG p f (O := O) LL g) LL.pos mu c N z := by
  unfold KKc ZZ; simp only [KKstate_eq]
  generalize KKs p (letG p f (O := O) LL g) LL.pos mu c N = st
  rcases st with ⟨a, _ | sl⟩ <;> rfl

end Link

section Closure

variable {A R : Type*} [CommRing A] [CommRing R] [Algebra A R] {N k : ℕ}

lemma colStep_mem (Sg : Subalgebra A R) (c : ℤ) (hP hN : ℕ) (x : Fin k → R) (Kv : Finset (Fin k) → R)
    (hx : ∀ b, x b ∈ Sg) (hK : ∀ J, Kv J ∈ Sg) (J : Finset (Fin k)) : colStep c hP hN x Kv J ∈ Sg := by
  have h1 : ∀ n : ℕ, ((-1 : R)) ^ n ∈ Sg := fun n => Sg.pow_mem (Sg.neg_mem Sg.one_mem) n
  unfold colStep wedgeR contrR
  split_ifs
  all_goals first
    | exact hK J
    | exact Sg.sum_mem fun m _ => Sg.mul_mem (Sg.mul_mem (h1 _) (hx m)) (hK _)

lemma ZZ_mem (Sg : Subalgebra A R) (p : ℕ) (x : Fin N → Fin k → R) (pos : Fin N → ℤ)
    (mu : Fin (N + 1) → Fin k → ℤ) (c : ℤ) (hx : ∀ i b, x i b ∈ Sg) (j : ℕ) (hj : j ≤ N) :
    ∀ (s : ℤ) (J : Finset (Fin k)), ZZ p x pos mu c j s J ∈ Sg := by
  induction j with
  | zero =>
    intro s J; rw [ZZ_zero]; unfold extOne; split_ifs
    · exact Sg.one_mem
    · exact Sg.zero_mem
  | succ j ih =>
    intro s J
    have h : j < N := hj
    by_cases hu : colH (mu ⟨j, by omega⟩) c = colH (mu ⟨j + 1, by omega⟩) c
    · rw [ZZ_unused p x pos mu c s j h hu]; exact ih (by omega) s J
    · rw [ZZ_used p x pos mu c s j h hu]
      exact Sg.pow_mem (colStep_mem Sg _ _ _ _ _ (hx _) (ih (by omega) _) J) _

end Closure

section Clause1

variable (p f : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra (WF p f) O] {N k : ℕ}

lemma letG_int (LL : LiftLetters (Fin N)) (g : Matrix (Fin k) (Fin k) (WF p f)) (hg : IsGLW g) (i : Fin N)
    (b : Fin k) : letG p f (O := O) LL g i b ∈ intSub O (Fin N × Fin k) := by
  unfold letG
  split_ifs
  · refine Subalgebra.sum_mem _ fun a _ => Subalgebra.mul_mem _ (X_mem_goodSub _ rfl) ?_
    rw [sigMat_apply]; exact C_mem_sub _ _
  · refine Subalgebra.sum_mem _ fun a _ => Subalgebra.mul_mem _ (X_mem_goodSub _ rfl) ?_
    rw [sigMat_inv p f O g hg, sigMat_apply]; exact C_mem_sub _ _

theorem column_kernel_components_integral (LL : LiftLetters (Fin N)) (g : Matrix (Fin k) (Fin k) (WF p f)) (hg : IsGLW g) (z : ℤ)
    (mu : Fin (N + 1) → Fin k → ℤ) (c : ℤ) (J : Finset (Fin k)) : InA (KKc p f (O := O) LL g z mu c J) := by
  rw [KKc_eq, ← mem_intSub]
  exact ZZ_mem _ p _ _ mu c (letG_int p f LL g hg) N le_rfl z J

end Clause1

section Clause5

variable {N r K : ℕ}

lemma costly_used (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (i : Fin N) (h : IsCostly mu c i) :
    IsUsed mu c i := by
  unfold IsUsed; rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

theorem column_order_le_two_power [NeZero N] (p : ℕ) (hp : 2 ≤ p) (pos : Fin N → ℤ) (z : ℤ) (hmono : Monotone pos)
    (hz : ∀ i, pos i ≤ z) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ)
    (hpos : ∀ i j : Fin N, i < j → IsUsed mu c i → IsCostly mu c j → pos i < pos j) :
    oc (fun i => p ^ (z - pos i).toNat) mu c ≤ 2 * p ^ (z - pos 0).toNat := by
  classical
  set E := (z - pos 0).toNat with hE
  have h1 : oc (fun i => p ^ (z - pos i).toNat) mu c =
      ∑ i ∈ univ.filter (fun i => IsCostly mu c i), p ^ (z - pos i).toNat := by
    unfold oc; rw [Finset.sum_filter]
  have hinj : Set.InjOn (fun i : Fin N => (z - pos i).toNat) (univ.filter (fun i => IsCostly mu c i) : Finset (Fin N)) := by
    intro i hi j hj hij
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi hj
    have hzi := hz i; have hzj := hz j
    simp only at hij
    rcases lt_trichotomy i j with h | h | h
    · have := hpos i j h (costly_used mu c i hi) hj; omega
    · exact h
    · have := hpos j i h (costly_used mu c j hj) hi; omega
  rw [h1, ← Finset.sum_image (f := fun e => p ^ e) hinj]
  have hsub : (univ.filter (fun i => IsCostly mu c i)).image (fun i : Fin N => (z - pos i).toNat) ⊆ range (E + 1) := by
    intro e he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    have : pos 0 ≤ pos i := hmono (Fin.zero_le i)
    rw [Finset.mem_range]; omega
  calc _ ≤ ∑ e ∈ range (E + 1), p ^ e := Finset.sum_le_sum_of_subset hsub
    _ = ∑ e ∈ range E, p ^ e + p ^ E := Finset.sum_range_succ _ _
    _ ≤ p ^ E + p ^ E := by
        have := Nat.geomSum_lt hp (s := range E) (n := E) (fun k hk => Finset.mem_range.mp hk)
        omega
    _ = 2 * p ^ E := by ring

end Clause5

section Maps

variable {R R' : Type*} [CommRing R] [CommRing R'] {N k : ℕ}

lemma colStep_map (φ : R →+* R') (c : ℤ) (hP hN : ℕ) (x : Fin k → R) (Kv : Finset (Fin k) → R)
    (J : Finset (Fin k)) :
    φ (colStep c hP hN x Kv J) = colStep c hP hN (fun b => φ (x b)) (fun J => φ (Kv J)) J := by
  unfold colStep wedgeR contrR
  split_ifs <;> simp [map_sum, map_mul, map_pow, map_neg, map_one]

lemma extOne_map (φ : R →+* R') (J : Finset (Fin k)) : φ (extOne J) = extOne J := by
  unfold extOne; split_ifs <;> simp

lemma ZZ_map (φ : R →+* R') (p : ℕ) (x : Fin N → Fin k → R) (pos : Fin N → ℤ)
    (mu : Fin (N + 1) → Fin k → ℤ) (c : ℤ) (j : ℕ) (hj : j ≤ N) :
    ∀ (s : ℤ) (J : Finset (Fin k)), φ (ZZ p x pos mu c j s J) = ZZ p (fun i b => φ (x i b)) pos mu c j s J := by
  induction j with
  | zero => intro s J; rw [ZZ_zero, ZZ_zero, extOne_map]
  | succ j ih =>
    intro s J
    have h : j < N := hj
    by_cases hu : colH (mu ⟨j, by omega⟩) c = colH (mu ⟨j + 1, by omega⟩) c
    · rw [ZZ_unused p x pos mu c s j h hu, ZZ_unused p _ pos mu c s j h hu]; exact ih (by omega) s J
    · rw [ZZ_used p x pos mu c s j h hu, ZZ_used p _ pos mu c s j h hu]
      simp only [powC, map_pow, colStep_map]
      congr 2
      funext J'; exact ih (by omega) _ J'

lemma colStep_smul (a : R) (c : ℤ) (hP hN : ℕ) (x : Fin k → R) (Kv : Finset (Fin k) → R) (J : Finset (Fin k)) :
    colStep c hP hN x (fun J => a * Kv J) J = a * colStep c hP hN x Kv J := by
  unfold colStep wedgeR contrR
  split_ifs
  all_goals first
    | rfl
    | (rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => by ring)

lemma extOne_pow (Q : ℕ) (hQ : Q ≠ 0) (J : Finset (Fin k)) : (extOne J : R) ^ Q = extOne J := by
  unfold extOne; split_ifs <;> simp [hQ]

lemma ZZ_pow (p : ℕ) (hp : p ≠ 0) (x : Fin N → Fin k → R) (pos : Fin N → ℤ)
    (mu : Fin (N + 1) → Fin k → ℤ) (c : ℤ) (j : ℕ) (hj : j ≤ N) (s s' : ℤ) (hs : s ≤ s')
    (hpos : ∀ i : Fin N, i.val < j → IsUsed mu c i → pos i ≤ s) :
    ZZ p x pos mu c j s' = powC (p ^ (s' - s).toNat) (ZZ p x pos mu c j s) := by
  induction j with
  | zero => funext J; simp only [ZZ_zero, powC]; rw [extOne_pow _ (pow_ne_zero _ hp)]
  | succ j ih =>
    have h : j < N := hj
    by_cases hu : colH (mu ⟨j, by omega⟩) c = colH (mu ⟨j + 1, by omega⟩) c
    · rw [ZZ_unused p x pos mu c s' j h hu, ZZ_unused p x pos mu c s j h hu]
      exact ih (by omega) fun i hi => hpos i (by omega)
    · rw [ZZ_used p x pos mu c s' j h hu, ZZ_used p x pos mu c s j h hu]
      have h1 : pos ⟨j, h⟩ ≤ s := hpos ⟨j, h⟩ (by simp) hu
      funext J
      simp only [powC]
      rw [← pow_mul, ← pow_add]
      congr 2; omega

end Maps

end Formalism.MainNotions.LemmaBAlt
