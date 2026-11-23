import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QsMnTranspose

noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

def qs_rem (D : Finset ℤ) (K : ℤ → Finset (Fin n)) (m : ↥D → Fin n) : ℤ → Finset (Fin n) :=
  fun c => if h : c ∈ D then (K c).erase (m ⟨c, h⟩) else K c

def qs_add (D : Finset ℤ) (J : ℤ → Finset (Fin n)) (a : ↥D → Fin n) : ℤ → Finset (Fin n) :=
  fun c => if h : c ∈ D then insert (a ⟨c, h⟩) (J c) else J c

lemma qs_rem_mem (D : Finset ℤ) (K : ℤ → Finset (Fin n)) (m : ↥D → Fin n) (c : ↥D) :
    qs_rem D K m c.1 = (K c.1).erase (m c) := by simp [qs_rem, c.2]

lemma qs_rem_not (D : Finset ℤ) (K : ℤ → Finset (Fin n)) (m : ↥D → Fin n) {c : ℤ} (hc : c ∉ D) :
    qs_rem D K m c = K c := by simp [qs_rem, hc]

lemma qs_add_mem (D : Finset ℤ) (K : ℤ → Finset (Fin n)) (m : ↥D → Fin n) (c : ↥D) :
    qs_add D K m c.1 = insert (m c) (K c.1) := by simp [qs_add, c.2]

lemma qs_add_not (D : Finset ℤ) (K : ℤ → Finset (Fin n)) (m : ↥D → Fin n) {c : ℤ} (hc : c ∉ D) :
    qs_add D K m c = K c := by simp [qs_add, hc]

lemma qs_rem_iff_add (D : Finset ℤ) (J K : ℤ → Finset (Fin n)) (m : ↥D → Fin n) :
    ((∀ c : ↥D, m c ∈ K c.1) ∧ J = qs_rem D K m) ↔ ((∀ c : ↥D, m c ∉ J c.1) ∧ K = qs_add D J m) := by
  constructor
  · rintro ⟨h1, rfl⟩
    refine ⟨fun c => by rw [qs_rem_mem]; simp, ?_⟩
    funext c
    by_cases hc : c ∈ D
    · have := qs_add_mem D (qs_rem D K m) m ⟨c, hc⟩
      have h2 := qs_rem_mem D K m ⟨c, hc⟩
      simp only at this h2
      rw [this, h2, Finset.insert_erase (h1 ⟨c, hc⟩)]
    · rw [qs_add_not _ _ _ hc, qs_rem_not _ _ _ hc]
  · rintro ⟨h1, rfl⟩
    refine ⟨fun c => by rw [qs_add_mem]; simp, ?_⟩
    funext c
    by_cases hc : c ∈ D
    · have := qs_rem_mem D (qs_add D J m) m ⟨c, hc⟩
      have h2 := qs_add_mem D J m ⟨c, hc⟩
      simp only at this h2
      rw [this, h2, Finset.erase_insert (h1 ⟨c, hc⟩)]
    · rw [qs_rem_not _ _ _ hc, qs_add_not _ _ _ hc]

variable {R : Type*} [CommRing R]

lemma qs_prod_split (S D : Finset ℤ) (hD : D ⊆ S) (F : ℤ → R) :
    ∏ c ∈ S, F c = (∏ c ∈ S \ D, F c) * ∏ c : ↥D, F c.1 := by
  rw [← Finset.prod_sdiff hD, Finset.prod_coe_sort]

lemma qs_sum_choices (S D : Finset ℤ) (hD : D ⊆ S) (u : ℤ → R) (p : ↥D → Fin n → Prop) [∀ c x, Decidable (p c x)]
    (s w : ↥D → Fin n → R) (F : (↥D → Fin n) → ℤ → R)
    (hF1 : ∀ m, ∀ c ∈ S \ D, F m c = u c) (hF2 : ∀ m (c : ↥D), F m c.1 = w c (m c))
    (v : ↥D → Fin n → R) :
    ∑ m : ↥D → Fin n, (if ∀ c, p c (m c) then (∏ c, s c (m c)) * (∏ c ∈ S, F m c) * ∏ c, v c (m c) else 0) =
      (∏ c ∈ S \ D, u c) * ∏ c : ↥D, ∑ x, if p c x then s c x * w c x * v c x else 0 := by
  rw [Fintype.prod_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Fintype.prod_ite_zero]
  split_ifs with h
  · rw [qs_prod_split S D hD, Finset.prod_congr rfl (hF1 m), Finset.prod_congr rfl (fun c _ => hF2 m c),
      Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    ring
  · rw [mul_zero]

variable (g : Matrix (Fin n) (Fin n) R)

theorem qs_core (S D : Finset ℤ) (hD : D ⊆ S) (J K : ℤ → Finset (Fin n)) (a : ↥D → Fin n) :
    ∑ m : ↥D → Fin n, (if ∀ c : ↥D, m c ∈ K c.1 then
        (∏ c : ↥D, ((qs_sg ((K c.1).erase (m c)) (m c) : ℤ) : R)) * (∏ c ∈ S, qs_mn g (J c) (qs_rem D K m c)) *
          ∏ c : ↥D, g (a c) (m c) else 0) =
      if ∀ c : ↥D, a c ∉ J c.1 then
        (∏ c : ↥D, ((qs_sg (J c.1) (a c) : ℤ) : R)) * ∏ c ∈ S, qs_mn g (qs_add D J a c) (K c) else 0 := by
  rw [qs_sum_choices S D hD (fun c => qs_mn g (J c) (K c)) (fun c x => x ∈ K c.1)
    (fun c x => ((qs_sg ((K c.1).erase x) x : ℤ) : R)) (fun c x => qs_mn g (J c.1) ((K c.1).erase x))
    (fun m c => qs_mn g (J c) (qs_rem D K m c))
    (fun m c hc => by rw [qs_rem_not _ _ _ (Finset.mem_sdiff.1 hc).2]) (fun m c => by rw [qs_rem_mem])]
  have h1 : ∀ c : ↥D, (∑ x, if x ∈ K c.1 then ((qs_sg ((K c.1).erase x) x : ℤ) : R) *
      qs_mn g (J c.1) ((K c.1).erase x) * g (a c) x else 0) =
      if a c ∉ J c.1 then ((qs_sg (J c.1) (a c) : ℤ) : R) * qs_mn g (insert (a c) (J c.1)) (K c.1) else 0 := by
    intro c
    rw [Finset.sum_ite_mem, Finset.univ_inter, qs_laplace, ite_not]
  rw [Finset.prod_congr rfl (fun c _ => h1 c), Fintype.prod_ite_zero]
  split_ifs with h
  · have e1 : ∏ c ∈ S \ D, qs_mn g (qs_add D J a c) (K c) = ∏ c ∈ S \ D, qs_mn g (J c) (K c) :=
      Finset.prod_congr rfl (fun c hc => by rw [qs_add_not _ _ _ (Finset.mem_sdiff.1 hc).2])
    have e2 : ∏ c : ↥D, qs_mn g (qs_add D J a c.1) (K c.1) = ∏ c : ↥D, qs_mn g (insert (a c) (J c.1)) (K c.1) :=
      Finset.prod_congr rfl (fun c _ => by rw [qs_add_mem])
    rw [qs_prod_split S D hD (fun c => qs_mn g (qs_add D J a c) (K c)), e1, e2, Finset.prod_mul_distrib]
    ring
  · rw [mul_zero]

theorem qs_laplace_inv (g' : Matrix (Fin n) (Fin n) R) (hg : g * g' = 1) (J K : Finset (Fin n)) (a : Fin n) :
    ∑ m, (if m ∉ K then ((qs_sg K m : ℤ) : R) * qs_mn g J (insert m K) * g' m a else 0) =
      if a ∈ J then ((qs_sg (J.erase a) a : ℤ) : R) * qs_mn g (J.erase a) K else 0 := by
  have h1 : ∀ m, (if m ∉ K then ((qs_sg K m : ℤ) : R) * qs_mn g J (insert m K) * g' m a else 0) =
      ∑ k ∈ J, ((qs_sg (J.erase k) k : ℤ) : R) * qs_mn g (J.erase k) K * (g k m * g' m a) := by
    intro m
    have := qs_laplace_col g J K m
    rw [← ite_not] at this
    calc _ = (if m ∉ K then ((qs_sg K m : ℤ) : R) * qs_mn g J (insert m K) else 0) * g' m a := by
          split_ifs <;> simp
      _ = _ := by rw [← this, Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [Finset.sum_congr rfl (fun m _ => h1 m), Finset.sum_comm]
  have h2 : ∀ k, ∑ m, g k m * g' m a = if k = a then 1 else 0 := by
    intro k
    have := congrFun (congrFun hg k) a
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    exact this
  simp_rw [← Finset.mul_sum, h2]
  simp [Finset.sum_ite_eq']

theorem qs_core_inv (g' : Matrix (Fin n) (Fin n) R) (hg : g * g' = 1) (S D : Finset ℤ) (hD : D ⊆ S)
    (J K : ℤ → Finset (Fin n)) (a : ↥D → Fin n) :
    ∑ m : ↥D → Fin n, (if ∀ c : ↥D, m c ∉ K c.1 then
        (∏ c : ↥D, ((qs_sg (K c.1) (m c) : ℤ) : R)) * (∏ c ∈ S, qs_mn g (J c) (qs_add D K m c)) *
          ∏ c : ↥D, g' (m c) (a c) else 0) =
      if ∀ c : ↥D, a c ∈ J c.1 then
        (∏ c : ↥D, ((qs_sg ((J c.1).erase (a c)) (a c) : ℤ) : R)) * ∏ c ∈ S, qs_mn g (qs_rem D J a c) (K c)
      else 0 := by
  rw [qs_sum_choices S D hD (fun c => qs_mn g (J c) (K c)) (fun c x => x ∉ K c.1)
    (fun c x => ((qs_sg (K c.1) x : ℤ) : R)) (fun c x => qs_mn g (J c.1) (insert x (K c.1)))
    (fun m c => qs_mn g (J c) (qs_add D K m c))
    (fun m c hc => by rw [qs_add_not _ _ _ (Finset.mem_sdiff.1 hc).2]) (fun m c => by rw [qs_add_mem])
    (fun c x => g' x (a c))]
  rw [Finset.prod_congr rfl (fun c _ => qs_laplace_inv g g' hg (J c.1) (K c.1) (a c)), Fintype.prod_ite_zero]
  split_ifs with h
  · have e1 : ∏ c ∈ S \ D, qs_mn g (qs_rem D J a c) (K c) = ∏ c ∈ S \ D, qs_mn g (J c) (K c) :=
      Finset.prod_congr rfl (fun c hc => by rw [qs_rem_not _ _ _ (Finset.mem_sdiff.1 hc).2])
    have e2 : ∏ c : ↥D, qs_mn g (qs_rem D J a c.1) (K c.1) = ∏ c : ↥D, qs_mn g ((J c.1).erase (a c)) (K c.1) :=
      Finset.prod_congr rfl (fun c _ => by rw [qs_rem_mem])
    rw [qs_prod_split S D hD (fun c => qs_mn g (qs_rem D J a c) (K c)), e1, e2, Finset.prod_mul_distrib]
    ring
  · rw [mul_zero]

end Formalism.InvariantFactorPaths.ColumnFamilies
