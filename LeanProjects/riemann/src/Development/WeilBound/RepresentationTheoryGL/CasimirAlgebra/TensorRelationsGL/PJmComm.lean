import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.LiftCommEAt

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace JMA

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem comp_swap {P : Type} [DecidableEq P] (I : P → Fin n) (p j : P) (_h : p ≠ j) :
    I ∘ Equiv.swap p j = Function.update (Function.update I p (I j)) j (I p) := by
  funext q
  simp only [Function.comp_apply, Function.update_apply, Equiv.swap_apply_def]
  split_ifs <;> subst_vars <;> simp_all

theorem pm_swap_eq {P : Type} [DecidableEq P] (p j : P) (h : p ≠ j) :
    (pm (Equiv.swap p j) : Module.End ℂ (TV n M P)) = ∑ a, ∑ b, eAt p a b * eAt j b a := by
  refine LinearMap.ext fun f => funext fun I => ?_
  rw [pm_apply, comp_swap I p j h]
  simp only [LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply, eAt_apply,
    Function.update_apply, if_neg (Ne.symm h)]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem xJ_eq {m : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (j : Fin m) :
    xJ E j = ∑ a, ∑ b, tE (Finset.univ.filter (· < j)) E a b * eAt j b a := by
  have hs : ∀ i ∈ Finset.univ.filter (· < j),
      pm (Equiv.swap i j) = ∑ a, ∑ b, (eAt i a b * eAt j b a : Module.End ℂ (TV n M (Fin m))) :=
    fun i hi => pm_swap_eq i j (ne_of_lt (Finset.mem_filter.1 hi).2)
  show Om E j + ∑ i ∈ Finset.univ.filter (· < j), pm (Equiv.swap i j) = _
  rw [Finset.sum_congr rfl hs]
  simp only [tE, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

theorem eAt_eq_sub {P : Type} [DecidableEq P] (S : Finset P) (j : P) (hj : j ∉ S)
    (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) :
    (eAt j a b : Module.End ℂ (TV n M P)) = tE (insert j S) E a b - tE S E a b := by
  simp only [tE, Finset.sum_insert hj]
  abel

theorem comm_xJ {m : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (j : Fin m) (X : Module.End ℂ (TV n M (Fin m)))
    (h1 : ∀ a b, Commute X (tE (Finset.univ.filter (· < j)) E a b))
    (h2 : ∀ a b, Commute X (tE (insert j (Finset.univ.filter (· < j))) E a b)) : Commute X (xJ E j) := by
  rw [xJ_eq]
  refine Commute.sum_right _ _ _ fun a _ => Commute.sum_right _ _ _ fun b _ => (h1 a b).mul_right ?_
  rw [eAt_eq_sub (Finset.univ.filter (· < j)) j (by simp) E]
  exact (h2 b a).sub_right (h1 b a)

theorem swap_pres {P : Type} [DecidableEq P] (S : Finset P) (i j : P) (h : i ∈ S ↔ j ∈ S) (q : P) :
    Equiv.swap i j q ∈ S ↔ q ∈ S := by
  rcases eq_or_ne q i with rfl | hi
  · rw [Equiv.swap_apply_left]
    exact h.symm
  rcases eq_or_ne q j with rfl | hj
  · rw [Equiv.swap_apply_right]
    exact h
  · rw [Equiv.swap_apply_of_ne_of_ne hi hj]

theorem swap_comm_xJ (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) {m : ℕ} (k i j : Fin m)
    (h1 : i < k ↔ j < k) (h2 : (i = k ∨ i < k) ↔ (j = k ∨ j < k)) :
    Commute (pm (Equiv.swap i j)) (xJ E k) :=
  comm_xJ E k _ (fun a b => (hT n M (Fin m) E hE _).2.2.1 _ (swap_pres _ i j (by simpa using h1)) a b)
    (fun a b => (hT n M (Fin m) E hE _).2.2.1 _ (swap_pres _ i j (by simpa using h2)) a b)

theorem om_comm_xJ (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) {m : ℕ} (i j : Fin m)
    (h : i < j) : Commute (Om E i) (xJ E j) :=
  comm_xJ E j _ (fun a b => (hT n M (Fin m) E hE _).2.1 i (by simpa using h) a b)
    (fun a b => (hT n M (Fin m) E hE _).2.1 i (by simp [h]) a b)

theorem xJ_comm_lt (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) {m : ℕ} (i j : Fin m)
    (h : i < j) : Commute (xJ E i) (xJ E j) := by
  show Commute (Om E i + ∑ l ∈ Finset.univ.filter (· < i), pm (Equiv.swap l i)) (xJ E j)
  refine (om_comm_xJ hT hE i j h).add_left (Commute.sum_left _ _ _ fun l hl => ?_)
  have hl' : l < i := (Finset.mem_filter.1 hl).2
  exact swap_comm_xJ hT hE j l i (iff_of_true (hl'.trans h) h)
    (iff_of_true (Or.inr (hl'.trans h)) (Or.inr h))

theorem xJ_comm (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) {m : ℕ} (i j : Fin m) :
    Commute (xJ E i) (xJ E j) := by
  rcases lt_trichotomy i j with h | rfl | h
  · exact xJ_comm_lt hT hE i j h
  · exact Commute.refl _
  · exact (xJ_comm_lt hT hE j i h).symm

theorem pm_swap_sq {P : Type} (i j : P) [DecidableEq P] :
    (pm (Equiv.swap i j) : Module.End ℂ (TV n M P)) * pm (Equiv.swap i j) = 1 := by
  rw [← pm_mul, Equiv.swap_mul_self, pm_one]

theorem xJ_succ (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) {m : ℕ} (i j : Fin m)
    (hij : (i : ℕ) + 1 = j) :
    xJ E j = pm (Equiv.swap i j) * xJ E i * pm (Equiv.swap i j) + pm (Equiv.swap i j) := by
  have hOm : pm (Equiv.swap i j) * Om E i * pm (Equiv.swap i j) = Om E j := by
    rw [(hT n M (Fin m) E hE (∅ : Finset (Fin m))).2.2.2, mul_assoc, pm_swap_sq, mul_one,
      Equiv.swap_apply_left]
  have hsum : ∀ l ∈ Finset.univ.filter (· < i),
      pm (Equiv.swap i j) * pm (Equiv.swap l i) * pm (Equiv.swap i j) =
        (pm (Equiv.swap l j) : Module.End ℂ (TV n M (Fin m))) := by
    intro l hl
    have hl' : (l : ℕ) < i := (Finset.mem_filter.1 hl).2
    rw [← pm_mul, ← pm_mul]
    congr 1
    refine Equiv.ext fun x => ?_
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
    split_ifs <;> simp_all [Fin.ext_iff] <;> omega
  have hset : Finset.univ.filter (· < j) = insert i (Finset.univ.filter (· < i)) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.lt_iff_val_lt_val, Fin.ext_iff]
    omega
  show Om E j + ∑ l ∈ Finset.univ.filter (· < j), pm (Equiv.swap l j) =
    pm (Equiv.swap i j) * (Om E i + ∑ l ∈ Finset.univ.filter (· < i), pm (Equiv.swap l i)) *
      pm (Equiv.swap i j) + pm (Equiv.swap i j)
  rw [hset, Finset.sum_insert (by simp), mul_add, add_mul, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_congr rfl hsum, hOm]
  abel

theorem xJ_mul_swap (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) {m : ℕ} (i j : Fin m)
    (hij : (i : ℕ) + 1 = j) : xJ E j * pm (Equiv.swap i j) = pm (Equiv.swap i j) * xJ E i + 1 := by
  rw [xJ_succ hT hE i j hij]
  simp only [add_mul, mul_assoc, pm_swap_sq, mul_one]

theorem swap_mul_xJ (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) {m : ℕ} (i j : Fin m)
    (hij : (i : ℕ) + 1 = j) : pm (Equiv.swap i j) * xJ E j = xJ E i * pm (Equiv.swap i j) + 1 := by
  rw [xJ_succ hT hE i j hij]
  simp only [mul_add, ← mul_assoc, pm_swap_sq, one_mul]

theorem list_prod_comm {A : Type} [Monoid A] (x : A) : ∀ (L : List A) (k : ℕ) (hk : k + 1 < L.length),
    (∀ t (ht : t < L.length), t ≠ k → t ≠ k + 1 → Commute L[t] x) → Commute (L[k] * L[k + 1]) x →
      Commute L.prod x
  | [], k, hk, _, _ => by simp at hk
  | [a], k, hk, _, _ => by simp at hk
  | a :: b :: L, 0, hk, h1, h2 => by
    rw [List.prod_cons, List.prod_cons, ← mul_assoc]
    refine h2.mul_left (Commute.list_prod_left _ _ fun y hy => ?_)
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hy
    exact h1 (t + 2) (by simp; omega) (by omega) (by omega)
  | a :: L, k + 1, hk, h1, h2 => by
    rw [List.prod_cons]
    exact (h1 0 (by simp) (by omega) (by omega)).mul_left (list_prod_comm x L k (by simpa using hk)
      (fun t ht h h' => h1 (t + 1) (by simpa using ht) (by omega) (by omega)) h2)

theorem pair_comm {A : Type} [Ring A] [Algebra ℂ A] (u : ℂ) (a b p : A) (hab : Commute a b)
    (h1 : b * p = p * a + 1) (h2 : p * b = a * p + 1) :
    Commute ((algebraMap ℂ A u + a) * (algebraMap ℂ A u + b)) p := by
  have hU : ∀ z : A, Commute (algebraMap ℂ A u) z := fun z => Algebra.commutes u z
  have hs : Commute (a + b) p := by
    show (a + b) * p = p * (a + b)
    rw [add_mul, mul_add, h1, h2]
    abel
  have hp : Commute (a * b) p := by
    show a * b * p = p * (a * b)
    calc a * b * p = a * (p * a + 1) := by rw [mul_assoc, h1]
      _ = (a * p + 1) * a := by noncomm_ring
      _ = p * b * a := by rw [h2]
      _ = p * (a * b) := by rw [mul_assoc, hab.eq]
  have he : (algebraMap ℂ A u + a) * (algebraMap ℂ A u + b) =
      algebraMap ℂ A u * algebraMap ℂ A u + algebraMap ℂ A u * (a + b) + a * b := by
    rw [add_mul, mul_add, mul_add, ← (hU a).eq, mul_add]
    abel
  rw [he]
  exact (((hU p).mul_left (hU p)).add_left ((hU p).mul_left hs)).add_left hp

theorem piJ_comm_adj (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) {m : ℕ} (u : ℂ)
    (i : Fin m) : Commute (PiJ (m + 1) E u) (pm (Equiv.swap i.castSucc i.succ)) := by
  have hij : ((i.castSucc : Fin (m + 1)) : ℕ) + 1 = i.succ := by simp
  show Commute (List.ofFn fun j : Fin (m + 1) => algebraMap ℂ (Module.End ℂ (TV n M (Fin (m + 1)))) u + xJ E j).prod _
  apply list_prod_comm _ _ i (by simp)
  · intro t ht h1 h2
    rw [List.getElem_ofFn]
    refine Commute.add_left (Algebra.commutes u _) ?_
    refine (swap_comm_xJ hT hE ⟨t, by simpa using ht⟩ i.castSucc i.succ ?_ ?_).symm
    · simp only [Fin.lt_iff_val_lt_val, Fin.coe_castSucc, Fin.val_succ]
      omega
    · simp only [Fin.lt_iff_val_lt_val, Fin.ext_iff, Fin.coe_castSucc, Fin.val_succ]
      omega
  · simp only [List.getElem_ofFn]
    exact pair_comm u _ _ _ (xJ_comm hT hE _ _) (xJ_mul_swap hT hE _ _ hij) (swap_mul_xJ hT hE _ _ hij)

theorem piJ_comm (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) (m : ℕ) (u : ℂ)
    (σ : Equiv.Perm (Fin m)) : Commute (PiJ m E u) (pm σ) := by
  cases m with
  | zero =>
    rw [Subsingleton.elim σ 1, pm_one]
    exact Commute.one_right _
  | succ m =>
    have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      trivial
    induction hσ using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact piJ_comm_adj hT hE u i
    | one =>
      rw [pm_one]
      exact Commute.one_right _
    | mul x y _ _ hx hy =>
      rw [pm_mul]
      exact hx.mul_right hy

end JMA

theorem jmComm_of : TensorGl → JMComm := by
  intro hT n M _ _ E hE m
  refine ⟨JMA.xJ_comm hT hE, fun i j h => ⟨JMA.xJ_mul_swap hT hE i j h, fun k hk1 hk2 => ?_⟩,
    fun u σ => JMA.piJ_comm hT hE m u σ⟩
  have e1 := Fin.val_ne_of_ne hk1
  have e2 := Fin.val_ne_of_ne hk2
  refine (JMA.swap_comm_xJ hT hE k i j ?_ ?_).symm
  · simp only [Fin.lt_iff_val_lt_val]
    omega
  · simp only [Fin.lt_iff_val_lt_val, Fin.ext_iff]
    omega

end PositivityTheory.Rg.Cz

end
