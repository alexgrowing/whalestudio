import Mathlib
import Formalism.GradedWeylDivisibility.StatementA

open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace PI.MSC

theorem card_colLen_gt (ν : YoungDiagram) (t : ℕ) :
    (Finset.univ.filter fun c : Fin (ν.rowLen 0) => t < ν.colLen c).card = ν.rowLen t := by
  have hk : ν.rowLen t ≤ ν.rowLen 0 := ν.rowLen_anti 0 t (Nat.zero_le _)
  have hiff : ∀ c : Fin (ν.rowLen 0), t < ν.colLen c ↔ (c : ℕ) < ν.rowLen t := fun c => by
    rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]
  simp_rw [hiff]
  rw [← Finset.card_map Fin.valEmbedding]
  have hm : (Finset.univ.filter fun c : Fin (ν.rowLen 0) => (c : ℕ) < ν.rowLen t).map Fin.valEmbedding =
      Finset.range (ν.rowLen t) := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_range]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hx
      exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [hm, Finset.card_range]

theorem rowLen_eq_zero (ν : YoungDiagram) {t : ℕ} (ht : ν.colLen 0 ≤ t) : ν.rowLen t = 0 := by
  by_contra h
  have h0 : (t, 0) ∈ ν := YoungDiagram.mem_iff_lt_rowLen.2 (Nat.pos_of_ne_zero h)
  have h1 := YoungDiagram.mem_iff_lt_colLen.1 h0
  omega

theorem colLen_pos (ν : YoungDiagram) (c : Fin (ν.rowLen 0)) : 0 < ν.colLen c := by
  exact YoungDiagram.mem_iff_lt_colLen.1 (YoungDiagram.mem_iff_lt_rowLen.2 c.2)

theorem card_fiber {γ : Type*} [Fintype γ] (h : γ → ℕ) {v : ℕ} (hv : 0 < v) :
    (Finset.univ.filter fun x => h x = v).card + (Finset.univ.filter fun x => v < h x).card =
      (Finset.univ.filter fun x => v - 1 < h x).card := by
  classical
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx
      omega
    · intro hx
      omega
  · rw [Finset.disjoint_filter]
    intro x _ h1 h2
    omega

def sz0 (ν : YoungDiagram) : Fin (ν.rowLen 0) → ℕ := fun c => ν.colLen c

theorem hsz0 (ν : YoungDiagram) : ∀ c, sz0 ν c ≤ ν.colLen 0 := fun c => ν.colLen_anti 0 c (Nat.zero_le _)

def nuR (ν : YoungDiagram) : Fin (ν.colLen 0) → ℕ := fun t => ν.rowLen t

theorem shapeColumnDegree_columnSizes (ν : YoungDiagram) : shapeDeg (sz0 ν) (n := ν.colLen 0) = nuR ν := by
  funext t
  exact card_colLen_gt ν t

theorem initMinor_cast (R : Type) [CommRing R] {r n s s' : ℕ} (h : s' = s) (I : Fin s → Fin r)
    (hs : s ≤ n) (hs' : s' ≤ n) :
    initMinor R (I ∘ Fin.cast h) hs' = initMinor R I hs := by
  subst h
  rfl

theorem initMinor_zero (R : Type) [CommRing R] {r n s : ℕ} (h : s = 0) (I : Fin s → Fin r)
    (hs : s ≤ n) : initMinor R I hs = 1 := by
  subst h
  simp [initMinor]

private theorem reorder_lemma {α β : Type} [Fintype α] [Fintype β] (f : α → ℕ) (g : β → ℕ)
    (h : ∀ v, Nat.card {x // f x = v} = Nat.card {y // g y = v}) :
    ∃ e : α ≃ β, ∀ x, g (e x) = f x := by
  classical
  have h' : ∀ v, Nonempty ({x // f x = v} ≃ {y // g y = v}) := fun v => Finite.card_eq.1 (h v)
  let ev : ∀ v, {x // f x = v} ≃ {y // g y = v} := fun v => (h' v).some
  refine ⟨(Equiv.sigmaFiberEquiv f).symm.trans ((Equiv.sigmaCongrRight ev).trans
    (Equiv.sigmaFiberEquiv g)), fun x => ?_⟩
  exact (ev (f x) ⟨x, rfl⟩).2

theorem reorder (R : Type) [CommRing R] (ν : YoungDiagram) (N : ℕ) {K : ℕ} (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ ν.colLen 0) (I : ∀ k, Fin (sz k) → Fin N) (hI : ∀ k, StrictMono (I k))
    (hsh : shapeDeg sz = nuR ν) :
    ∃ J : ∀ c : Fin (ν.rowLen 0), Fin (sz0 ν c) → Fin N, (∀ c, StrictMono (J c)) ∧
      bideterminant R sz hsz I = bideterminant R (sz0 ν) (hsz0 ν) J := by
  classical
  have hcnt : ∀ t : ℕ, (Finset.univ.filter fun k => t < sz k).card =
      (Finset.univ.filter fun c : Fin (ν.rowLen 0) => t < ν.colLen c).card := by
    intro t
    rw [card_colLen_gt]
    by_cases ht : t < ν.colLen 0
    · have h := congrFun hsh ⟨t, ht⟩
      simpa [shapeDeg, nuR] using h
    · rw [rowLen_eq_zero ν (not_lt.1 ht), Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k _
      have := hsz k
      omega
  have hfib : ∀ v, 0 < v → (Finset.univ.filter fun k => sz k = v).card =
      (Finset.univ.filter fun c : Fin (ν.rowLen 0) => ν.colLen c = v).card := by
    intro v hv
    have h1 := card_fiber sz hv
    have h2 : (Finset.univ.filter fun c : Fin (ν.rowLen 0) => ν.colLen c = v).card +
        (Finset.univ.filter fun c : Fin (ν.rowLen 0) => v < ν.colLen c).card =
        (Finset.univ.filter fun c : Fin (ν.rowLen 0) => v - 1 < ν.colLen c).card :=
      card_fiber (fun c : Fin (ν.rowLen 0) => ν.colLen c) hv
    rw [hcnt, hcnt] at h1
    omega
  have hcard : ∀ v, Nat.card {x : {k : Fin K // 0 < sz k} // sz x.1 = v} =
      Nat.card {c : Fin (ν.rowLen 0) // ν.colLen c = v} := by
    intro v
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    rcases Nat.eq_zero_or_pos v with rfl | hv
    · rw [Fintype.card_eq_zero_iff.2 ⟨fun x => by have := x.2; have := x.1.2; omega⟩,
        Fintype.card_eq_zero_iff.2 ⟨fun c => by have := c.2; have := colLen_pos ν c.1; omega⟩]
    · rw [Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun k => 0 < sz k)
        (fun k => sz k = v)), Fintype.card_subtype, Fintype.card_subtype, ← hfib v hv]
      have hf : (Finset.univ.filter fun k : Fin K => 0 < sz k ∧ sz k = v) =
          Finset.univ.filter fun k => sz k = v :=
        Finset.filter_congr fun k _ => ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
      rw [hf]
  obtain ⟨e, he⟩ := reorder_lemma (fun x : {k : Fin K // 0 < sz k} => sz x.1)
    (fun c : Fin (ν.rowLen 0) => ν.colLen c) hcard
  have hJ : ∀ c, sz0 ν c = sz (e.symm c).1 := by
    intro c
    have h := he (e.symm c)
    rw [e.apply_symm_apply] at h
    exact h
  refine ⟨fun c => I (e.symm c).1 ∘ Fin.cast (hJ c), fun c => ?_, ?_⟩
  · intro a b hab
    exact hI _ hab
  · unfold bideterminant
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun k => 0 < sz k)]
    have h1 : ∏ k : {k // ¬ 0 < sz k}, initMinor R (I k.1) (hsz k.1) = 1 :=
      Finset.prod_eq_one fun k _ => initMinor_zero R (by have := k.2; omega) _ _
    rw [h1, mul_one]
    exact (Fintype.prod_equiv e.symm _ _
      (fun c => initMinor_cast R (hJ c) (I (e.symm c).1) (hsz _) (hsz0 ν c))).symm

end PI.MSC
