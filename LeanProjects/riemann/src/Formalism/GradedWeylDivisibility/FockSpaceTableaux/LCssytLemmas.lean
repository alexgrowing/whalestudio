import Formalism.GradedWeylDivisibility.StatementC

open MvPolynomial Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem lcssyt_card_initial {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (hP : ∀ t t' : Fin n, t' ≤ t → P t → P t') (t : Fin n) :
    t.val < (univ.filter P).card ↔ P t := by
  constructor
  · intro h
    by_contra hPt
    have hsub : univ.filter P ⊆ Iio t := by
      intro t' ht'
      simp only [mem_filter, mem_univ, true_and] at ht'
      simp only [mem_Iio]
      by_contra hle
      exact hPt (hP t' t (not_lt.mp hle) ht')
    have := card_le_card hsub
    rw [Fin.card_Iio] at this
    omega
  · intro hPt
    have hsub : Iic t ⊆ univ.filter P := by
      intro t' ht'
      simp only [mem_Iic] at ht'
      simp only [mem_filter, mem_univ, true_and]
      exact hP t t' ht' hPt
    have := card_le_card hsub
    rw [Fin.card_Iic] at this
    omega

theorem lcssyt_colExp_apply_lt {r n h : ℕ} (c : Fin h → Fin r) (hh : h ≤ n) (a : Fin r) (t : Fin n)
    (ht : t.val < h) : colExp c hh (a, t) = if c ⟨t.val, ht⟩ = a then 1 else 0 := by
  unfold colExp
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single ⟨t.val, ht⟩]
  · rw [Finsupp.single_apply]
    congr 1
    apply propext
    constructor
    · intro he; exact (Prod.ext_iff.mp he).1
    · intro he; exact Prod.ext he (Fin.ext rfl)
  · intro p _ hp
    rw [Finsupp.single_apply, if_neg]
    intro he
    apply hp
    have := congrArg (fun x => x.2.val) he
    exact Fin.ext (by simpa using this)
  · simp

theorem lcssyt_colExp_apply_ge {r n h : ℕ} (c : Fin h → Fin r) (hh : h ≤ n) (a : Fin r) (t : Fin n)
    (ht : ¬ t.val < h) : colExp c hh (a, t) = 0 := by
  unfold colExp
  rw [Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [Finsupp.single_apply, if_neg]
  intro he
  apply ht
  have := congrArg (fun x => x.2.val) he
  simp only [Fin.coe_castLE] at this
  omega

theorem lcssyt_colExp_sum_lt {r n h : ℕ} (c : Fin h → Fin r) (hh : h ≤ n) (S : Finset (Fin r)) (t : Fin n)
    (ht : t.val < h) : ∑ b ∈ S, colExp c hh (b, t) = if c ⟨t.val, ht⟩ ∈ S then 1 else 0 := by
  simp only [lcssyt_colExp_apply_lt c hh _ t ht]
  exact Finset.sum_ite_eq S (c ⟨t.val, ht⟩) (fun _ => 1)

theorem lcssyt_colExp_sum_ge {r n h : ℕ} (c : Fin h → Fin r) (hh : h ≤ n) (S : Finset (Fin r)) (t : Fin n)
    (ht : ¬ t.val < h) : ∑ b ∈ S, colExp c hh (b, t) = 0 := by
  simp [lcssyt_colExp_apply_ge c hh _ t ht]

theorem lcssyt_shapeDeg_cons {n K : ℕ} (h : ℕ) (sz : Fin K → ℕ) (t : Fin n) :
    shapeDeg (Fin.cons h sz : Fin (K + 1) → ℕ) t = (if t.val < h then 1 else 0) + shapeDeg sz t := by
  unfold shapeDeg
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

theorem lcssyt_consSz {n K h : ℕ} (hh : h ≤ n) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) :
    ∀ k : Fin (K + 1), (Fin.cons h sz : Fin (K + 1) → ℕ) k ≤ n := by
  intro k
  refine Fin.cases ?_ (fun i => ?_) k
  · simpa using hh
  · simpa using hsz i

def lcssyt_consI {r K h : ℕ} (sz : Fin K → ℕ) (c : Fin h → Fin r) (I : ∀ k, Fin (sz k) → Fin r) :
    ∀ k : Fin (K + 1), Fin ((Fin.cons h sz : Fin (K + 1) → ℕ) k) → Fin r :=
  fun k => Fin.cases (motive := fun k => Fin ((Fin.cons h sz : Fin (K + 1) → ℕ) k) → Fin r) c I k

theorem lcssyt_bidetExp_cons {r n K h : ℕ} (hh : h ≤ n) (c : Fin h → Fin r) (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r) :
    bidetExp (Fin.cons h sz : Fin (K + 1) → ℕ) (lcssyt_consSz hh sz hsz) (lcssyt_consI sz c I) =
      colExp c hh + bidetExp sz hsz I := by
  unfold bidetExp
  rw [Fin.sum_univ_succ]
  rfl

theorem lcssyt_consI_strictMono {r K h : ℕ} (sz : Fin K → ℕ) (c : Fin h → Fin r) (I : ∀ k, Fin (sz k) → Fin r)
    (hc : StrictMono c) (hI : ∀ k, StrictMono (I k)) : ∀ k, StrictMono (lcssyt_consI sz c I k) := by
  intro k
  refine Fin.cases ?_ (fun i => ?_) k
  · exact hc
  · exact hI i

end Formalism.GradedWeylDivisibility
