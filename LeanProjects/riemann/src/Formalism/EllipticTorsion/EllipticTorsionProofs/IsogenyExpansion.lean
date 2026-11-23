import Formalism.EllipticTorsion.IsoExpand

open Finset

namespace Formalism.ELL.QuadraticDifferenceHypotheses

universe u

section Exact
variable {O M Q : Type u} [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup Q]

structure BiHyp (bar : O → O) (ψ : M → Q) : Prop where
  add1 : ∀ a a' b : M, quadDiff ψ (a + a') b = quadDiff ψ a b + quadDiff ψ a' b
  zero : ψ 0 = 0
  adj : ∀ (α : O) (a b : M), quadDiff ψ (α • a) b = quadDiff ψ a (bar α • b)

theorem qd_comm (ψ : M → Q) (a b : M) : quadDiff ψ a b = quadDiff ψ b a := by
  unfold quadDiff; rw [add_comm]; abel

theorem sum1 {bar : O → O} {ψ : M → Q} (H : BiHyp bar ψ) {ι : Type*}
    (s : Finset ι) (x : ι → M) (b : M) :
    quadDiff ψ (∑ e ∈ s, x e) b = ∑ e ∈ s, quadDiff ψ (x e) b :=
  map_sum (AddMonoidHom.mk' (fun a => quadDiff ψ a b) (fun a a' => H.add1 a a' b)) x s

theorem sum2 {bar : O → O} {ψ : M → Q} (H : BiHyp bar ψ) {ι : Type*}
    (s : Finset ι) (x : ι → M) (a : M) :
    quadDiff ψ a (∑ e ∈ s, x e) = ∑ e ∈ s, quadDiff ψ a (x e) := by
  rw [qd_comm, sum1 H]
  exact Finset.sum_congr rfl fun e _ => qd_comm _ _ _

theorem expand {bar : O → O} {ψ : M → Q} (H : BiHyp bar ψ) {ι : Type*}
    [LinearOrder ι] (s : Finset ι) (x : ι → M) :
    ψ (∑ e ∈ s, x e) = ∑ e ∈ s, ψ (x e) +
      ∑ e ∈ s, ∑ e' ∈ s.filter (fun e' => e < e'), quadDiff ψ (x e) (x e') := by
  refine Finset.induction_on_max s ?_ ?_
  · simp [H.zero]
  · intro a s hlt ih
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hdef : ∀ p q : M, ψ (p + q) = quadDiff ψ p q + ψ p + ψ q := by
      intro p q; unfold quadDiff; abel
    have hfa : (insert a s).filter (fun e' => a < e') = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact lt_irrefl _
      · exact not_lt.mpr (hlt z hz).le
    have hse : ∀ e ∈ s, ∑ e' ∈ (insert a s).filter (fun e' => e < e'), quadDiff ψ (x e) (x e') =
        quadDiff ψ (x e) (x a) + ∑ e' ∈ s.filter (fun e' => e < e'), quadDiff ψ (x e) (x e') := by
      intro e he
      rw [Finset.filter_insert, if_pos (hlt e he),
        Finset.sum_insert (fun h => ha (Finset.mem_filter.mp h).1)]
    rw [Finset.sum_insert ha, hdef, ih, Finset.sum_insert ha, Finset.sum_insert ha, hfa,
      Finset.sum_empty, Finset.sum_congr rfl hse, Finset.sum_add_distrib, qd_comm, sum1 H]
    abel

end Exact

section Quot
variable {O S M T : Type u} [CommRing O] [CommRing S] [AddCommGroup M] [Module O M]
    [AddCommGroup T] [Module S T]

theorem mk_quadDiff (N : AddSubgroup T) (φ : M → T) (a b : M) :
    QuotientAddGroup.mk' N (quadDiff φ a b) =
      quadDiff (fun a => QuotientAddGroup.mk' N (φ a)) a b := by
  simp [quadDiff, map_sub]

theorem biHyp_of {N : AddSubgroup T} {bar : O → O} {nrm : O → S} {φ : M → T}
    (h : QuadHyp N bar nrm φ) : BiHyp bar (fun a => QuotientAddGroup.mk' N (φ a)) := by
  have key : ∀ x : T, x ∈ N → QuotientAddGroup.mk' N x = 0 :=
    fun x hx => (QuotientAddGroup.eq_zero_iff x).mpr hx
  refine ⟨?_, key _ h.2.1, ?_⟩
  · intro a a' b
    have := key _ (h.1 a a' b)
    simp only [map_sub, mk_quadDiff] at this
    rw [sub_sub, sub_eq_zero] at this
    exact this
  · intro α a b
    have := key _ (h.2.2.2 α a b)
    simp only [map_sub, mk_quadDiff] at this
    exact sub_eq_zero.mp this

theorem mk_nrm {N : AddSubgroup T} {bar : O → O} {nrm : O → S} {φ : M → T}
    (h : QuadHyp N bar nrm φ) (α : O) (s : M) :
    QuotientAddGroup.mk' N (φ (α • s)) = QuotientAddGroup.mk' N (nrm α • φ s) :=
  sub_eq_zero.mp (by rw [← map_sub]; exact (QuotientAddGroup.eq_zero_iff _).mpr (h.2.2.1 α s))

theorem expand_mk {N : AddSubgroup T} {bar : O → O} {nrm : O → S} {φ : M → T}
    (h : QuadHyp N bar nrm φ) (n m : ℕ) (y : Fin m → Fin n → O) (t : Fin m → M) :
    QuotientAddGroup.mk' N (∑ i, φ (∑ e, y e i • t e)) =
      QuotientAddGroup.mk' N ((∑ e, (∑ i, nrm (y e i)) • φ (t e))
        + (∑ e, ∑ e' ∈ Finset.univ.filter (fun e' => e < e'),
            quadDiff φ (t e) ((∑ i, bar (y e i) * y e' i) • t e'))) := by
  set f := QuotientAddGroup.mk' N
  have H := biHyp_of h
  have e1 : ∀ i, f (φ (∑ e, y e i • t e)) = ∑ e, f (nrm (y e i) • φ (t e)) +
      ∑ e, ∑ e' ∈ Finset.univ.filter (fun e' => e < e'),
        quadDiff (fun a => f (φ a)) (t e) ((bar (y e i) * y e' i) • t e') := by
    intro i
    rw [expand H]
    congr 1
    · exact Finset.sum_congr rfl fun e _ => mk_nrm h _ _
    · refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun e' _ => ?_
      rw [H.adj, smul_smul]
  rw [map_sum, Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_add_distrib, map_add, map_sum,
    map_sum]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← map_sum, ← Finset.sum_smul]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_comm, map_sum]
    refine Finset.sum_congr rfl fun e' _ => ?_
    rw [mk_quadDiff, Finset.sum_smul, sum2 H]

end Quot

end Formalism.ELL.QuadraticDifferenceHypotheses

namespace Formalism.ELL

open Formalism.ELL.QuadraticDifferenceHypotheses

universe u

theorem isogeny_expansion : IsoExpand.{u} := by
  intro O S M T _ _ _ _ _ _ N bar nrm φ h n m y t
  have E := expand_mk h n m y t
  rw [← sub_eq_zero, ← map_sub] at E
  exact (QuotientAddGroup.eq_zero_iff _).mp E

theorem isogeny_vanishing : IsoVanish.{u} := by
  intro O S M T _ _ _ _ _ _ N bar nrm φ h n m y t hiso hnrm
  have E := isogeny_expansion O S M T N bar nrm φ h n m y t
  have hz : ∀ a : M, quadDiff φ a 0 ∈ N := fun a => by
    simpa [quadDiff] using neg_mem h.2.1
  simp only [hiso, hnrm, zero_smul, Finset.sum_const_zero, zero_add] at E
  have hS : (∑ e, ∑ e' ∈ Finset.univ.filter (fun e' => e < e'), quadDiff φ (t e) 0) ∈ N :=
    sum_mem fun e _ => sum_mem fun e' _ => hz _
  have := add_mem E hS
  rwa [sub_add_cancel] at this

end Formalism.ELL
