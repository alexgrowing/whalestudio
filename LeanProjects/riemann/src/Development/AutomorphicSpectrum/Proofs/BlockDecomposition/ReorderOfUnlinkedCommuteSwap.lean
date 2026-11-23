import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsListPairwiseNotRel

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.BZSegReorder

theorem exists_minimal_pair {h : ℕ} (R : Fin h → Fin h → Prop) (hex : ∃ a b, a < b ∧ R a b) :
    ∃ a b, a < b ∧ R a b ∧ ∀ c, a < c → c < b → ¬ R c b := by
  classical
  have ex : ∃ d : ℕ, ∃ a b : Fin h, a < b ∧ R a b ∧ b.1 - a.1 = d := by
    obtain ⟨a, b, hab, hR⟩ := hex
    exact ⟨_, a, b, hab, hR, rfl⟩
  obtain ⟨d, ⟨a, b, hab, hR, hd⟩, hmin⟩ :
      ∃ d : ℕ, (∃ a b : Fin h, a < b ∧ R a b ∧ b.1 - a.1 = d) ∧
        ∀ m < d, ¬ ∃ a b : Fin h, a < b ∧ R a b ∧ b.1 - a.1 = m :=
    ⟨Nat.find ex, Nat.find_spec ex, fun m hm => Nat.find_min ex hm⟩
  refine ⟨a, b, hab, hR, fun c hac hcb hc => hmin (b.1 - c.1) ?_ ⟨c, b, hcb, hc, rfl⟩⟩
  have h1 : a.1 < c.1 := hac
  have h2 : c.1 < b.1 := hcb
  omega

theorem arith_step {a b t h : ℕ} (ht : a + (t + 1) < b) (hb : b < h) :
    b - (t + 1) + 1 < h ∧ b - (t + 1) + 1 = b - t ∧ b - (t + 1) < b - t ∧ a < b - (t + 1) ∧ b - (t + 1) < b ∧ a + t < b := by
  omega

theorem arith_end {a b h : ℕ} (hab : a < b) (hb : b < h) :
    a + (b - a - 1) < b ∧ a + 1 < h ∧ b - (b - a - 1) = a + 1 ∧ a < b - (b - a - 1) := by
  omega

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_pair {h : ℕ} (Δ : Fin h → Segment k) (hord : ∀ i j, i < j → ¬ (Δ i).Precedes (Δ j))
    (hlk : ∃ i j, (Δ i).Linked (Δ j)) :
    ∃ a b : Fin h, a < b ∧ (Δ b).Precedes (Δ a) ∧ ∀ c, a < c → c < b → ¬ (Δ c).Linked (Δ b) := by
  obtain ⟨i, j, hij⟩ := hlk
  have hne : i ≠ j := fun e => Segment.not_linked_self (Δ j) (e ▸ hij)
  have ex : ∃ a b : Fin h, a < b ∧ (Δ a).Linked (Δ b) := by
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ⟨i, j, hlt, hij⟩
    · exact ⟨j, i, hlt, hij.symm⟩
  obtain ⟨a, b, hab, hlink, hmin⟩ := exists_minimal_pair (fun a b => (Δ a).Linked (Δ b)) ex
  exact ⟨a, b, hab, (Segment.linked_iff_precedes.1 hlink).resolve_left (hord a b hab), hmin⟩

theorem ntrans {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
    {G : Type} [Monoid G] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {τ : Representation ℂ G U}
    (a : Nonempty (ρ.Equiv σ)) (b : Nonempty (σ.Equiv τ)) : Nonempty (ρ.Equiv τ) := by
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  exact ⟨a.trans b⟩

theorem equiv_of_eq {h N : ℕ} {y y' : Fin h → IrrGL k} (e : y = y') (hy : ∑ a, (y a).1 = N)
    (hy' : ∑ a, (y' a).1 = N) : Nonempty ((prodIrr y hy).Equiv (prodIrr y' hy')) := by
  subst e
  exact ⟨Representation.Equiv.refl _⟩

theorem segment_swap_unlinked_adjacent (hcomm : GlobalTheory.BZSeg.LUnlinkedComm k) (hswap : GlobalTheory.BZSeg.SwapProd k) {h N : ℕ} (D : Fin h → Segment k)
    (y : Fin h → IrrGL k) (hy : ∑ a, (y a).1 = N) (hL : ∀ i, IsLSeg (D i) (y i).rep)
    (j : ℕ) (hj : j + 1 < h) (p : j < h) (hu : ¬ (D ⟨j, p⟩).Linked (D ⟨j + 1, hj⟩))
    (hd' : ∑ a, (y (Equiv.swap (⟨j, p⟩ : Fin h) ⟨j + 1, hj⟩ a)).1 = N) (M : ℕ)
    (hd2 : ∑ a, (![y ⟨j, p⟩, y ⟨j + 1, hj⟩] a).1 = M) (hd2' : ∑ a, (![y ⟨j + 1, hj⟩, y ⟨j, p⟩] a).1 = M) :
    Nonempty ((prodIrr y hy).Equiv (prodIrr (fun a => y (Equiv.swap (⟨j, p⟩ : Fin h) ⟨j + 1, hj⟩ a)) hd')) :=
  hswap h N y hy j hj M hd2 hd2' hd'
    (hcomm (D ⟨j, p⟩) (D ⟨j + 1, hj⟩) (y ⟨j, p⟩) (y ⟨j + 1, hj⟩) M hd2 hd2' hu (hL ⟨j, p⟩) (hL ⟨j + 1, hj⟩))

theorem step0 (hcomm : GlobalTheory.BZSeg.LUnlinkedComm k) (hswap : GlobalTheory.BZSeg.SwapProd k) {h N : ℕ} (D : Fin h → Segment k)
    (y : Fin h → IrrGL k) (hy : ∑ a, (y a).1 = N) (hL : ∀ i, IsLSeg (D i) (y i).rep)
    (j : ℕ) (hj : j + 1 < h) (p : j < h) (hu : ¬ (D ⟨j, p⟩).Linked (D ⟨j + 1, hj⟩))
    (hd' : ∑ a, (y (Equiv.swap (⟨j, p⟩ : Fin h) ⟨j + 1, hj⟩ a)).1 = N) :
    Nonempty ((prodIrr y hy).Equiv (prodIrr (fun a => y (Equiv.swap (⟨j, p⟩ : Fin h) ⟨j + 1, hj⟩ a)) hd')) :=
  segment_swap_unlinked_adjacent hcomm hswap D y hy hL j hj p hu hd' _ rfl (by simp [Fin.sum_univ_two, add_comm])

def Reach {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) (σ : Equiv.Perm (Fin h)) : Prop :=
  ∀ hd' : ∑ a, (x (σ a)).1 = N, Nonempty ((prodIrr x hd).Equiv (prodIrr (x ∘ σ) hd'))

theorem step (hcomm : GlobalTheory.BZSeg.LUnlinkedComm k) (hswap : GlobalTheory.BZSeg.SwapProd k) {h N : ℕ} {Δ : Fin h → Segment k}
    {x : Fin h → IrrGL k} (hd : ∑ a, (x a).1 = N) (hL : ∀ i, IsLSeg (Δ i) (x i).rep) (σ : Equiv.Perm (Fin h))
    (hσ : Reach x hd σ) (j : ℕ) (hj : j + 1 < h) (p : j < h)
    (hu : ¬ (Δ (σ ⟨j, p⟩)).Linked (Δ (σ ⟨j + 1, hj⟩))) :
    Reach x hd (σ * Equiv.swap (⟨j, p⟩ : Fin h) ⟨j + 1, hj⟩) := by
  intro hd'
  have h1 : ∑ a, (x (σ a)).1 = N := (Equiv.sum_comp σ (fun a => (x a).1)).trans hd
  have h2 : ∑ a, (x (σ (Equiv.swap (⟨j, p⟩ : Fin h) ⟨j + 1, hj⟩ a))).1 = N :=
    (Equiv.sum_comp (Equiv.swap (⟨j, p⟩ : Fin h) ⟨j + 1, hj⟩) (fun a => (x (σ a)).1)).trans h1
  have F := step0 hcomm hswap (fun a => Δ (σ a)) (fun a => x (σ a)) h1 (fun i => hL (σ i)) j hj p hu h2
  have G := equiv_of_eq (N := N) (y := fun a => x (σ (Equiv.swap (⟨j, p⟩ : Fin h) ⟨j + 1, hj⟩ a)))
    (y' := x ∘ ⇑(σ * Equiv.swap (⟨j, p⟩ : Fin h) ⟨j + 1, hj⟩)) rfl h2 hd'
  have E := equiv_of_eq (N := N) (y := x ∘ σ) (y' := fun a => x (σ a)) rfl h1 h1
  exact ntrans (ntrans (ntrans (hσ h1) E) F) G

theorem descend (hcomm : GlobalTheory.BZSeg.LUnlinkedComm k) (hswap : GlobalTheory.BZSeg.SwapProd k) {h N : ℕ} {Δ : Fin h → Segment k}
    {x : Fin h → IrrGL k} (hd : ∑ a, (x a).1 = N) (hL : ∀ i, IsLSeg (Δ i) (x i).rep) (a b : ℕ) (hb : b < h)
    (hun : ∀ (c : ℕ) (hc : c < h), a < c → c < b → ¬ (Δ ⟨c, hc⟩).Linked (Δ ⟨b, hb⟩))
    (t : ℕ) (ht : a + t < b) :
    ∃ σ : Equiv.Perm (Fin h), Reach x hd σ ∧
      σ ⟨b - t, lt_of_le_of_lt (Nat.sub_le b t) hb⟩ = ⟨b, hb⟩ ∧ ∀ i : Fin h, i.1 < b - t → σ i = i := by
  induction t with
  | zero => exact ⟨1, fun hd' => equiv_of_eq rfl hd hd', rfl, fun _ _ => rfl⟩
  | succ t ih =>
    obtain ⟨q1, q2, q3, q4, q5, q6⟩ := arith_step ht hb
    obtain ⟨σ, hE, hp, hfix⟩ := ih q6
    have e1 : (⟨b - (t + 1) + 1, q1⟩ : Fin h) = ⟨b - t, lt_of_le_of_lt (Nat.sub_le b t) hb⟩ := Fin.ext q2
    have s0 : σ ⟨b - (t + 1), Nat.lt_of_succ_lt q1⟩ = ⟨b - (t + 1), Nat.lt_of_succ_lt q1⟩ := hfix _ q3
    have s1 : σ ⟨b - (t + 1) + 1, q1⟩ = ⟨b, hb⟩ := by rw [e1]; exact hp
    refine ⟨σ * Equiv.swap (⟨b - (t + 1), Nat.lt_of_succ_lt q1⟩ : Fin h) ⟨b - (t + 1) + 1, q1⟩, ?_, ?_, ?_⟩
    · refine step hcomm hswap hd hL σ hE _ q1 _ ?_
      rw [s0, s1]
      exact hun _ _ q4 q5
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, s1]
    · intro i hi
      have n0 : i ≠ ⟨b - (t + 1), Nat.lt_of_succ_lt q1⟩ := fun e => by rw [e] at hi; exact lt_irrefl _ hi
      have n1 : i ≠ ⟨b - (t + 1) + 1, q1⟩ := fun e => by
        rw [e] at hi
        exact absurd hi (Nat.not_lt.2 (Nat.le_succ _))
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne n0 n1]
      exact hfix i (lt_of_lt_of_le hi (Nat.sub_le_sub_left (Nat.le_succ t) b))

theorem segment_reorder_linked_precedes (hcomm : GlobalTheory.BZSeg.LUnlinkedComm k) (hswap : GlobalTheory.BZSeg.SwapProd k) {h N : ℕ} {Δ : Fin h → Segment k}
    {x : Fin h → IrrGL k} (hd : ∑ a, (x a).1 = N) (hL : ∀ i, IsLSeg (Δ i) (x i).rep)
    (hord : ∀ i j, i < j → ¬ (Δ i).Precedes (Δ j)) (hlk : ∃ i j, (Δ i).Linked (Δ j)) :
    ∃ (σ : Equiv.Perm (Fin h)) (j : ℕ) (hj : j + 1 < h) (p : j < h),
      (Δ (σ ⟨j + 1, hj⟩)).Precedes (Δ (σ ⟨j, p⟩)) ∧ Reach x hd σ := by
  obtain ⟨a, b, hab, hpre, hmin⟩ := exists_pair Δ hord hlk
  obtain ⟨q1, q2, q3, q4⟩ := arith_end (show a.1 < b.1 from hab) b.2
  obtain ⟨σ, hE, hp, hfix⟩ := descend hcomm hswap hd hL a.1 b.1 b.2
    (fun c hc h1 h2 => hmin ⟨c, hc⟩ h1 h2) (b.1 - a.1 - 1) q1
  have e1 : (⟨a.1 + 1, q2⟩ : Fin h) = ⟨b.1 - (b.1 - a.1 - 1), lt_of_le_of_lt (Nat.sub_le _ _) b.2⟩ := Fin.ext q3.symm
  have s0 : σ ⟨a.1, Nat.lt_of_succ_lt q2⟩ = a := hfix a q4
  have s1 : σ ⟨a.1 + 1, q2⟩ = b := by rw [e1]; exact hp
  refine ⟨σ, a.1, q2, Nat.lt_of_succ_lt q2, ?_, hE⟩
  rw [s0, s1]
  exact hpre

theorem reorder : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.BZSeg.LUnlinkedComm k → GlobalTheory.BZSeg.SwapProd k → GlobalTheory.BZSeg.Reorder k :=
  fun _ _ _ _ _ hcomm hswap _ _ _ _ hd hL hord hlk =>
    (segment_reorder_linked_precedes hcomm hswap hd hL hord hlk).elim fun σ H => H.elim fun j H => H.elim fun hj H => H.elim fun _ H =>
      ⟨σ, j, hj, H.1, H.2⟩

end GlobalTheory.CompanionTheory.BZSegReorder
