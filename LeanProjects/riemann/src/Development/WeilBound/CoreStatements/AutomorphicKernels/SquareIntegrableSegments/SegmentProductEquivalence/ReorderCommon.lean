import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleAppendEquivStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsListPairwiseNotRel
import BuildAid.D4

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace PositivityTheory.PfEss.Zc2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ntrans {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U]
    [Module ℂ U] {G : Type} [Group G] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    {τ : Representation ℂ G U} (a : Nonempty (ρ.Equiv σ)) (b : Nonempty (σ.Equiv τ)) : Nonempty (ρ.Equiv τ) :=
  a.elim fun a => b.elim fun b => ⟨a.trans b⟩

theorem prodIrr_equiv_of_eq {h N : ℕ} {y y' : Fin h → IrrGL k} (e : y = y') (hy : ∑ a, (y a).1 = N)
    (hy' : ∑ a, (y' a).1 = N) : Nonempty ((prodIrr y hy).Equiv (prodIrr y' hy')) := by
  subst e
  exact ⟨Representation.Equiv.refl _⟩

theorem cut_e {h j : ℕ} (hj : j + 1 < h) : j + (2 + (h - (j + 2))) = h := by omega

theorem cutC_lt {h j b : ℕ} (hb : b < h - (j + 2)) : j + 2 + b < h := by omega

def cutA {α : Type*} {h : ℕ} (x : Fin h → α) (j : ℕ) (hj : j + 1 < h) : Fin j → α :=
  fun a => x ⟨a.1, lt_trans a.2 (Nat.lt_of_succ_lt hj)⟩

def cutC {α : Type*} {h : ℕ} (x : Fin h → α) (j : ℕ) : Fin (h - (j + 2)) → α :=
  fun b => x ⟨j + 2 + b.1, cutC_lt b.2⟩

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in

theorem sum_append {q c : ℕ} (Q : Fin q → IrrGL k) (C : Fin c → IrrGL k) :
    ∑ a, (Fin.append Q C a).1 = ∑ a, (Q a).1 + ∑ a, (C a).1 := by
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in

theorem sum_split2 {p q n : ℕ} (A : Fin p → IrrGL k) (R : Fin q → IrrGL k) (w : Fin n → IrrGL k) (e : p + q = n)
    (hw : ∀ m : Fin (p + q), w (Fin.cast e m) = Fin.append A R m) :
    ∑ a, (w a).1 = ∑ a, (A a).1 + ∑ a, (R a).1 := by
  subst e
  have hw' : w = Fin.append A R := funext fun m => hw m
  subst hw'
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem stage2 {p q n rA rR : ℕ} (A : Fin p → IrrGL k) (R : Fin q → IrrGL k) (w : Fin n → IrrGL k)
    (e : p + q = n) (hw : ∀ m : Fin (p + q), w (Fin.cast e m) = Fin.append A R m)
    (hA : ∑ a, (A a).1 = rA) (hR : ∑ a, (R a).1 = rR) (hN : ∑ a, (w a).1 = rA + rR) :
    Nonempty ((prod₂ (prodIrr A hA) (prodIrr R hR)).Equiv (prodIrr w hN)) := by
  subst e
  have hw' : w = Fin.append A R := funext fun m => hw m
  subst hw'
  exact GlobalTheory.T.product_irreducible_append_equiv k p q rA rR A R hA hR hN

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem head_swap {c rQ rC : ℕ} (Q Q' : Fin 2 → IrrGL k) (C : Fin c → IrrGL k)
    (hQ : ∑ a, (Q a).1 = rQ) (hQ' : ∑ a, (Q' a).1 = rQ) (hC : ∑ a, (C a).1 = rC)
    (hR : ∑ a, (Fin.append Q C a).1 = rQ + rC) (hR' : ∑ a, (Fin.append Q' C a).1 = rQ + rC)
    (E : Nonempty ((prodIrr Q hQ).Equiv (prodIrr Q' hQ'))) :
    Nonempty ((prodIrr (Fin.append Q C) hR).Equiv (prodIrr (Fin.append Q' C) hR')) := by
  obtain ⟨E⟩ := E
  obtain ⟨o1⟩ := GlobalTheory.T.product_irreducible_append_equiv k 2 c rQ rC Q C hQ hC hR
  obtain ⟨o2⟩ := GlobalTheory.T.product_irreducible_append_equiv k 2 c rQ rC Q' C hQ' hC hR'
  exact ⟨o1.symm.trans ((prod₂Equiv E (Representation.Equiv.refl _)).trans o2)⟩

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in

theorem split_alt_alt {h j : ℕ} (hj : j + 1 < h) (e : j + (2 + (h - (j + 2))) = h) (x : Fin h → IrrGL k)
    (m : Fin (j + (2 + (h - (j + 2))))) :
    x (Fin.cast e m) = Fin.append (cutA x j hj)
      (Fin.append ![x ⟨j, Nat.lt_of_succ_lt hj⟩, x ⟨j + 1, hj⟩]
        (cutC x j)) m := by
  refine Fin.addCases (fun a => ?_) (fun b => ?_) m
  · rw [Fin.append_left]
    exact congrArg x (Fin.ext (by simp))
  · rw [Fin.append_right]
    refine Fin.addCases (fun b => ?_) (fun b => ?_) b
    · rw [Fin.append_left]
      fin_cases b
      · exact congrArg x (Fin.ext (by simp))
      · exact congrArg x (Fin.ext (by simp))
    · rw [Fin.append_right]
      exact congrArg x (Fin.ext (by simp; omega))

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in

theorem split_swap {h j : ℕ} (hj : j + 1 < h) (e : j + (2 + (h - (j + 2))) = h) (x : Fin h → IrrGL k)
    (m : Fin (j + (2 + (h - (j + 2))))) :
    x (Equiv.swap (⟨j, Nat.lt_of_succ_lt hj⟩ : Fin h) ⟨j + 1, hj⟩ (Fin.cast e m)) =
      Fin.append (cutA x j hj)
      (Fin.append ![x ⟨j + 1, hj⟩, x ⟨j, Nat.lt_of_succ_lt hj⟩]
        (cutC x j)) m := by
  refine Fin.addCases (fun a => ?_) (fun b => ?_) m
  · rw [Fin.append_left]
    have h0 : (Fin.cast e (Fin.castAdd (2 + (h - (j + 2))) a) : Fin h) = ⟨a.1, by have := a.2; omega⟩ :=
      Fin.ext (by simp)
    rw [h0, Equiv.swap_apply_of_ne_of_ne (fun H => by have := a.2; simp [Fin.ext_iff] at H; omega)
      (fun H => by have := a.2; simp [Fin.ext_iff] at H; omega)]
    rfl
  · rw [Fin.append_right]
    refine Fin.addCases (fun b => ?_) (fun b => ?_) b
    · rw [Fin.append_left]
      fin_cases b
      · have h0 : (Fin.cast e (Fin.natAdd j (Fin.castAdd (h - (j + 2)) (0 : Fin 2))) : Fin h) = ⟨j, Nat.lt_of_succ_lt hj⟩ :=
          Fin.ext (by simp)
        simp only [Fin.zero_eta, Fin.isValue] at h0 ⊢
        rw [h0, Equiv.swap_apply_left]
        rfl
      · have h0 : (Fin.cast e (Fin.natAdd j (Fin.castAdd (h - (j + 2)) (1 : Fin 2))) : Fin h) = ⟨j + 1, hj⟩ :=
          Fin.ext (by simp)
        simp only [Fin.mk_one, Fin.isValue] at h0 ⊢
        rw [h0, Equiv.swap_apply_right]
        rfl
    · rw [Fin.append_right]
      have h0 : (Fin.cast e (Fin.natAdd j (Fin.natAdd 2 b)) : Fin h) = ⟨j + 2 + b.1, by have := b.2; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [h0, Equiv.swap_apply_of_ne_of_ne (fun H => by simp [Fin.ext_iff] at H; omega)
        (fun H => by simp [Fin.ext_iff] at H; omega)]
      rfl

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem swap_adj {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) (j : ℕ) (hj : j + 1 < h) (M : ℕ)
    (hd2 : ∑ a, (![x ⟨j, Nat.lt_of_succ_lt hj⟩, x ⟨j + 1, hj⟩] a).1 = M)
    (hd2' : ∑ a, (![x ⟨j + 1, hj⟩, x ⟨j, Nat.lt_of_succ_lt hj⟩] a).1 = M)
    (hd' : ∑ a, (x (Equiv.swap (⟨j, Nat.lt_of_succ_lt hj⟩ : Fin h) ⟨j + 1, hj⟩ a)).1 = N)
    (E : Nonempty ((prodIrr ![x ⟨j, Nat.lt_of_succ_lt hj⟩, x ⟨j + 1, hj⟩] hd2).Equiv
      (prodIrr ![x ⟨j + 1, hj⟩, x ⟨j, Nat.lt_of_succ_lt hj⟩] hd2'))) :
    Nonempty ((prodIrr x hd).Equiv
      (prodIrr (fun a => x (Equiv.swap (⟨j, Nat.lt_of_succ_lt hj⟩ : Fin h) ⟨j + 1, hj⟩ a)) hd')) := by
  have e := cut_e hj
  have hw1 := split_alt_alt hj e x
  have hw2 := split_swap hj e x
  have s1 := sum_split2 _ _ x e hw1
  have sR := sum_append ![x ⟨j, Nat.lt_of_succ_lt hj⟩, x ⟨j + 1, hj⟩] (cutC x j)
  have sR' := sum_append ![x ⟨j + 1, hj⟩, x ⟨j, Nat.lt_of_succ_lt hj⟩] (cutC x j)
  rw [hd2] at sR
  rw [hd2'] at sR'
  rw [sR] at s1
  have eN : N = _ := hd.symm.trans s1
  subst eN
  have ER := head_swap _ _ _ hd2 hd2' rfl sR sR' E
  obtain ⟨ER⟩ := ER
  obtain ⟨o1⟩ := stage2 _ _ x e hw1 rfl sR hd
  obtain ⟨o2⟩ := stage2 _ _ _ e hw2 rfl sR' hd'
  exact ⟨o1.symm.trans ((prod₂Equiv (Representation.Equiv.refl _) ER).trans o2)⟩

def Reach {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) (σ : Equiv.Perm (Fin h)) : Prop :=
  ∀ hd' : ∑ a, (x (σ a)).1 = N, Nonempty ((prodIrr x hd).Equiv (prodIrr (x ∘ σ) hd'))

set_option maxHeartbeats 1000000 in

theorem reach_step (hcomm : LUnlinkedComm k) {h N : ℕ} {Δ : Fin h → Segment k} {x : Fin h → IrrGL k}
    (hd : ∑ a, (x a).1 = N) (hL : ∀ i, IsLSeg (Δ i) (x i).rep) (σ : Equiv.Perm (Fin h)) (hσ : Reach x hd σ)
    (j : ℕ) (hj : j + 1 < h) (hu : ¬ (Δ (σ ⟨j, Nat.lt_of_succ_lt hj⟩)).Linked (Δ (σ ⟨j + 1, hj⟩))) :
    Reach x hd (σ * Equiv.swap (⟨j, Nat.lt_of_succ_lt hj⟩ : Fin h) ⟨j + 1, hj⟩) := by
  intro hd'
  have h1 : ∑ a, (x (σ a)).1 = N := (Equiv.sum_comp σ (fun a => (x a).1)).trans hd
  have h2 : ∑ a, (x (σ (Equiv.swap (⟨j, Nat.lt_of_succ_lt hj⟩ : Fin h) ⟨j + 1, hj⟩ a))).1 = N :=
    (Equiv.sum_comp (Equiv.swap (⟨j, Nat.lt_of_succ_lt hj⟩ : Fin h) ⟨j + 1, hj⟩) (fun a => (x (σ a)).1)).trans h1
  have F := swap_adj (fun a => x (σ a)) h1 j hj _ rfl (by simp [Fin.sum_univ_two, add_comm]) h2
    (hcomm _ _ _ _ _ _ _ hu (hL _) (hL _))
  have E1 := prodIrr_equiv_of_eq (N := N) (y := x ∘ σ) (y' := fun a => x (σ a)) rfl h1 h1
  have E2 := prodIrr_equiv_of_eq (N := N)
    (y := fun a => x (σ (Equiv.swap (⟨j, Nat.lt_of_succ_lt hj⟩ : Fin h) ⟨j + 1, hj⟩ a)))
    (y' := x ∘ ⇑(σ * Equiv.swap (⟨j, Nat.lt_of_succ_lt hj⟩ : Fin h) ⟨j + 1, hj⟩)) rfl h2 hd'
  exact ntrans (ntrans (ntrans (hσ h1) E1) F) E2

theorem strictMono_of_adj {h : ℕ} (f : Fin h → Fin h)
    (H : ∀ (j : ℕ) (hj : j + 1 < h), f ⟨j, Nat.lt_of_succ_lt hj⟩ < f ⟨j + 1, hj⟩) : StrictMono f := by
  have key : ∀ (d a : ℕ) (ha : a + d + 1 < h), f ⟨a, by omega⟩ < f ⟨a + d + 1, ha⟩ := by
    intro d
    induction d with
    | zero => intro a ha; exact H a ha
    | succ d ih =>
      intro a ha
      have H1 := H (a + d + 1) (by omega)
      have e1 : (⟨a + (d + 1) + 1, ha⟩ : Fin h) = ⟨a + d + 1 + 1, by omega⟩ :=
        Fin.ext (by show a + (d + 1) + 1 = a + d + 1 + 1; omega)
      rw [e1]
      exact (ih a (by omega)).trans H1
  intro a b hab
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  have hab' : a < b := hab
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d + 1 := ⟨b - a - 1, by omega⟩
  exact key d a hb

theorem swap_lt_swap {h j : ℕ} (hj : j + 1 < h) {u v : Fin h} (hvu : v < u)
    (H : Equiv.swap (⟨j, Nat.lt_of_succ_lt hj⟩ : Fin h) ⟨j + 1, hj⟩ u < Equiv.swap (⟨j, Nat.lt_of_succ_lt hj⟩ : Fin h) ⟨j + 1, hj⟩ v) :
    v.1 = j ∧ u.1 = j + 1 := by
  obtain ⟨u, hu⟩ := u
  obtain ⟨v, hv⟩ := v
  have hvu' : v < u := hvu
  simp only [Equiv.swap_apply_def, Fin.ext_iff] at H ⊢
  split_ifs at H <;> simp only [Fin.lt_def] at H <;> omega

def invSet {h : ℕ} (σ : Equiv.Perm (Fin h)) : Finset (Fin h × Fin h) :=
  Finset.univ.filter fun p => p.1 < p.2 ∧ σ.symm p.2 < σ.symm p.1

theorem symm_mul_swap_apply {h : ℕ} (σ s : Equiv.Perm (Fin h)) (a b : Fin h) (hs : s = Equiv.swap a b)
    (p : Fin h) : (σ * s).symm p = s (σ.symm p) := by
  rw [Equiv.Perm.mul_def, Equiv.symm_trans_apply, hs, Equiv.symm_swap]

theorem reach_of_inv (hcomm : LUnlinkedComm k) {h N : ℕ} {Δ : Fin h → Segment k} {x : Fin h → IrrGL k}
    (hd : ∑ a, (x a).1 = N) (hL : ∀ i, IsLSeg (Δ i) (x i).rep) :
    ∀ (n : ℕ) (σ : Equiv.Perm (Fin h)), (invSet σ).card = n →
      (∀ a b, a < b → σ.symm b < σ.symm a → ¬ (Δ a).Linked (Δ b)) → Reach x hd σ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro σ hn hσ
  by_cases hdesc : ∃ (j : ℕ) (hj : j + 1 < h), σ ⟨j + 1, hj⟩ < σ ⟨j, Nat.lt_of_succ_lt hj⟩
  · obtain ⟨j, hj, hlt⟩ := hdesc
    obtain ⟨s, hs⟩ : ∃ s, s = Equiv.swap (⟨j, Nat.lt_of_succ_lt hj⟩ : Fin h) ⟨j + 1, hj⟩ := ⟨_, rfl⟩
    have hτs : ∀ p, (σ * s).symm p = s (σ.symm p) := symm_mul_swap_apply σ s _ _ hs
    have sj : s ⟨j, Nat.lt_of_succ_lt hj⟩ = ⟨j + 1, hj⟩ := by rw [hs, Equiv.swap_apply_left]
    have sj1 : s ⟨j + 1, hj⟩ = ⟨j, Nat.lt_of_succ_lt hj⟩ := by rw [hs, Equiv.swap_apply_right]
    have hsub : invSet (σ * s) ⊆ invSet σ := by
      intro p hp
      simp only [invSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      refine ⟨hp.1, ?_⟩
      rcases lt_trichotomy (σ.symm p.2) (σ.symm p.1) with H | H | H
      · exact H
      · exact absurd (σ.symm.injective H) (ne_of_gt hp.1)
      · exfalso
        rw [hτs, hτs, hs] at hp
        obtain ⟨e1, e2⟩ := swap_lt_swap hj H hp.2
        have q1 : p.1 = σ ⟨j, Nat.lt_of_succ_lt hj⟩ := by
          rw [← Equiv.apply_symm_apply σ p.1]; exact congrArg σ (Fin.ext e1)
        have q2 : p.2 = σ ⟨j + 1, hj⟩ := by
          rw [← Equiv.apply_symm_apply σ p.2]; exact congrArg σ (Fin.ext e2)
        have h12 := hp.1
        rw [q1, q2] at h12
        exact absurd (hlt.trans h12) (lt_irrefl _)
    have hmem : (σ ⟨j + 1, hj⟩, σ ⟨j, Nat.lt_of_succ_lt hj⟩) ∈ invSet σ := by
      simp only [invSet, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
      exact ⟨hlt, by simp [Fin.lt_def]⟩
    have hnot : (σ ⟨j + 1, hj⟩, σ ⟨j, Nat.lt_of_succ_lt hj⟩) ∉ invSet (σ * s) := by
      simp only [invSet, Finset.mem_filter, Finset.mem_univ, true_and, hτs, Equiv.symm_apply_apply, not_and]
      intro _
      rw [sj, sj1]
      simp [Fin.lt_def]
    have hlt' : (invSet (σ * s)).card < n := by
      rw [← hn]
      exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2 ⟨_, hmem, hnot⟩)
    have hτinv : ∀ a b, a < b → (σ * s).symm b < (σ * s).symm a → ¬ (Δ a).Linked (Δ b) := by
      intro a b hab hba
      have hab2 : (a, b) ∈ invSet (σ * s) := by
        simp only [invSet, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hab, hba⟩
      have hab3 := hsub hab2
      simp only [invSet, Finset.mem_filter, Finset.mem_univ, true_and] at hab3
      exact hσ a b hab3.1 hab3.2
    have Rτ := ih _ hlt' (σ * s) rfl hτinv
    have hτj : (σ * s) ⟨j, Nat.lt_of_succ_lt hj⟩ = σ ⟨j + 1, hj⟩ := by rw [Equiv.Perm.mul_apply, sj]
    have hτj1 : (σ * s) ⟨j + 1, hj⟩ = σ ⟨j, Nat.lt_of_succ_lt hj⟩ := by rw [Equiv.Perm.mul_apply, sj1]
    have hu : ¬ (Δ ((σ * s) ⟨j, Nat.lt_of_succ_lt hj⟩)).Linked (Δ ((σ * s) ⟨j + 1, hj⟩)) := by
      rw [hτj, hτj1]
      exact hσ _ _ hlt (by simp [Fin.lt_def])
    have R := reach_step hcomm hd hL (σ * s) Rτ j hj hu
    have hσ' : σ * s * Equiv.swap (⟨j, Nat.lt_of_succ_lt hj⟩ : Fin h) ⟨j + 1, hj⟩ = σ := by
      rw [hs, mul_assoc, Equiv.swap_mul_self, mul_one]
    rw [hσ'] at R
    exact R
  · push Not at hdesc
    have hmono : StrictMono σ := strictMono_of_adj σ fun j hj =>
      lt_of_le_of_ne (hdesc j hj) (fun H => by have H2 := σ.injective H; simp [Fin.ext_iff] at H2)
    have h1 : σ = 1 := by
      have H3 : StrictMono.orderIsoOfSurjective σ hmono σ.surjective = OrderIso.refl _ := Subsingleton.elim _ _
      ext i
      have H4 := congrArg (fun f : Fin h ≃o Fin h => (f i : ℕ)) H3
      simpa using H4
    subst h1
    intro hd'
    exact prodIrr_equiv_of_eq rfl hd hd'

end PositivityTheory.PfEss.Zc2
