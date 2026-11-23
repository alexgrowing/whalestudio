import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section

namespace GlobalTheory.ProdLocInv

section Ops

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D)

def lOp (c : WO A S →₀ ℂ) (C : WO A S → WO S A' → ℂ) : WO A S → WO S A' → ℂ :=
  fun u v => comb ψ A S c (fun u' => C u' v) u

def rOp (c : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) : WO A S → WO S A' → ℂ :=
  fun u => comb ψ S A' c (C u)

theorem biComb_eq_lOp_rOp (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) :
    biComb ψ A S A' c c' C = lOp ψ A S A' c (rOp ψ A S A' c' C) := rfl

theorem lOp_rOp (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) :
    lOp ψ A S A' c (rOp ψ A S A' c' C) = rOp ψ A S A' c' (lOp ψ A S A' c C) := by
  funext u v
  simp only [lOp, rOp, comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem lOp_lOp (c d e : WO A S →₀ ℂ) (h : ∀ f, comb ψ A S e f = comb ψ A S c (comb ψ A S d f))
    (C : WO A S → WO S A' → ℂ) : lOp ψ A S A' c (lOp ψ A S A' d C) = lOp ψ A S A' e C := by
  funext u v
  exact congrFun (h fun u'' => C u'' v).symm u

theorem rOp_rOp (c d e : WO S A' →₀ ℂ) (h : ∀ f, comb ψ S A' e f = comb ψ S A' c (comb ψ S A' d f))
    (C : WO A S → WO S A' → ℂ) : rOp ψ A S A' c (rOp ψ A S A' d C) = rOp ψ A S A' e C := by
  funext u
  exact (h (C u)).symm

theorem lOp_comm (c d : WO A S →₀ ℂ) (h : ∀ f, comb ψ A S c (comb ψ A S d f) = comb ψ A S d (comb ψ A S c f))
    (C : WO A S → WO S A' → ℂ) : lOp ψ A S A' c (lOp ψ A S A' d C) = lOp ψ A S A' d (lOp ψ A S A' c C) := by
  funext u v
  exact congrFun (h fun u'' => C u'' v) u

theorem rOp_comm (c d : WO S A' →₀ ℂ) (h : ∀ f, comb ψ S A' c (comb ψ S A' d f) = comb ψ S A' d (comb ψ S A' c f))
    (C : WO A S → WO S A' → ℂ) : rOp ψ A S A' c (rOp ψ A S A' d C) = rOp ψ A S A' d (rOp ψ A S A' c C) := by
  funext u
  exact h (C u)

theorem biComb_comp (c d e : WO A S →₀ ℂ) (c' d' e' : WO S A' →₀ ℂ)
    (hl : ∀ f, comb ψ A S e f = comb ψ A S c (comb ψ A S d f))
    (hr : ∀ f, comb ψ S A' e' f = comb ψ S A' c' (comb ψ S A' d' f)) (C : WO A S → WO S A' → ℂ) :
    biComb ψ A S A' c c' (biComb ψ A S A' d d' C) = biComb ψ A S A' e e' C := by
  simp only [biComb_eq_lOp_rOp]
  rw [← lOp_rOp ψ A S A' d c', lOp_lOp ψ A S A' c d e hl, rOp_rOp ψ A S A' c' d' e' hr]

theorem biComb_comm (c d : WO A S →₀ ℂ) (c' d' : WO S A' →₀ ℂ)
    (hl : ∀ f, comb ψ A S c (comb ψ A S d f) = comb ψ A S d (comb ψ A S c f))
    (hr : ∀ f, comb ψ S A' c' (comb ψ S A' d' f) = comb ψ S A' d' (comb ψ S A' c' f)) (C : WO A S → WO S A' → ℂ) :
    biComb ψ A S A' c c' (biComb ψ A S A' d d' C) = biComb ψ A S A' d d' (biComb ψ A S A' c c' C) := by
  simp only [biComb_eq_lOp_rOp]
  rw [← lOp_rOp ψ A S A' d c', lOp_comm ψ A S A' c d hl, rOp_comm ψ A S A' c' d' hr, lOp_rOp ψ A S A' c d']

theorem comb_single_zero (T T' : HSp D) (f : WO T T' → ℂ) : comb ψ T T' (Finsupp.single 0 1) f = f := by
  classical
  funext w
  have h0 : symplOH T T' w 0 = 0 := by simp [symplOH, symplO, hO]
  simp [comb, heisO, h0]

end Ops

theorem comm_foldr {α ι : Type} (F : α → α) (H : ι → α → α) (l : List ι) (h : ∀ i ∈ l, ∀ x, F (H i x) = H i (F x))
    (x : α) : F (l.foldr H x) = l.foldr H (F x) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons]
    rw [h i (by simp), ih (fun j hj => h j (by simp [hj]))]

theorem foldr_mem {α ι : Type} (H : ι → α → α) (s : Set α) (l : List ι) (h : ∀ i ∈ l, ∀ x ∈ s, H i x ∈ s) (x : α)
    (hx : x ∈ s) : l.foldr H x ∈ s := by
  induction l with
  | nil => exact hx
  | cons i l ih => exact h i (by simp) _ (ih fun j hj => h j (by simp [hj]))

section Lists

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D)

theorem prodList {ι' : Type} (e₁ : ι' → WO A S →₀ ℂ) (e₂ : ι' → WO S A' →₀ ℂ) (l : List ι') :
    ∃ (e : WO A S →₀ ℂ) (e' : WO S A' →₀ ℂ),
      (∀ w ∈ e.support, w ∈ AddSubmonoid.closure (⋃ i ∈ l, ((e₁ i).support : Set (WO A S)))) ∧
      (∀ w ∈ e'.support, w ∈ AddSubmonoid.closure (⋃ i ∈ l, ((e₂ i).support : Set (WO S A')))) ∧
      ∀ C, biComb ψ A S A' e e' C = l.foldr (fun i C => biComb ψ A S A' (e₁ i) (e₂ i) C) C := by
  classical
  induction l with
  | nil =>
    refine ⟨Finsupp.single 0 1, Finsupp.single 0 1, ?_, ?_, fun C => ?_⟩
    · intro w hw
      rw [Finsupp.mem_support_single] at hw
      rw [hw.1]; exact zero_mem _
    · intro w hw
      rw [Finsupp.mem_support_single] at hw
      rw [hw.1]; exact zero_mem _
    · funext u v
      simp only [List.foldr_nil, biComb, comb_single_zero]
  | cons i l ih =>
    obtain ⟨e0, e0', hs, hs', hc⟩ := ih
    obtain ⟨c, hcs, hcf⟩ := (GlobalTheory.HeisComb.main D ψ A S).1 (e₁ i) e0
    obtain ⟨c', hcs', hcf'⟩ := (GlobalTheory.HeisComb.main D ψ S A').1 (e₂ i) e0'
    refine ⟨c, c', ?_, ?_, fun C => ?_⟩
    · intro w hw
      obtain ⟨x, hx, y, hy, rfl⟩ := hcs w hw
      refine add_mem (AddSubmonoid.subset_closure ?_) (AddSubmonoid.closure_mono ?_ (hs y hy))
      · simp only [Set.mem_iUnion]
        exact ⟨i, by simp, hx⟩
      · intro z hz
        simp only [Set.mem_iUnion] at hz ⊢
        obtain ⟨j, hj, hz⟩ := hz
        exact ⟨j, List.mem_cons_of_mem _ hj, hz⟩
    · intro w hw
      obtain ⟨x, hx, y, hy, rfl⟩ := hcs' w hw
      refine add_mem (AddSubmonoid.subset_closure ?_) (AddSubmonoid.closure_mono ?_ (hs' y hy))
      · simp only [Set.mem_iUnion]
        exact ⟨i, by simp, hx⟩
      · intro z hz
        simp only [Set.mem_iUnion] at hz ⊢
        obtain ⟨j, hj, hz⟩ := hz
        exact ⟨j, List.mem_cons_of_mem _ hj, hz⟩
    · rw [List.foldr_cons, ← hc]
      exact (biComb_comp ψ A S A' _ _ _ _ _ _ hcf hcf' C).symm

theorem keyList {ι' : Type} (e₁ g₁ : ι' → WO A S →₀ ℂ) (e₂ g₂ : ι' → WO S A' →₀ ℂ)
    (Cl Vl : ι' → Set (WO A S → WO S A' → ℂ)) (l : List ι') (hl : l.Nodup)
    (horth : ∀ i ∈ l, ∀ i' ∈ l, i ≠ i' → (∀ x, x ∈ (e₁ i).support ∨ x ∈ (g₁ i).support → ∀ y ∈ (e₁ i').support,
      symplO A S x y = 0) ∧ ∀ x, x ∈ (e₂ i).support ∨ x ∈ (g₂ i).support → ∀ y ∈ (e₂ i').support, symplO S A' x y = 0)
    (hloc : ∀ i ∈ l, ∀ C ∈ Cl i, biComb ψ A S A' (e₁ i) (e₂ i) C ∈ Vl i ∧
      C = biComb ψ A S A' (g₁ i) (g₂ i) (biComb ψ A S A' (e₁ i) (e₂ i) C))
    (hstab : ∀ i ∈ l, ∀ i' ∈ l, i ≠ i' → ∀ C ∈ Cl i, biComb ψ A S A' (e₁ i') (e₂ i') C ∈ Cl i)
    (C : WO A S → WO S A' → ℂ) (hC : ∀ i ∈ l, C ∈ Cl i) :
    (∀ i ∈ l, l.foldr (fun i C => biComb ψ A S A' (e₁ i) (e₂ i) C) C ∈ Vl i) ∧
      C = l.foldr (fun i C => biComb ψ A S A' (g₁ i) (g₂ i) C)
        (l.foldr (fun i C => biComb ψ A S A' (e₁ i) (e₂ i) C) C) := by
  induction l generalizing C with
  | nil => simp
  | cons i l ih =>
    rw [List.nodup_cons] at hl
    have ih' := ih hl.2 (fun a ha b hb hab => horth a (by simp [ha]) b (by simp [hb]) hab)
      (fun a ha => hloc a (by simp [ha])) (fun a ha b hb hab => hstab a (by simp [ha]) b (by simp [hb]) hab)
    have hne : ∀ j ∈ l, i ≠ j := fun j hj h => hl.1 (h ▸ hj)
    have hEE : ∀ j ∈ l, ∀ Y, biComb ψ A S A' (e₁ i) (e₂ i) (biComb ψ A S A' (e₁ j) (e₂ j) Y) =
        biComb ψ A S A' (e₁ j) (e₂ j) (biComb ψ A S A' (e₁ i) (e₂ i) Y) := by
      intro j hj Y
      obtain ⟨h1, h2⟩ := horth i (by simp) j (by simp [hj]) (hne j hj)
      exact biComb_comm ψ A S A' _ _ _ _
        ((GlobalTheory.HeisComb.main D ψ A S).2.1 _ _ fun x hx y hy => h1 x (Or.inl hx) y hy)
        ((GlobalTheory.HeisComb.main D ψ S A').2.1 _ _ fun x hx y hy => h2 x (Or.inl hx) y hy) Y
    have hGE : ∀ j ∈ l, ∀ Y, biComb ψ A S A' (e₁ i) (e₂ i) (biComb ψ A S A' (g₁ j) (g₂ j) Y) =
        biComb ψ A S A' (g₁ j) (g₂ j) (biComb ψ A S A' (e₁ i) (e₂ i) Y) := by
      intro j hj Y
      obtain ⟨h1, h2⟩ := horth j (by simp [hj]) i (by simp) (hne j hj).symm
      exact (biComb_comm ψ A S A' _ _ _ _
        ((GlobalTheory.HeisComb.main D ψ A S).2.1 (g₁ j) (e₁ i) fun x hx y hy => h1 x (Or.inr hx) y hy)
        ((GlobalTheory.HeisComb.main D ψ S A').2.1 (g₂ j) (e₂ i) fun x hx y hy => h2 x (Or.inr hx) y hy) Y).symm
    have hEL := comm_foldr (biComb ψ A S A' (e₁ i) (e₂ i)) (fun j C => biComb ψ A S A' (e₁ j) (e₂ j) C) l hEE
    have hGL := comm_foldr (biComb ψ A S A' (e₁ i) (e₂ i)) (fun j C => biComb ψ A S A' (g₁ j) (g₂ j) C) l hGE
    have hCi : C ∈ Cl i := hC i (by simp)
    have hstabL : l.foldr (fun j C => biComb ψ A S A' (e₁ j) (e₂ j) C) C ∈ Cl i :=
      foldr_mem _ (Cl i) l (fun j hj Y hY => hstab i (by simp) j (by simp [hj]) (hne j hj) Y hY) C hCi
    obtain ⟨-, ihC⟩ := ih' C (fun j hj => hC j (by simp [hj]))
    obtain ⟨ihV2, -⟩ := ih' (biComb ψ A S A' (e₁ i) (e₂ i) C)
      (fun j hj => hstab j (by simp [hj]) i (by simp) (hne j hj).symm C (hC j (by simp [hj])))
    refine ⟨fun j hj => ?_, ?_⟩
    · simp only [List.foldr_cons]
      rcases List.mem_cons.1 hj with h | hj
      · subst h
        exact (hloc _ (by simp) _ hstabL).1
      · rw [hEL]
        exact ihV2 j hj
    · simp only [List.foldr_cons]
      rw [← hGL, ← ihC]
      exact (hloc i (by simp) C hCi).2

end Lists

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (ι' P : Type) (l : List ι') (X : P → WO A S → WO S A' → ℂ) (e₁ g₁ : ι' → WO A S →₀ ℂ) (e₂ g₂ : ι' → WO S A' →₀ ℂ) (Cl Vl : ι' → Set (WO A S → WO S A' → ℂ)), l.Nodup → (∀ i ∈ l, ∀ i' ∈ l, i ≠ i' → (∀ x, x ∈ (e₁ i).support ∨ x ∈ (g₁ i).support → ∀ y ∈ (e₁ i').support, symplO A S x y = 0) ∧ ∀ x, x ∈ (e₂ i).support ∨ x ∈ (g₂ i).support → ∀ y ∈ (e₂ i').support, symplO S A' x y = 0) → (∀ i ∈ l, ∀ p, X p ∈ Cl i) → (∀ i ∈ l, ∀ C ∈ Cl i, biComb ψ A S A' (e₁ i) (e₂ i) C ∈ Vl i ∧ C = biComb ψ A S A' (g₁ i) (g₂ i) (biComb ψ A S A' (e₁ i) (e₂ i) C)) → (∀ i ∈ l, ∀ i' ∈ l, i ≠ i' → ∀ C ∈ Cl i, biComb ψ A S A' (e₁ i') (e₂ i') C ∈ Cl i) → ∃ (e : WO A S →₀ ℂ) (e' : WO S A' →₀ ℂ), (∀ w ∈ e.support, w ∈ AddSubmonoid.closure (⋃ i ∈ l, ((e₁ i).support : Set (WO A S)))) ∧ (∀ w ∈ e'.support, w ∈ AddSubmonoid.closure (⋃ i ∈ l, ((e₂ i).support : Set (WO S A')))) ∧ ∀ p, (∀ i ∈ l, biComb ψ A S A' e e' (X p) ∈ Vl i) ∧ X p = l.foldr (fun i C => biComb ψ A S A' (g₁ i) (g₂ i) C) (biComb ψ A S A' e e' (X p)) := by
  intro D ψ A S A' ι' P l X e₁ g₁ e₂ g₂ Cl Vl hl horth hX hloc hstab
  obtain ⟨e, e', hs, hs', hc⟩ := prodList ψ A S A' e₁ e₂ l
  refine ⟨e, e', hs, hs', fun p => ?_⟩
  rw [hc]
  exact keyList ψ A S A' e₁ g₁ e₂ g₂ Cl Vl l hl horth hloc hstab (X p) fun i hi => hX i hi p

end GlobalTheory.ProdLocInv
