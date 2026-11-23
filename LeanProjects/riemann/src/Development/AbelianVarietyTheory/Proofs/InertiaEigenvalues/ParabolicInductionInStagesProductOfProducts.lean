import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MultiProdCompCongr
import BuildAid.D3

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.ProdReorder

namespace GlobalTheory.ProdFlatten

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

structure BR (k : Type) [Field k] (n : ℕ) : Type 1 where

  V : Type
  [ac : AddCommGroup V]
  [smul : Module ℂ V]

  ρ : Representation ℂ (GL (Fin n) k) V

attribute [instance] BR.ac BR.smul

def one (w : IrrGL k) : BR k w.1 := ⟨_, w.rep⟩

def two {r t N : ℕ} (e : r + t = N) (A : BR k r) (C : BR k t) : BR k N :=
  ⟨_, ind₂ (stdSum e) (extTensor A.ρ C.ρ)⟩

def mp {d M : ℕ} (N : Fin d → ℕ) (hM : ∑ i, N i = M) (A : ∀ i, BR k (N i)) : BR k M :=
  ⟨_, multiProd (stdBlocks N hM) fun i => (A i).ρ⟩

def pr {a N : ℕ} (x : Fin a → IrrGL k) (hx : ∑ i, (x i).1 = N) : BR k N :=
  mp (fun i => (x i).1) hx fun i => one (x i)

def Iso {n : ℕ} (A C : BR k n) : Prop := Nonempty (A.ρ.Equiv C.ρ)

def Sm {n : ℕ} (A : BR k n) : Prop := IsSmooth A.ρ

theorem iso_refl {n : ℕ} (A : BR k n) : Iso A A := eqv_refl A.ρ

theorem iso_symm {n : ℕ} {A C : BR k n} (h : Iso A C) : Iso C A := eqv_symm (ρ := A.ρ) (σ := C.ρ) h

theorem iso_trans {n : ℕ} {A C D : BR k n} (h : Iso A C) (h' : Iso C D) : Iso A D :=
  eqv_trans (ρ := A.ρ) (σ := C.ρ) (τ := D.ρ) h h'

theorem sm_one (w : IrrGL k) : Sm (one w) := w.2.rep.smooth

theorem sm_pr {a N : ℕ} (x : Fin a → IrrGL k) (hx : ∑ i, (x i).1 = N) : Sm (pr x hx) := isSmooth_prodIrr x hx

theorem two_congr {r t N : ℕ} (e : r + t = N) {A A' : BR k r} {C C' : BR k t} (h : Iso A A') (h' : Iso C C') :
    Iso (two e A C) (two e A' C') :=
  ind₂_congr e (π₁ := A.ρ) (σ₁ := A'.ρ) (π₂ := C.ρ) (σ₂ := C'.ρ) h h'

theorem two_assoc {r s t M M' N : ℕ} (h₁ : r + s = M) (h₂ : M + t = N) (h₃ : s + t = M') (h₄ : r + M' = N)
    (A : BR k r) (C : BR k s) (D : BR k t) (s₁ : Sm A) (s₂ : Sm C) (s₃ : Sm D) :
    Iso (two h₂ (two h₁ A C) D) (two h₄ A (two h₃ C D)) :=
  ind₂_assoc' h₁ h₂ h₃ h₄ A.ρ C.ρ D.ρ s₁ s₂ s₃

theorem mp_head {d T M : ℕ} (N : Fin (d + 1) → ℕ) (hM : ∑ i, N i = M) (A : ∀ i, BR k (N i))
    (hT : ∑ i : Fin d, N i.succ = T) (e : N 0 + T = M) :
    Iso (mp N hM A) (two e (A 0) (mp (fun i : Fin d => N i.succ) hT fun i => A i.succ)) :=
  multiProd_head (d := N) (X := fun i => (A i).V) (fun i => (A i).ρ) (stdBlocks N hM) e
    (stdBlocks (fun i : Fin d => N i.succ) hT)

theorem mp_empty {M : ℕ} (N N' : Fin 0 → ℕ) (hM : ∑ i, N i = M) (hM' : ∑ i, N' i = M) (A : ∀ i, BR k (N i))
    (A' : ∀ i, BR k (N' i)) : Iso (mp N hM A) (mp N' hM' A') :=
  multiProd_empty (d := N) (d' := N') (X := fun i => (A i).V) (X' := fun i => (A' i).V) (fun i => (A i).ρ)
    (fun i => (A' i).ρ) (stdBlocks N hM) (stdBlocks N' hM')

theorem two_unit {r t : ℕ} (e : r + t = r) (A : BR k r) (hA : Sm A) (N : Fin 0 → ℕ) (hN : ∑ i, N i = t)
    (C : ∀ i, BR k (N i)) : Iso (two e A (mp N hN C)) A :=
  ind₂_unit_right e A.ρ hA (d := N) (X := fun i => (C i).V) (fun i => (C i).ρ) (stdBlocks N hN)

theorem two_unit_pr {r t : ℕ} (e : r + t = r) (A : BR k r) (hA : Sm A) (y : Fin 0 → IrrGL k)
    (hy : ∑ i, (y i).1 = t) : Iso (two e A (pr y hy)) A :=
  two_unit e A hA _ hy _

theorem mp_empty_pr {M : ℕ} (N : Fin 0 → ℕ) (hM : ∑ i, N i = M) (A : ∀ i, BR k (N i)) (y : Fin 0 → IrrGL k)
    (hy : ∑ i, (y i).1 = M) : Iso (mp N hM A) (pr y hy) :=
  mp_empty N _ hM hy A _

theorem pr_succ {a t N : ℕ} (z : Fin (a + 1) → IrrGL k)
    (hx : ∑ i : Fin a, (z i.succ).1 = t) (hz : ∑ i, (z i).1 = N) (e : (z 0).1 + t = N) :
    Iso (pr z hz) (two e (one (z 0)) (pr (fun i : Fin a => z i.succ) hx)) :=
  mp_head (fun i => (z i).1) hz (fun i => one (z i)) hx e

theorem of_iso {d h : ℕ} (y : Fin d → Fin h → IrrGL k) (N : Fin d → ℕ) {M c : ℕ} (hN : ∀ i, ∑ j, (y i j).1 = N i)
    (hM : ∑ i, N i = M) (z : Fin c → IrrGL k) (hz : ∑ p, (z p).1 = M)
    (H : Iso (mp N hM fun i => pr (y i) (hN i)) (pr z hz)) :
    Nonempty ((multiProd (stdBlocks N hM) fun i => prodIrr (y i) (hN i)).Equiv (prodIrr z hz)) := H

attribute [irreducible] one two mp pr Iso Sm

theorem pr_congr {a b N : ℕ} {x : Fin a → IrrGL k} {z : Fin b → IrrGL k} (h : List.ofFn x = List.ofFn z)
    (hx : ∑ i, (x i).1 = N) (hz : ∑ i, (z i).1 = N) : Iso (pr x hx) (pr z hz) := by
  obtain rfl : a = b := by simpa using congrArg List.length h
  obtain rfl := List.ofFn_injective h
  exact iso_refl _

theorem pr_cons {a b t N : ℕ} {w : IrrGL k} {x : Fin a → IrrGL k} {z : Fin b → IrrGL k}
    (h : List.ofFn z = w :: List.ofFn x) (hx : ∑ i, (x i).1 = t) (hz : ∑ i, (z i).1 = N) (e : w.1 + t = N) :
    Iso (pr z hz) (two e (one w) (pr x hx)) := by
  have hb : b = a + 1 := by simpa using congrArg List.length h
  subst hb
  have h' : z 0 :: List.ofFn (fun i : Fin a => z i.succ) = w :: List.ofFn x := List.ofFn_succ.symm.trans h
  have h₁ : z 0 = w := (List.cons.inj h').1
  have h₂ : (fun i : Fin a => z i.succ) = x := List.ofFn_injective (List.cons.inj h').2
  subst h₁ h₂
  exact pr_succ z hx hz e

theorem pr_append {a : ℕ} : ∀ {b c r t N : ℕ} (x : Fin a → IrrGL k) (y : Fin b → IrrGL k) (z : Fin c → IrrGL k)
    (_ : List.ofFn z = List.ofFn x ++ List.ofFn y) (_ : a ≠ 0 ∨ b = 0) (hx : ∑ i, (x i).1 = r)
    (hy : ∑ i, (y i).1 = t) (hz : ∑ i, (z i).1 = N) (e : r + t = N),
    Iso (pr z hz) (two e (pr x hx) (pr y hy)) := by
  induction a with
  | zero =>
    intro b c r t N x y z h hab hx hy hz e
    obtain rfl : b = 0 := by simpa using hab
    obtain rfl : t = 0 := by simpa using hy.symm
    have e0 : N = r := e.symm
    subst e0
    exact iso_trans (pr_congr (by simpa using h) hz hx) (iso_symm (two_unit_pr e _ (sm_pr x hx) y hy))
  | succ a ih =>
    intro b c r t N x y z h _ hx hy hz e
    have hx' : List.ofFn x = x 0 :: List.ofFn fun i : Fin a => x i.succ := List.ofFn_succ
    have hs : (x 0).1 + ∑ i : Fin a, (x i.succ).1 = r := (Fin.sum_univ_succ fun i => (x i).1).symm.trans hx
    have A := pr_cons hx' rfl hx hs
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · obtain rfl : (x 0).1 = r := by simpa using hs
      have B := iso_trans A (two_unit_pr hs _ (sm_one (x 0)) (fun i : Fin 0 => x i.succ) rfl)
      refine iso_trans (pr_cons (w := x 0) (by simpa using h) hy hz e) ?_
      exact two_congr e (iso_symm B) (iso_refl _)
    · let L := (List.ofFn fun i : Fin a => x i.succ) ++ List.ofFn y
      have hL : List.ofFn L.get = L := List.ofFn_get L
      have hT : ∑ i, (L.get i).1 = ∑ i : Fin a, (x i.succ).1 + t := by
        have := congrArg (fun l : List (IrrGL k) => (l.map Sigma.fst).sum) hL
        simp only [L, List.map_append, List.sum_append, List.map_ofFn, List.sum_ofFn, Function.comp_def] at this
        rw [← hy]
        exact this
      have e' : (x 0).1 + (∑ i : Fin a, (x i.succ).1 + t) = N := by omega
      have B := pr_cons (w := x 0) (z := z) (x := L.get) (by rw [h, hx', hL]; rfl) hT hz e'
      have C := ih (fun i => x i.succ) y L.get hL (Or.inl ha.ne') rfl hy hT rfl
      have D := two_assoc hs e rfl e' (one (x 0)) (pr (fun i : Fin a => x i.succ) rfl) (pr y hy)
        (sm_one _) (sm_pr _ _) (sm_pr _ _)
      exact iso_trans B (iso_trans (two_congr e' (iso_refl _) C) (iso_trans (iso_symm D)
        (two_congr e (iso_symm A) (iso_refl _))))

theorem ofFn_lex {α : Type*} {d h : ℕ} (y : Fin d → Fin h → α) :
    List.ofFn (fun p : Fin (d * h) => y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2) =
      (List.ofFn fun i => List.ofFn (y i)).flatten := by
  rw [List.ofFn_mul]
  refine congrArg List.flatten (congrArg List.ofFn (funext fun i => congrArg List.ofFn (funext fun j => ?_)))
  have key : ∀ p : Fin (d * h), p = finProdFinEquiv (i, j) →
      y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2 = y i j := by
    rintro _ rfl
    rw [Equiv.symm_apply_apply]
  exact key _ (Fin.ext (by simp; ring))

theorem mp_pr_iso {h : ℕ} (d : ℕ) : ∀ (y : Fin d → Fin h → IrrGL k) (N : Fin d → ℕ) (M : ℕ)
    (hN : ∀ i, ∑ j, (y i j).1 = N i) (hM : ∑ i, N i = M)
    (hM' : ∑ p : Fin (d * h), (y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).1 = M),
    Iso (mp N hM fun i => pr (y i) (hN i))
      (pr (fun p => y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2) hM') := by
  induction d with
  | zero =>
    intro y N M hN hM hM'
    obtain rfl : M = 0 := by simpa using hM.symm
    let z : Fin 0 → IrrGL k := fun i => i.elim0
    have hz : ∑ i, (z i).1 = 0 := by simp
    exact iso_trans (mp_empty_pr N hM _ z hz) (pr_congr (x := z) (by rw [ofFn_lex]; simp) hz hM')
  | succ d ih =>
    intro y N M hN hM hM'
    have e : N 0 + ∑ i : Fin d, N i.succ = M := (Fin.sum_univ_succ N).symm.trans hM
    have hT : ∑ p : Fin (d * h), (y (finProdFinEquiv.symm p).1.succ (finProdFinEquiv.symm p).2).1 =
        ∑ i : Fin d, N i.succ := by
      rw [Equiv.sum_comp finProdFinEquiv.symm fun q : Fin d × Fin h => (y q.1.succ q.2).1, Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun i _ => hN _
    have A := mp_head N hM (fun i => pr (y i) (hN i)) rfl e
    have B := ih (fun i => y i.succ) (fun i => N i.succ) _ (fun i => hN _) rfl hT
    have C := pr_append (y 0) _ _
      (by rw [ofFn_lex y, ofFn_lex fun i : Fin d => y i.succ, List.ofFn_succ, List.flatten_cons])
      (by rcases Nat.eq_zero_or_pos h with rfl | hh; exacts [Or.inr rfl, Or.inl hh.ne']) (hN 0) hT hM' e
    exact iso_trans A (iso_trans (two_congr e (iso_refl _) B) (iso_symm C))

theorem multiProd_prodIrr_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (d h : ℕ) (y : Fin d → Fin h → IrrGL k) (N : Fin d → ℕ) (M : ℕ) (hN : ∀ i, ∑ j, (y i j).1 = N i)
    (hM : ∑ i, N i = M)
    (hM' : ∑ p : Fin (d * h), (y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).1 = M),
    Nonempty ((multiProd (stdBlocks N hM) fun i => prodIrr (y i) (hN i)).Equiv
      (prodIrr (fun p => y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2) hM')) :=
  fun _ _ _ _ _ d _ y N M hN hM hM' => of_iso y N hN hM _ hM' (mp_pr_iso d y N M hN hM hM')

end GlobalTheory.ProdFlatten
