import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.CechDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeCech

variable {R : Type} [CommRing R] {D : Type 1} [Category.{0} D] (A : D ⥤ CommAlgCat.{0} R)

abbrev Co (k : ℕ) : Type 1 := CH.Cn (CH.modF A) k

def one0 : Co A 0 := fun s => (1 : A.obj (s.obj (Fin.last 0)))

def aL : ∀ {p : ℕ}, (Fin (p + 1) → Co A 1) → Co A p := fun {p} =>
  Nat.rec (motive := fun p => (Fin (p + 1) → Co A 1) → Co A p) (fun _ => one0 A)
    (fun p ih β => (CH.mulP A).cupC (by omega : 1 + p = p + 1) (β 0 - β 1) (ih fun i => β i.succ)) p

theorem aL_succ {p : ℕ} (β : Fin (p + 2) → Co A 1) :
    aL A β = (CH.mulP A).cupC (by omega : 1 + p = p + 1) (β 0 - β 1) (aL A fun i => β i.succ) := rfl

theorem cupList_left {k : ℕ} (l : Fin (k + 1) → Co A 1) :
    cupListC A l = (CH.mulP A).cupC (by omega : 1 + k = k + 1) (l 0) (cupListC A fun i => l i.succ) := by
  induction k with
  | zero =>
    have e1 : cupListC A l = (CH.mulP A).cupC (Nat.zero_add 1) (one0 A) (l (Fin.last 0)) := rfl
    have e2 : (cupListC A fun i : Fin 0 => l i.succ) = one0 A := rfl
    rw [e1, e2]
    exact (Auxff.unit_left A _).trans (Auxff.unit_right A _).symm
  | succ k ih =>
    have e1 : cupListC A l = (CH.mulP A).cupC (by omega : k + 1 + 1 = k + 1 + 1)
      (cupListC A fun i : Fin (k + 1) => l i.castSucc) (l (Fin.last (k + 1))) := rfl
    have e2 : (cupListC A fun i : Fin (k + 1) => l i.succ) = (CH.mulP A).cupC (by omega : k + 1 = k + 1)
      (cupListC A fun i : Fin k => l i.castSucc.succ) (l (Fin.last k).succ) := rfl
    rw [e1, e2, ih (fun i => l i.castSucc)]
    exact Auxff.assoc A _ _ (by omega : k + 1 = k + 1) (by omega) _ _ _

theorem aL_eq {p : ℕ} (β : Fin (p + 1) → Co A 1) : aL A β = cupListC A fun k : Fin p => β k.castSucc - β k.succ := by
  induction p with
  | zero => rfl
  | succ p ih =>
    rw [aL_succ, ih, cupList_left]
    rfl

theorem cech_d_one_zero : CH.d (CH.modF A) 0 (one0 A) = 0 := by
  funext s
  change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (A.map (GlobalTheory.CatH.toLast i s)).hom 1 = (0 : A.obj _)
  rw [Fin.sum_univ_two, map_one, map_one]
  simp

theorem aL_closed {p : ℕ} (β : Fin (p + 1) → Co A 1) (hβ : ∀ i j, CH.d _ 1 (β i) = CH.d _ 1 (β j)) :
    CH.d _ p (aL A β) = 0 := by
  induction p with
  | zero => exact cech_d_one_zero A
  | succ p ih =>
    rw [aL_succ, P.leibniz, ih _ fun i j => hβ _ _, map_sub, hβ 0 1, sub_self]
    simp

theorem pow_closed (z : Co A 2) (hz : CH.d _ 2 z = 0) (k : ℕ) : CH.d _ (2 * k) (cupPowC A z k) = 0 := by
  induction k with
  | zero => exact cech_d_one_zero A
  | succ k ih =>
    have e : cupPowC A z (k + 1) = (CH.mulP A).cupC (by omega) (cupPowC A z k) z := rfl
    rw [e, P.leibniz, ih, hz]
    simp

theorem aL_cocycle {p : ℕ} (β : Fin (p + 2) → Co A 1) :
    ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) • aL A (β ∘ j.succAbove) = 0 := by
  induction p with
  | zero =>
    rw [Fin.sum_univ_two]
    have e : ∀ γ : Fin 1 → Co A 1, aL A γ = one0 A := fun _ => rfl
    rw [e, e]
    simp
  | succ p ih =>
    have ih' := ih fun i => β i.succ
    rw [Fin.sum_univ_succ] at ih'
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    have e0 : β ∘ (0 : Fin (p + 3)).succAbove = fun i => β i.succ := by
      funext i; simp
    have e1 : aL A (β ∘ (Fin.succ 0 : Fin (p + 3)).succAbove) = (CH.mulP A).cupC (by omega : 1 + p = p + 1) (β 0 - β 2)
        (aL A ((fun i => β i.succ) ∘ (0 : Fin (p + 2)).succAbove)) := by
      rw [aL_succ]
      refine congrArg₂ (fun x y => (CH.mulP A).cupC (by omega : 1 + p = p + 1) x y) ?_ (congrArg _ ?_)
      · simp only [Function.comp]
        congr 2
      · funext i
        simp only [Function.comp]
        congr 1
    have e2 : ∀ j : Fin (p + 1), aL A (β ∘ (Fin.succ (Fin.succ j)).succAbove) = (CH.mulP A).cupC (by omega : 1 + p = p + 1) (β 0 - β 1)
        (aL A ((fun i => β i.succ) ∘ (Fin.succ j).succAbove)) := by
      intro j
      rw [aL_succ]
      refine congrArg₂ (fun x y => (CH.mulP A).cupC (by omega : 1 + p = p + 1) x y) ?_ (congrArg _ ?_)
      · simp only [Function.comp]
        congr 2
      · funext i
        simp only [Function.comp]
        exact congrArg β (Fin.succ_succAbove_succ _ _)
    have e3 : aL A (fun i => β i.succ) = (CH.mulP A).cupC (by omega : 1 + p = p + 1) (β 1 - β 2)
        (aL A ((fun i => β i.succ) ∘ (0 : Fin (p + 2)).succAbove)) := by
      rw [aL_succ]
      refine congrArg₂ (fun x y => (CH.mulP A).cupC (by omega : 1 + p = p + 1) x y) rfl (congrArg _ ?_)
      funext i
      simp
    simp only [e2]
    rw [e0, e1, e3]
    generalize aL A ((fun i => β i.succ) ∘ (0 : Fin (p + 2)).succAbove) = B at ih' ⊢
    generalize hM : (CH.mulP A).cupC (by omega : 1 + p = p + 1) = M
    have h1 : ∑ i : Fin (p + 1), (-1 : ℤ) ^ ((Fin.succ i : Fin (p + 2)) : ℕ) • aL A ((fun i => β i.succ) ∘ (Fin.succ i).succAbove) = -B := by
      refine eq_neg_of_add_eq_zero_right ?_
      simpa using ih'
    have h2 : ∑ j : Fin (p + 1), (-1 : ℤ) ^ ((Fin.succ (Fin.succ j) : Fin (p + 3)) : ℕ) • M (β 0 - β 1) (aL A ((fun i => β i.succ) ∘ (Fin.succ j).succAbove)) =
        M (β 0 - β 1) B := by
      rw [← neg_neg B, ← h1, map_neg, map_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, ← neg_smul]
      congr 1
      simp [Fin.val_succ, pow_succ]
    rw [h2]
    simp only [map_sub, LinearMap.sub_apply, Fin.val_zero, Fin.val_succ, pow_zero, one_smul, zero_add, pow_one, neg_smul]
    abel

theorem aL_E {p : ℕ} (β : Fin (p + 2) → Co A 1) :
    ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) • (CH.mulP A).cupC (by omega : 1 + p = p + 1) (β (j.succAbove 0)) (aL A (β ∘ j.succAbove)) =
      - aL A β := by
  have h0 := aL_cocycle A β
  rw [Fin.sum_univ_succ] at h0
  rw [Fin.sum_univ_succ]
  have e0 : β ∘ (0 : Fin (p + 2)).succAbove = fun i => β i.succ := by
    funext i; simp
  rw [e0] at h0 ⊢
  generalize hM : (CH.mulP A).cupC (by omega : 1 + p = p + 1) = M
  have h1 : ∑ i : Fin (p + 1), (-1 : ℤ) ^ ((Fin.succ i : Fin (p + 2)) : ℕ) • aL A (β ∘ (Fin.succ i).succAbove) = -aL A fun i => β i.succ := by
    refine eq_neg_of_add_eq_zero_right ?_
    simpa using h0
  have h2 : ∑ j : Fin (p + 1), (-1 : ℤ) ^ ((Fin.succ j : Fin (p + 2)) : ℕ) • M (β ((Fin.succ j).succAbove 0)) (aL A (β ∘ (Fin.succ j).succAbove)) =
      - M (β 0) (aL A fun i => β i.succ) := by
    rw [← map_neg, ← h1, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, Fin.succ_succAbove_zero]
  rw [h2, aL_succ, hM]
  simp only [map_sub, LinearMap.sub_apply, Fin.val_zero, pow_zero, one_smul, Fin.zero_succAbove]
  have : (Fin.succ 0 : Fin (p + 2)) = 1 := rfl
  rw [this]
  abel

def fP (z : Co A 2) {p : ℕ} (β : Fin (p + 1) → Co A 1) (k q : ℕ) (h : 2 * k + (p + 1) = q) : Co A q :=
  (CH.mulP A).cupC h (cupPowC A z k) ((CH.mulP A).cupC (by omega : 1 + p = p + 1) (β 0) (aL A β))

def gP (z : Co A 2) {p : ℕ} (β : Fin (p + 1) → Co A 1) (k q : ℕ) (h : 2 * k + p = q) : Co A q :=
  (CH.mulP A).cupC h (cupPowC A z k) (aL A β)

theorem d_fP (z : Co A 2) (hz : CH.d _ 2 z = 0) {p : ℕ} (β : Fin (p + 1) → Co A 1) (hβ : ∀ i, CH.d _ 1 (β i) = z)
    (k q : ℕ) (h : 2 * k + (p + 1) = q) : CH.d _ q (fP A z β k q h) = gP A z β (k + 1) (q + 1) (by omega) := by
  unfold fP gP
  rw [P.leibniz, pow_closed A z hz, P.leibniz, aL_closed A β (fun i j => by rw [hβ, hβ]), hβ, pow_mul]
  simp only [map_zero, LinearMap.zero_apply, smul_zero, add_zero, zero_add, neg_one_sq, one_pow, one_smul]
  exact (Auxff.assoc A _ _ _ _ _ _ _).symm

theorem sum_fP (z : Co A 2) {p : ℕ} (β : Fin (p + 2) → Co A 1) (k q : ℕ) (h : 2 * k + (p + 1) = q) :
    ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) • fP A z (β ∘ j.succAbove) k q h = - gP A z β k q h := by
  unfold fP gP
  rw [← map_neg, ← aL_E, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]
  rfl

section Res

variable {C : Type 1} [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R) {U V : ObjectProperty C}

def resM (h : V ≤ U) : CH.Mor (CH.modF (U.ι ⋙ A)) (CH.modF (V.ι ⋙ A)) (RingHom.id R) where
  G := ObjectProperty.ιOfLE h
  τ _ := LinearMap.id
  nat _ _ := rfl

theorem d_resB (h : V ≤ U) {k : ℕ} (b : CH.Cn (CH.modF (U.ι ⋙ A)) k) :
    CH.d _ k (resB A h b) = resB A h (CH.d _ k b) := (resM A h).d_pullC k b

theorem resB_cup (h : V ≤ U) {p q n : ℕ} (e : p + q = n) (a : CH.Cn (CH.modF (U.ι ⋙ A)) p) (b : CH.Cn (CH.modF (U.ι ⋙ A)) q) :
    resB A h ((CH.mulP _).cupC e a b) = (CH.mulP _).cupC e (resB A h a) (resB A h b) := by
  funext s
  rw [Auxff.cupC_apply]
  exact congrArg₂ (fun x y => (CH.mulP _).μ _ x y) (Auxff.term_pull (resM A h) s a _ _) (Auxff.term_pull (resM A h) s b _ _)

theorem resB_sub (h : V ≤ U) {k : ℕ} (a b : CH.Cn (CH.modF (U.ι ⋙ A)) k) :
    resB A h (a - b) = resB A h a - resB A h b := rfl

theorem resB_pow (h : V ≤ U) (z : Co (U.ι ⋙ A) 2) (k : ℕ) :
    resB A h (cupPowC (U.ι ⋙ A) z k) = cupPowC (V.ι ⋙ A) (resB A h z) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have e : cupPowC (U.ι ⋙ A) z (k + 1) = (CH.mulP _).cupC (by omega) (cupPowC (U.ι ⋙ A) z k) z := rfl
    rw [e, resB_cup, ih]
    rfl

theorem resB_aL (h : V ≤ U) {p : ℕ} (β : Fin (p + 1) → Co (U.ι ⋙ A) 1) :
    resB A h (aL (U.ι ⋙ A) β) = aL (V.ι ⋙ A) fun i => resB A h (β i) := by
  induction p with
  | zero => rfl
  | succ p ih =>
    rw [aL_succ, resB_cup, ih, resB_sub, aL_succ]

theorem resB_fP (h : V ≤ U) (z : Co (U.ι ⋙ A) 2) {p : ℕ} (β : Fin (p + 1) → Co (U.ι ⋙ A) 1) (k q : ℕ)
    (e : 2 * k + (p + 1) = q) :
    resB A h (fP (U.ι ⋙ A) z β k q e) = fP (V.ι ⋙ A) (resB A h z) (fun i => resB A h (β i)) k q e := by
  unfold fP
  rw [resB_cup, resB_cup, resB_pow, resB_aL]

theorem resB_resB {T : ObjectProperty C} (h : V ≤ U) (h' : T ≤ V) (h'' : T ≤ U) {k : ℕ} (b : CH.Cn (CH.modF (U.ι ⋙ A)) k) :
    resB A h' (resB A h b) = resB A h'' b := rfl

end Res

end GlobalTheory.CompanionTheory.ConeCech
