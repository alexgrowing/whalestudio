import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.Interface

noncomputable section
open scoped BigOperators
open Classical

namespace GlobalTheory.RowValueCheck

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds

variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]

def emptyValue [NeZero d] (X : RowData C V d I J) (ν : WithTop ℝ) : RowValue X where
  nu := ν
  FF := fun _ => ∅
  VAL := fun _ _ h => absurd h (Set.notMem_empty _)

theorem exists_value_top [NeZero d] (X : RowData C V d I J) : ∃ Y : RowValue X, Y.nu = ⊤ :=
  ⟨emptyValue X ⊤, rfl⟩

theorem no_equal_types (G : ∀ g, Cart V d (I g) (J g)) (alt : Prop) {N : ℕ}
    (P : MvPolynomial (Fin N × WV I) C) (kind : Fin N → Option (Fin 2 × ZMod d × ZMod d))
    (h : RowsOK G alt P kind) (ρ : Fin N) (μ μ' : Fin N × WV I →₀ ℕ) (hμ : μ ∈ P.support)
    (hμ' : μ' ∈ P.support) (w w' : WV I) (hw : μ (ρ, w) ≠ 0) (hw' : μ' (ρ, w') ≠ 0)
    (hne : w.1 ≠ w'.1) : alt ∧ tyW G w ≠ tyW G w' := by
  rcases hk : kind ρ with _ | ⟨g, a, a'⟩
  · obtain ⟨g, hg⟩ := h.2 ρ hk
    exact absurd ((hg μ hμ w hw).trans (hg μ' hμ' w' hw').symm) hne
  · obtain ⟨ha, ho, hl⟩ := h.1 ρ g a a' hk
    have hab : a ≠ a' := by
      rintro rfl
      simp at ho
    refine ⟨ha, ?_⟩
    rcases hl μ hμ w hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hl μ' hμ' w' hw' with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact absurd (h1.trans h3.symm) hne
    · rw [h2, h4]; exact hab
    · rw [h2, h4]; exact hab.symm
    · exact absurd (h1.trans h3.symm) hne

def Agree {σ : Type} (S : Set σ) (F F' : MvPowerSeries σ C) : Prop :=
  ∀ μ : σ →₀ ℕ, (∀ x, μ x ≠ 0 → x ∈ S) → MvPowerSeries.coeff μ F = MvPowerSeries.coeff μ F'

theorem Agree.mul {σ : Type} {S : Set σ} {F F' K K' : MvPowerSeries σ C} (h : Agree S F F')
    (h' : Agree S K K') : Agree S (F * K) (F' * K') := by
  intro μ hμ
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have e : p.1 + p.2 = μ := by simpa using hp
  rw [h p.1 fun x hx => hμ x (by rw [← e]; simp; omega),
    h' p.2 fun x hx => hμ x (by rw [← e]; simp; omega)]

theorem Agree.pow {σ : Type} {S : Set σ} {F F' : MvPowerSeries σ C} (h : Agree S F F') (k : ℕ) :
    Agree S (F ^ k) (F' ^ k) := by
  induction k with
  | zero => intro μ _; simp
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul h

theorem Agree.exp {σ : Type} {S : Set σ} {F F' : MvPowerSeries σ C} (h : Agree S F F') :
    Agree S (mvExp F) (mvExp F') := by
  intro μ hμ
  show (∑ k ∈ Finset.range (μ.degree + 1), MvPowerSeries.coeff μ (F ^ k) / (k.factorial : C)) =
    ∑ k ∈ Finset.range (μ.degree + 1), MvPowerSeries.coeff μ (F' ^ k) / (k.factorial : C)
  exact Finset.sum_congr rfl fun k _ => by rw [h.pow k μ hμ]

theorem Agree.prod {σ α : Type} {S : Set σ} (s : Finset α) {F F' : α → MvPowerSeries σ C}
    (h : ∀ i, Agree S (F i) (F' i)) : Agree S (∏ i ∈ s, F i) (∏ i ∈ s, F' i) := by
  induction s using Finset.induction_on with
  | empty => intro μ _; simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha]; exact (h a).mul ih

theorem agree_rowCopy {N : ℕ} (S : Set (Fin N × WV I)) (ρ : Fin N) (F F' : MvPowerSeries (WV I) C)
    (h : Agree {w | (ρ, w) ∈ S} F F') : Agree S (rowCopy ρ F) (rowCopy ρ F') := by
  intro μ hμ
  have hs : MvPowerSeries.HasSubst
      (fun w : WV I => (MvPowerSeries.X (ρ, w) : MvPowerSeries (Fin N × WV I) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (by simp)
  unfold rowCopy
  rw [MvPowerSeries.coeff_subst hs, MvPowerSeries.coeff_subst hs]
  refine finsum_congr fun e => ?_
  by_cases he : ∀ x, e x ≠ 0 → (ρ, x) ∈ S
  · rw [h e he]
  · push Not at he
    obtain ⟨x, hx, hxS⟩ := he
    have h0 : μ (ρ, x) = 0 := by
      by_contra h1
      exact hxS (hμ _ h1)
    have hd : (MvPowerSeries.X (ρ, x) : MvPowerSeries (Fin N × WV I) C) ∣
        e.prod fun s k => (MvPowerSeries.X (ρ, s) : MvPowerSeries (Fin N × WV I) C) ^ k :=
      (dvd_pow_self _ hx).trans (Finset.dvd_prod_of_mem
        (fun s => (MvPowerSeries.X (ρ, s) : MvPowerSeries (Fin N × WV I) C) ^ e s)
        (Finsupp.mem_support_iff.2 hx))
    rw [MvPowerSeries.X_dvd_iff.1 hd μ h0]
    simp

def hOf (hL : Fin 2 → ZMod d → ZMod d → MvPowerSeries (WV I) C) :
    Option (Fin 2 × ZMod d × ZMod d) → MvPowerSeries (WV I) C
  | some (g, a, a') => hL g a a'
  | none => 0

theorem valOf_eq (hL : Fin 2 → ZMod d → ZMod d → MvPowerSeries (WV I) C) {N : ℕ}
    (P : MvPolynomial (Fin N × WV I) C) (kind : Fin N → Option (Fin 2 × ZMod d × ZMod d))
    (gr : Fin N → MvPowerSeries (WV I) C) :
    ValOf hL P kind gr =
      jetAt0 P (∏ ρ, (rowCopy ρ (gr ρ) * mvExp (rowCopy ρ (hOf hL (kind ρ))))) := by
  unfold ValOf
  congr 1

theorem agree_hOf_zero [NeZero d] (X : RowData C V d I J) (T : Set (WV I)) (g0 : Fin 2)
    (hT : ∀ w ∈ T, w.1 = g0) (k : Option (Fin 2 × ZMod d × ZMod d)) : Agree T (hOf X.hL k) 0 := by
  intro μ hμ
  rcases k with _ | ⟨g, a, a'⟩
  · rfl
  · rw [map_zero]
    refine X.hL_axes g a a' μ ?_
    have : g0 = g ∨ g0 = 1 - g := (by decide : ∀ x y : Fin 2, x = y ∨ x = 1 - y) g0 g
    rcases this with e | e
    · exact Or.inl fun w hw => (hT w (hμ w (Finsupp.mem_support_iff.1 hw))).trans e
    · exact Or.inr fun w hw => (hT w (hμ w (Finsupp.mem_support_iff.1 hw))).trans e

theorem hOf_mixed [NeZero d] (X : RowData C V d I J) (w0 w1 : WV I) (h0 : w0.1 = 0) (h1 : w1.1 = 1)
    (g : Fin 2) (a a' : ZMod d) (l0 : OnLeafV X.G g a a' w0) (l1 : OnLeafV X.G g a a' w1) :
    X.hL g a a' = X.hL 0 (tyW X.G w0) (tyW X.G w1) := by
  have hg : g = 0 ∨ g = 1 := (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) g
  unfold OnLeafV at l0 l1
  rw [h0] at l0
  rw [h1] at l1
  rcases hg with rfl | rfl
  · have e0 : tyW X.G w0 = a := by simpa using l0
    have e1 : tyW X.G w1 = a' := by simpa using l1
    rw [e0, e1]
  · have e0 : tyW X.G w0 = a' := by simpa using l0
    have e1 : tyW X.G w1 = a := by simpa using l1
    rw [e0, e1, X.hL_swap]

theorem valOf_kind_indep [NeZero d] (X : RowData C V d I J) {N : ℕ}
    (P : MvPolynomial (Fin N × WV I) C) (k k' : Fin N → Option (Fin 2 × ZMod d × ZMod d))
    (hk : RowsOK X.G X.Alt P k) (hk' : RowsOK X.G X.Alt P k')
    (gr : Fin N → MvPowerSeries (WV I) C) : ValOf X.hL P k gr = ValOf X.hL P k' gr := by
  rw [valOf_eq, valOf_eq]
  set S : Set (Fin N × WV I) := {x | ∃ μ ∈ P.support, μ x ≠ 0} with hS
  have key : ∀ ρ, Agree {w | (ρ, w) ∈ S} (hOf X.hL (k ρ)) (hOf X.hL (k' ρ)) := by
    intro ρ
    by_cases hone : ∃ g0 : Fin 2, ∀ w ∈ {w | (ρ, w) ∈ S}, w.1 = g0
    · obtain ⟨g0, hg0⟩ := hone
      intro μ hμ
      rw [agree_hOf_zero X _ g0 hg0 _ μ hμ, agree_hOf_zero X _ g0 hg0 _ μ hμ]
    · push Not at hone
      obtain ⟨w1, ⟨μ1, m1, n1⟩, e1⟩ := hone 0
      obtain ⟨w0, ⟨μ0, m0, n0⟩, e0⟩ := hone 1
      have f1 : w1.1 = 1 := by revert e1; generalize w1.1 = g; revert g; decide
      have f0 : w0.1 = 0 := by revert e0; generalize w0.1 = g; revert g; decide
      have aux : ∀ kk : Fin N → Option (Fin 2 × ZMod d × ZMod d), RowsOK X.G X.Alt P kk →
          hOf X.hL (kk ρ) = X.hL 0 (tyW X.G w0) (tyW X.G w1) := by
        intro kk hkk
        rcases hr : kk ρ with _ | ⟨g, a, a'⟩
        · obtain ⟨g, hg⟩ := hkk.2 ρ hr
          have := (hg μ0 m0 w0 n0).trans (hg μ1 m1 w1 n1).symm
          rw [f0, f1] at this
          exact absurd this (by decide)
        · obtain ⟨-, -, hl⟩ := hkk.1 ρ g a a' hr
          exact hOf_mixed X w0 w1 f0 f1 g a a' (hl μ0 m0 w0 n0) (hl μ1 m1 w1 n1)
      rw [aux k hk, aux k' hk']
      intro μ _
      rfl
  have hA := Agree.prod (S := S) Finset.univ (fun ρ =>
    Agree.mul (F := rowCopy ρ (gr ρ)) (F' := rowCopy ρ (gr ρ)) (fun _ _ => rfl)
      (agree_rowCopy S ρ _ _ (key ρ)).exp)
  unfold jetAt0
  exact Finset.sum_congr rfl fun μ hμ => by rw [hA μ fun x hx => ⟨μ, hμ, hx⟩]

end GlobalTheory.RowValueCheck
