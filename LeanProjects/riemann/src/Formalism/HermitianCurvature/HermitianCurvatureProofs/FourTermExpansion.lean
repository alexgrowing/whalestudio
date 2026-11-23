import Formalism.HermitianCurvature.HermitianCurvatureProofs.LieDecompositionLocal
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.FourTermExpansion

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem loc_zero (m : ℕ∞) (g : Mat k r) : Loc m (fun _ : Mat k r => (0 : E)) g := by
  unfold Loc
  exact ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩

theorem loc_of_eq {m : ℕ∞} {Ψ Ψ' : Mat k r → E} {g : Mat k r} (h : Ψ = Ψ') (h' : Loc m Ψ' g) : Loc m Ψ g := by
  subst h
  exact h'

theorem EZ_congr {Φ₁ Φ₂ : Mat k r → E} {U : Set (Mat k r)} (hU : IsOpen U) {g : Mat k r} (hg : g ∈ U)
    (hgG : g ∈ GV k r) (he : ∀ x ∈ U, x ∈ GV k r → Φ₁ x = Φ₂ x) (Z : Mat k r) : EZ Z Φ₁ g = EZ Z Φ₂ g := by
  show RdV _ Φ₁ g + Complex.I • RdV _ Φ₁ g = RdV _ Φ₂ g + Complex.I • RdV _ Φ₂ g
  rw [rdV_congr hU hg hgG (hermitian_part_mem_lie Z) he, rdV_congr hU hg hgG (antihermitian_part_mem_lie Z) he]

theorem EZ_lin {Φ₁ Φ₂ : Mat k r → E} {g : Mat k r} (h₁ : Loc 1 Φ₁ g) (h₂ : Loc 1 Φ₂ g) (hgG : g ∈ GV k r)
    (c : ℂ) (Z : Mat k r) : EZ Z (fun x => Φ₁ x + c • Φ₂ x) g = EZ Z Φ₁ g + c • EZ Z Φ₂ g := by
  show RdV _ (fun x => Φ₁ x + c • Φ₂ x) g + Complex.I • RdV _ (fun x => Φ₁ x + c • Φ₂ x) g =
    (RdV _ Φ₁ g + Complex.I • RdV _ Φ₁ g) + c • (RdV _ Φ₂ g + Complex.I • RdV _ Φ₂ g)
  rw [rdV_fun_add h₁ h₂ hgG (hermitian_part_mem_lie Z), rdV_fun_add h₁ h₂ hgG (antihermitian_part_mem_lie Z)]
  module

theorem EZ_zero (Z g : Mat k r) : EZ Z (fun _ : Mat k r => (0 : E)) g = 0 := by
  simp [EZ, RdV]

def LT (M : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Mat k r) :
    Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E) :=
  fun a b => EZ (M a b)

def fold (M : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Mat k r)
    (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) (Φ : Mat k r → E) : Mat k r → E :=
  (ts.map fun t => Top (LT M) t.1 t.2.1 t.2.2).foldr (fun T h => T h) Φ

variable (M : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Mat k r)

theorem fold_nil (Φ : Mat k r → E) : fold M [] Φ = Φ := rfl

theorem fold_cons (t : ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) (ts) (Φ : Mat k r → E) :
    fold M (t :: ts) Φ = Top (LT M) t.1 t.2.1 t.2.2 (fold M ts Φ) := rfl

theorem fold_append (ts ts' : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) (Φ : Mat k r → E) :
    fold M (ts ++ ts') Φ = fold M ts (fold M ts' Φ) := by
  simp only [fold, List.map_append, List.foldr_append]

theorem top_apply'' (v : ℂ) (a b : Fin (2 * r + k + 1)) (Φ : Mat k r → E) (g : Mat k r) :
    Top (LT M) v a b Φ g = (if a = b then v • Φ g else 0) + EZ (M a b) Φ g := rfl

theorem top_congr {Φ₁ Φ₂ : Mat k r → E} {U : Set (Mat k r)} (hU : IsOpen U)
    (he : ∀ x ∈ U, x ∈ GV k r → Φ₁ x = Φ₂ x) (v : ℂ) (a b : Fin (2 * r + k + 1)) :
    ∀ x ∈ U, x ∈ GV k r → Top (LT M) v a b Φ₁ x = Top (LT M) v a b Φ₂ x := by
  intro x hx hxG
  rw [top_apply'' M, top_apply'' M, he x hx hxG, EZ_congr hU hx hxG he]

theorem top_lin {Φ₁ Φ₂ : Mat k r → E} {g : Mat k r} (h₁ : Loc 1 Φ₁ g) (h₂ : Loc 1 Φ₂ g) (hgG : g ∈ GV k r)
    (c : ℂ) (v : ℂ) (a b : Fin (2 * r + k + 1)) :
    Top (LT M) v a b (fun x => Φ₁ x + c • Φ₂ x) g = Top (LT M) v a b Φ₁ g + c • Top (LT M) v a b Φ₂ g := by
  rw [top_apply'' M, top_apply'' M, top_apply'' M, EZ_lin h₁ h₂ hgG]
  split_ifs <;> module

theorem top_loc {m : ℕ∞} {Φ : Mat k r → E} {g : Mat k r} (h : Loc (m + 1) Φ g) (v : ℂ)
    (a b : Fin (2 * r + k + 1)) : Loc m (Top (LT M) v a b Φ) g := by
  have hΦ : Loc m Φ g := loc_mono le_self_add h
  have h1 : Loc m (fun x => if a = b then v • Φ x else 0) g := by
    by_cases hab : a = b
    · exact loc_of_eq (by funext x; simp [hab]) (loc_add (loc_zero m g) hΦ v)
    · exact loc_of_eq (by funext x; simp [hab]) (loc_zero m g)
  exact loc_of_eq (by funext x; simp [top_apply'']) (loc_add h1 (loc_EZ (M a b) h) 1)

theorem fold_congr (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) {Φ₁ Φ₂ : Mat k r → E}
    {U : Set (Mat k r)} (hU : IsOpen U) (he : ∀ x ∈ U, x ∈ GV k r → Φ₁ x = Φ₂ x) :
    ∀ x ∈ U, x ∈ GV k r → fold M ts Φ₁ x = fold M ts Φ₂ x := by
  induction ts with
  | nil => exact he
  | cons t ts ih =>
    intro x hx hxG
    rw [fold_cons, fold_cons]
    exact top_congr M hU ih t.1 t.2.1 t.2.2 x hx hxG

theorem fold_loc (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) :
    ∀ (m : ℕ) (Φ : Mat k r → E) (g : Mat k r), Loc ((m + ts.length : ℕ) : ℕ∞) Φ g →
      Loc (m : ℕ∞) (fold M ts Φ) g := by
  induction ts with
  | nil =>
    intro m Φ g h
    rw [fold_nil]
    simpa using h
  | cons t ts ih =>
    intro m Φ g h
    rw [fold_cons]
    have e : m + 1 + ts.length = m + (t :: ts).length := by simp only [List.length_cons]; omega
    have h' : Loc ((m + 1 + ts.length : ℕ) : ℕ∞) Φ g := by rw [e]; exact h
    have := ih (m + 1) Φ g h'
    exact top_loc M (by exact_mod_cast this) t.1 t.2.1 t.2.2

theorem fold_zero (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) :
    ∀ x ∈ GV k r, fold M ts (fun _ : Mat k r => (0 : E)) x = 0 := by
  induction ts with
  | nil => intro x _; rfl
  | cons t ts ih =>
    intro x hx
    rw [fold_cons, top_apply'' M, ih x hx,
      EZ_congr (Φ₂ := fun _ => (0 : E)) isOpen_univ (Set.mem_univ x) hx (fun y _ hy => ih y hy) (M t.2.1 t.2.2),
      EZ_zero]
    simp

theorem fold_lin (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) :
    ∀ (Φ₁ Φ₂ : Mat k r → E) (g : Mat k r), g ∈ GV k r → Loc (ts.length : ℕ∞) Φ₁ g →
      Loc (ts.length : ℕ∞) Φ₂ g → ∀ c : ℂ,
        fold M ts (fun x => Φ₁ x + c • Φ₂ x) g = fold M ts Φ₁ g + c • fold M ts Φ₂ g := by
  induction ts with
  | nil => intro Φ₁ Φ₂ g _ _ _ c; rfl
  | cons t ts ih =>
    intro Φ₁ Φ₂ g hg h₁ h₂ c
    obtain ⟨U₁, hU₁, hgU₁, hU₁'⟩ := loc_spread h₁
    obtain ⟨U₂, hU₂, hgU₂, hU₂'⟩ := loc_spread h₂
    have hle : (ts.length : ℕ∞) ≤ ((t :: ts).length : ℕ∞) := by exact_mod_cast Nat.le_succ ts.length
    have heq : ∀ x ∈ U₁ ∩ U₂, x ∈ GV k r →
        fold M ts (fun y => Φ₁ y + c • Φ₂ y) x = (fun y => fold M ts Φ₁ y + c • fold M ts Φ₂ y) x :=
      fun x hx hxG => ih Φ₁ Φ₂ x hxG (loc_mono hle (hU₁' x hx.1)) (loc_mono hle (hU₂' x hx.2)) c
    have e1 : 1 + ts.length = (t :: ts).length := by simp only [List.length_cons]; omega
    have hf₁ : Loc 1 (fold M ts Φ₁) g := by
      have := fold_loc M ts 1 Φ₁ g (by rw [e1]; exact h₁)
      simpa using this
    have hf₂ : Loc 1 (fold M ts Φ₂) g := by
      have := fold_loc M ts 1 Φ₂ g (by rw [e1]; exact h₂)
      simpa using this
    rw [fold_cons, fold_cons, fold_cons, top_congr M (hU₁.inter hU₂) heq t.1 t.2.1 t.2.2 g ⟨hgU₁, hgU₂⟩ hg]
    exact top_lin M hf₁ hf₂ hg c t.1 t.2.1 t.2.2

end Formalism.FourierDecayAlt.P.FourTermExpansion

namespace Formalism.FourierDecayAlt.P.FourTermExpansion

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Msg (k r : ℕ) (a b : Fin (2 * r + k + 1)) : Mat k r := Matrix.single a b 1

theorem single_comm (a b c d : Fin (2 * r + k + 1)) :
    Msg k r a b * Msg k r c d - Msg k r c d * Msg k r a b =
      (if b = c then (1 : ℂ) else 0) • Msg k r a d + (-(if d = a then (1 : ℂ) else 0)) • Msg k r c b := by
  ext i j
  simp only [Msg, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.single_apply,
    smul_eq_mul]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', ite_and]
  split_ifs <;> simp_all

theorem gl_single {Φ : Mat k r → E} {g : Mat k r} (hloc : Loc 2 Φ g) (hgG : g ∈ GV k r)
    (a b c d : Fin (2 * r + k + 1)) :
    EZ (Msg k r a b) (EZ (Msg k r c d) Φ) g - EZ (Msg k r c d) (EZ (Msg k r a b) Φ) g =
      (if b = c then (1 : ℂ) else 0) • EZ (Msg k r a d) Φ g -
        (if d = a then (1 : ℂ) else 0) • EZ (Msg k r c b) Φ g := by
  rw [EZ_comm _ _ hloc hgG, single_comm, EZ_add (loc_mono (by norm_num) hloc) hgG,
    EZ_smul (loc_mono (by norm_num) hloc) hgG, EZ_smul (loc_mono (by norm_num) hloc) hgG, neg_smul,
    ← sub_eq_add_neg]

theorem EZ_smul_fun {Φ : Mat k r → E} {g : Mat k r} (h : Loc 1 Φ g) (hgG : g ∈ GV k r) (c : ℂ)
    (Z : Mat k r) : EZ Z (fun x => c • Φ x) g = c • EZ Z Φ g := by
  have e1 : RdV (hpart1 (Hpk k r) Z) (fun x => c • Φ x) g = c • RdV (hpart1 (Hpk k r) Z) Φ g :=
    ((loc_hasDerivAt le_rfl h hgG (hermitian_part_mem_lie Z)).const_smul c).deriv
  have e2 : RdV (hpart2 (Hpk k r) Z) (fun x => c • Φ x) g = c • RdV (hpart2 (Hpk k r) Z) Φ g :=
    ((loc_hasDerivAt le_rfl h hgG (antihermitian_part_mem_lie Z)).const_smul c).deriv
  show RdV _ (fun x => c • Φ x) g + Complex.I • RdV _ (fun x => c • Φ x) g =
    c • (RdV _ Φ g + Complex.I • RdV _ Φ g)
  rw [e1, e2]
  module

theorem EZ_top {Φ : Mat k r → E} {g : Mat k r} (hloc : Loc 2 Φ g) (hgG : g ∈ GV k r) (Z : Mat k r)
    (y : ℂ) (q d : Fin (2 * r + k + 1)) :
    EZ Z (Top (LT (Msg k r)) y q d Φ) g =
      (if q = d then (1 : ℂ) else 0) • (y • EZ Z Φ g) + EZ Z (EZ (Msg k r q d) Φ) g := by
  have hΦ1 : Loc 1 Φ g := loc_mono (by norm_num) hloc
  have h11 : Loc (1 + 1) Φ g := by rw [one_add_one_eq_two]; exact hloc
  by_cases hqd : q = d
  · have e : Top (LT (Msg k r)) y q d Φ = fun x => y • Φ x + (1 : ℂ) • EZ (Msg k r q d) Φ x := by
      funext x; simp [top_apply'', hqd]
    have hy1 : Loc 1 (fun x => y • Φ x) g := loc_of_eq (by funext x; simp) (loc_add (loc_zero 1 g) hΦ1 y)
    rw [e, EZ_lin hy1 (loc_EZ _ h11) hgG, EZ_smul_fun hΦ1 hgG]
    simp [hqd]
  · have e : Top (LT (Msg k r)) y q d Φ = EZ (Msg k r q d) Φ := by
      funext x; simp [top_apply'', hqd]
    rw [e]
    simp [hqd]

private theorem top_top_lemma_10 {Φ : Mat k r → E} {g : Mat k r} (hloc : Loc 2 Φ g) (hgG : g ∈ GV k r) (x y : ℂ)
    (a b c d : Fin (2 * r + k + 1)) :
    Top (LT (Msg k r)) x a b (Top (LT (Msg k r)) y c d Φ) g =
      (if a = b then x • ((if c = d then y • Φ g else 0) + EZ (Msg k r c d) Φ g) else 0) +
        ((if c = d then (1 : ℂ) else 0) • (y • EZ (Msg k r a b) Φ g) + EZ (Msg k r a b) (EZ (Msg k r c d) Φ) g) := by
  rw [top_apply'' (Msg k r), EZ_top hloc hgG, top_apply'' (Msg k r)]

theorem two {Φ : Mat k r → E} {g : Mat k r} (hloc : Loc 2 Φ g) (hgG : g ∈ GV k r) (x y : ℂ) (hxy : x - y = 1)
    (p q c d : Fin (2 * r + k + 1)) :
    Top (LT (Msg k r)) x p c (Top (LT (Msg k r)) y q d Φ) g
      - Top (LT (Msg k r)) x q c (Top (LT (Msg k r)) y p d Φ) g
      + Top (LT (Msg k r)) x p d (Top (LT (Msg k r)) y q c Φ) g
      - Top (LT (Msg k r)) x q d (Top (LT (Msg k r)) y p c Φ) g = 0 := by
  rw [top_top_lemma_10 hloc hgG, top_top_lemma_10 hloc hgG, top_top_lemma_10 hloc hgG, top_top_lemma_10 hloc hgG]
  have g1 := gl_single hloc hgG p c q d
  have g2 := gl_single hloc hgG p d q c
  rw [sub_eq_iff_eq_add] at g1 g2
  rw [g1, g2]
  obtain rfl : x = y + 1 := by linear_combination hxy
  simp only [@eq_comm _ c q, @eq_comm _ d p, @eq_comm _ d q, @eq_comm _ c p]
  split_ifs <;> module

end Formalism.FourierDecayAlt.P.FourTermExpansion

namespace Formalism.FourierDecayAlt.P.FourTermExpansion

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem half (X : E) (h : X + X = 0) : X = 0 := by
  have h2 : (2 : ℂ) • X = 0 := by rw [two_smul]; exact h
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

theorem split (M : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Mat k r) {t : ℕ}
    (f : Fin t → ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) (i : ℕ) (hi : i + 1 < t) (Φ : Mat k r → E) :
    fold M (List.ofFn f) Φ = fold M ((List.ofFn f).take i)
      (Top (LT M) (f ⟨i, by omega⟩).1 (f ⟨i, by omega⟩).2.1 (f ⟨i, by omega⟩).2.2
        (Top (LT M) (f ⟨i + 1, hi⟩).1 (f ⟨i + 1, hi⟩).2.1 (f ⟨i + 1, hi⟩).2.2
          (fold M ((List.ofFn f).drop (i + 2)) Φ))) := by
  conv_lhs =>
    rw [← List.take_append_drop i (List.ofFn f),
      List.drop_eq_getElem_cons (l := List.ofFn f) (i := i) (by simp; omega),
      List.drop_eq_getElem_cons (l := List.ofFn f) (i := i + 1) (by simp; omega)]
  rw [fold_append, fold_cons, fold_cons, List.getElem_ofFn, List.getElem_ofFn]
  all_goals rfl

theorem four {t : ℕ} (f₁ f₂ f₃ f₄ : Fin t → ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) (i : ℕ)
    (hi : i + 1 < t)
    (h₂ : ∀ j : Fin t, (j : ℕ) ≠ i → (j : ℕ) ≠ i + 1 → f₂ j = f₁ j)
    (h₃ : ∀ j : Fin t, (j : ℕ) ≠ i → (j : ℕ) ≠ i + 1 → f₃ j = f₁ j)
    (h₄ : ∀ j : Fin t, (j : ℕ) ≠ i → (j : ℕ) ≠ i + 1 → f₄ j = f₁ j)
    (hmid : ∀ (Ψ : Mat k r → E) (x : Mat k r), x ∈ GV k r → Loc 2 Ψ x →
      (let P := fun (f : Fin t → ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) =>
        Top (LT (Msg k r)) (f ⟨i, by omega⟩).1 (f ⟨i, by omega⟩).2.1 (f ⟨i, by omega⟩).2.2
          (Top (LT (Msg k r)) (f ⟨i + 1, hi⟩).1 (f ⟨i + 1, hi⟩).2.1 (f ⟨i + 1, hi⟩).2.2 Ψ) x
       P f₁ - P f₂ + P f₃ - P f₄ = 0))
    (Φ : Mat k r → E) (g : Mat k r) (hg : g ∈ GV k r) (hloc : Loc (t : ℕ∞) Φ g) :
    fold (Msg k r) (List.ofFn f₁) Φ g - fold (Msg k r) (List.ofFn f₂) Φ g +
      fold (Msg k r) (List.ofFn f₃) Φ g - fold (Msg k r) (List.ofFn f₄) Φ g = 0 := by
  rw [split _ f₁ i hi, split _ f₂ i hi, split _ f₃ i hi, split _ f₄ i hi,
    Formalism.REAL.take_ofFn_congr f₂ f₁ i (fun j hj => h₂ j (by omega) (by omega)),
    Formalism.REAL.take_ofFn_congr f₃ f₁ i (fun j hj => h₃ j (by omega) (by omega)),
    Formalism.REAL.take_ofFn_congr f₄ f₁ i (fun j hj => h₄ j (by omega) (by omega)),
    Formalism.REAL.drop_ofFn_congr f₂ f₁ (i + 2) (fun j hj => h₂ j (by omega) (by omega)),
    Formalism.REAL.drop_ofFn_congr f₃ f₁ (i + 2) (fun j hj => h₃ j (by omega) (by omega)),
    Formalism.REAL.drop_ofFn_congr f₄ f₁ (i + 2) (fun j hj => h₄ j (by omega) (by omega))]
  set L := (List.ofFn f₁).take i with hL
  set Ψ := fold (Msg k r) ((List.ofFn f₁).drop (i + 2)) Φ with hΨ
  have hLlen : L.length = i := by simp [hL]; omega
  have hdlen : ((List.ofFn f₁).drop (i + 2)).length + (i + 2) = t := by simp; omega

  set P : (Fin t → ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) → Mat k r → E := fun f =>
    Top (LT (Msg k r)) (f ⟨i, by omega⟩).1 (f ⟨i, by omega⟩).2.1 (f ⟨i, by omega⟩).2.2
      (Top (LT (Msg k r)) (f ⟨i + 1, hi⟩).1 (f ⟨i + 1, hi⟩).2.1 (f ⟨i + 1, hi⟩).2.2 Ψ) with hP
  show fold (Msg k r) L (P f₁) g - fold (Msg k r) L (P f₂) g + fold (Msg k r) L (P f₃) g -
    fold (Msg k r) L (P f₄) g = 0
  obtain ⟨U, hU, hgU, hUl⟩ := loc_spread hloc
  have hΨloc : ∀ x ∈ U, Loc ((i + 2 : ℕ) : ℕ∞) Ψ x := by
    intro x hx
    apply fold_loc (Msg k r) _ (i + 2) Φ x
    rw [add_comm, hdlen]; exact hUl x hx
  have hPloc : ∀ f, Loc ((L.length : ℕ) : ℕ∞) (P f) g := by
    intro f
    rw [hLlen]
    have h := hΨloc g hgU
    have : Loc ((i + 1 : ℕ) : ℕ∞ ) (Top (LT (Msg k r)) (f ⟨i + 1, hi⟩).1 (f ⟨i + 1, hi⟩).2.1
        (f ⟨i + 1, hi⟩).2.2 Ψ) g := top_loc _ (by exact_mod_cast h) _ _ _
    exact top_loc _ (by exact_mod_cast this) _ _ _
  set Q12 : Mat k r → E := fun w => P f₁ w + (-1 : ℂ) • P f₂ w with hQ12
  set Q123 : Mat k r → E := fun w => Q12 w + (1 : ℂ) • P f₃ w with hQ123
  set F : Mat k r → E := fun w => Q123 w + (-1 : ℂ) • P f₄ w with hF
  have lQ12 : Loc ((L.length : ℕ) : ℕ∞) Q12 g := loc_add (hPloc f₁) (hPloc f₂) (-1 : ℂ)
  have lQ123 : Loc ((L.length : ℕ) : ℕ∞) Q123 g := loc_add lQ12 (hPloc f₃) 1
  have hvan : ∀ x ∈ U, x ∈ GV k r → F x = (fun _ => (0 : E)) x := by
    intro x hx hxG
    have := hmid Ψ x hxG (loc_mono (by norm_num) (hΨloc x hx))
    simp only at this
    simp only [hF, hQ123, hQ12, neg_one_smul, one_smul]
    rw [← sub_eq_add_neg, ← sub_eq_add_neg]
    exact this
  have e1 : fold (Msg k r) L F g = fold (Msg k r) L Q123 g + (-1 : ℂ) • fold (Msg k r) L (P f₄) g :=
    fold_lin (Msg k r) L Q123 (P f₄) g hg lQ123 (hPloc f₄) (-1)
  have e2 : fold (Msg k r) L Q123 g = fold (Msg k r) L Q12 g + (1 : ℂ) • fold (Msg k r) L (P f₃) g :=
    fold_lin (Msg k r) L Q12 (P f₃) g hg lQ12 (hPloc f₃) 1
  have e3 : fold (Msg k r) L Q12 g = fold (Msg k r) L (P f₁) g + (-1 : ℂ) • fold (Msg k r) L (P f₂) g :=
    fold_lin (Msg k r) L (P f₁) (P f₂) g hg (hPloc f₁) (hPloc f₂) (-1)
  have hzero : fold (Msg k r) L F g = 0 := by
    rw [fold_congr (Msg k r) L hU hvan g hgU hg, fold_zero (Msg k r) L g hg]
  rw [e1, e2, e3] at hzero
  simp only [neg_one_smul, one_smul] at hzero
  rw [← hzero]; abel

end Formalism.FourierDecayAlt.P.FourTermExpansion

namespace Formalism.FourierDecayAlt.P.FourTermExpansion

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def PP {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (σ : Equiv.Perm (Fin t)) (Φ : Mat k r → E) :
    Mat k r → E :=
  fold (Msg k r) (List.ofFn fun j : Fin t => (u - ((j : ℕ) : ℂ), a (σ j), b j)) Φ

theorem qm_eq {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (Φ : Mat k r → E) (g : Mat k r) :
    qminorOp (Q.EH k r) a b u Φ g = ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) • PP a b u σ Φ g := by
  unfold qminorOp
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Pi.smul_apply]
  simp only [PP, fold, List.map_ofFn]
  rfl

theorem key {m : ℕ} (a b : Fin (m + 1) → Fin (2 * r + k + 1)) (i : Fin m) (u : ℂ) (σ : Equiv.Perm (Fin (m + 1)))
    (Φ : Mat k r → E) (g : Mat k r) (hg : g ∈ GV k r) (hloc : Loc ((m + 1 : ℕ) : ℕ∞) Φ g) :
    PP a b u σ Φ g - PP a b u (σ * Equiv.swap i.castSucc i.succ) Φ g
      + PP a (b ∘ Equiv.swap i.castSucc i.succ) u σ Φ g
      - PP a (b ∘ Equiv.swap i.castSucc i.succ) u (σ * Equiv.swap i.castSucc i.succ) Φ g = 0 := by
  have hi : (i : ℕ) + 1 < m + 1 := by omega
  have hsw : ∀ j : Fin (m + 1), (j : ℕ) ≠ i → (j : ℕ) ≠ i + 1 → Equiv.swap i.castSucc i.succ j = j :=
    fun j h1 h2 => Equiv.swap_apply_of_ne_of_ne (fun h => h1 (by rw [h, Fin.coe_castSucc]))
      (fun h => h2 (by rw [h, Fin.val_succ]))
  have hc : (⟨(i : ℕ), by omega⟩ : Fin (m + 1)) = i.castSucc := Fin.ext rfl
  have hs : (⟨(i : ℕ) + 1, hi⟩ : Fin (m + 1)) = i.succ := Fin.ext rfl
  refine four (f₁ := fun j => (u - ((j : ℕ) : ℂ), a (σ j), b j))
    (f₂ := fun j => (u - ((j : ℕ) : ℂ), a ((σ * Equiv.swap i.castSucc i.succ) j), b j))
    (f₃ := fun j => (u - ((j : ℕ) : ℂ), a (σ j), (b ∘ Equiv.swap i.castSucc i.succ) j))
    (f₄ := fun j => (u - ((j : ℕ) : ℂ), a ((σ * Equiv.swap i.castSucc i.succ) j), (b ∘ Equiv.swap i.castSucc i.succ) j))
    (i : ℕ) hi ?_ ?_ ?_ ?_ Φ g hg hloc
  · intro j h1 h2; simp only [Equiv.Perm.mul_apply, hsw j h1 h2]
  · intro j h1 h2; simp only [Function.comp_apply, hsw j h1 h2]
  · intro j h1 h2; simp only [Equiv.Perm.mul_apply, Function.comp_apply, hsw j h1 h2]
  · intro Ψ x hx hΨ
    simp only [hc, hs, Equiv.Perm.mul_apply, Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
      Fin.coe_castSucc, Fin.val_succ]
    exact two hΨ hx _ _ (by push_cast; ring) _ _ _ _

theorem adj {m : ℕ} (a b : Fin (m + 1) → Fin (2 * r + k + 1)) (i : Fin m) (u : ℂ)
    (Φ : Mat k r → E) (g : Mat k r) (hg : g ∈ GV k r) (hloc : Loc ((m + 1 : ℕ) : ℕ∞) Φ g) :
    qminorOp (Q.EH k r) a (b ∘ Equiv.swap i.castSucc i.succ) u Φ g = -qminorOp (Q.EH k r) a b u Φ g := by
  have hne : i.castSucc ≠ i.succ := (show i.castSucc < i.succ from Fin.castSucc_lt_succ).ne
  have hsg : ∀ σ : Equiv.Perm (Fin (m + 1)),
      ((Equiv.Perm.sign (σ * Equiv.swap i.castSucc i.succ) : ℤ) : ℂ) = -((Equiv.Perm.sign σ : ℤ) : ℂ) := by
    intro σ
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne]
    push_cast
    ring
  have hre : ∀ c : Fin (m + 1) → Fin (2 * r + k + 1),
      ∑ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤ) : ℂ) • PP a c u (σ * Equiv.swap i.castSucc i.succ) Φ g =
        -∑ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤ) : ℂ) • PP a c u σ Φ g := by
    intro c
    rw [← Finset.sum_neg_distrib]
    exact Fintype.sum_equiv (Equiv.mulRight (Equiv.swap i.castSucc i.succ)) _ _
      (fun σ => by simp only [Equiv.coe_mulRight, hsg, neg_smul, neg_neg])
  have hsum : ∑ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
      (PP a b u σ Φ g - PP a b u (σ * Equiv.swap i.castSucc i.succ) Φ g
        + PP a (b ∘ Equiv.swap i.castSucc i.succ) u σ Φ g
        - PP a (b ∘ Equiv.swap i.castSucc i.succ) u (σ * Equiv.swap i.castSucc i.succ) Φ g) = 0 :=
    Finset.sum_eq_zero fun σ _ => by rw [key a b i u σ Φ g hg hloc, smul_zero]
  simp only [smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, hre] at hsum
  rw [qm_eq, qm_eq]
  have h2 := half _ (show ((∑ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤ) : ℂ) • PP a b u σ Φ g) +
      ∑ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤ) : ℂ) • PP a (b ∘ Equiv.swap i.castSucc i.succ) u σ Φ g) +
      ((∑ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤ) : ℂ) • PP a b u σ Φ g) +
      ∑ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤ) : ℂ) • PP a (b ∘ Equiv.swap i.castSucc i.succ) u σ Φ g) = 0
    by rw [← hsum]; abel)
  exact eq_neg_of_add_eq_zero_right h2

theorem skewCol {t : ℕ} (a : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (Φ : Mat k r → E) (g : Mat k r)
    (hg : g ∈ GV k r) (hloc : Loc (t : ℕ∞) Φ g) :
    ∀ (b : Fin t → Fin (2 * r + k + 1)) (τ : Equiv.Perm (Fin t)),
      qminorOp (Q.EH k r) a (b ∘ τ) u Φ g = ((Equiv.Perm.sign τ : ℤ) : ℂ) • qminorOp (Q.EH k r) a b u Φ g := by
  intro b τ
  cases t with
  | zero =>
    have : τ = 1 := Subsingleton.elim _ _
    subst this
    simp
  | succ m =>
    have hτ : τ ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ m]; exact Submonoid.mem_top τ
    induction hτ using Submonoid.closure_induction generalizing b with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [adj a b i u Φ g hg hloc, Equiv.Perm.sign_swap (show i.castSucc < i.succ from Fin.castSucc_lt_succ).ne]
      simp
    | one => simp
    | mul x y _ _ ihx ihy =>
      rw [show b ∘ ⇑(x * y) = (b ∘ ⇑x) ∘ ⇑y from rfl, ihy (b ∘ ⇑x), ihx b, smul_smul, Equiv.Perm.sign_mul]
      congr 1
      push_cast
      ring

end Formalism.FourierDecayAlt.P.FourTermExpansion
