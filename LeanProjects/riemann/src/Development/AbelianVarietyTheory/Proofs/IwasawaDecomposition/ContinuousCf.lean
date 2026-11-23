import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalBasis

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

noncomputable section

namespace GlobalTheory.TypeSumCtrl

def allWords {α : Type} {k : ℕ} (E : Fin k → α) (m : ℕ) : List (List α) :=
  Nat.rec [[]] (fun _ T => [] :: T.flatMap fun l => (List.ofFn E).map fun X => X :: l) m

theorem allWords_zero {α : Type} {k : ℕ} (E : Fin k → α) : allWords E 0 = [[]] := rfl

theorem allWords_succ {α : Type} {k : ℕ} (E : Fin k → α) (m : ℕ) :
    allWords E (m + 1) = [] :: (allWords E m).flatMap fun l => (List.ofFn E).map fun X => X :: l := rfl

theorem mem_allWords {α : Type} {k : ℕ} (E : Fin k → α) :
    ∀ (m : ℕ) (l : List α), l ∈ allWords E m ↔ l.length ≤ m ∧ ∀ X ∈ l, ∃ i, E i = X
  | 0, l => by
    cases l <;> simp [allWords_zero]
  | m + 1, [] => by simp [allWords_succ]
  | m + 1, X :: l => by
    simp only [allWords_succ, List.mem_cons, List.mem_flatMap, List.mem_map, List.mem_ofFn, List.length_cons,
      reduceCtorEq, false_or, List.cons.injEq, forall_eq_or_imp, Nat.add_le_add_iff_right]
    constructor
    · rintro ⟨l', h1, Y, h2, rfl, rfl⟩
      exact ⟨((mem_allWords E m _).1 h1).1, h2, ((mem_allWords E m _).1 h1).2⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨l, (mem_allWords E m _).2 ⟨h1, h3⟩, X, h2, rfl, rfl⟩

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ε : Fin n → Bool} {σ : Mx n → (H →L[ℂ] H)} {k : ℕ}

def cf (E : Fin k → Mx n) (X : Mx n) : ℝ := ∑ i, |((X * (E i)ᴴ).trace).re|

theorem cf_nonneg (E : Fin k → Mx n) (X : Mx n) : 0 ≤ cf E X := Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem continuous_cf (E : Fin k → Mx n) : Continuous (cf E) := by
  unfold cf
  refine continuous_finsetSum _ fun i _ => ?_
  exact (Complex.continuous_re.comp ((continuous_id.matrix_mul continuous_const).matrix_trace)).abs

omit [CompleteSpace H] in
theorem Dw_sum (hσ : IsURepOn (UJset ε) σ) {l : List (Mx n)} (hl : ∀ X ∈ l, X ∈ lieSet ε) (c : Fin k → ℂ)
    {x : Fin k → H} (hx : ∀ i, Sm ε σ (x i)) : Dw σ l (∑ i, c i • x i) = ∑ i, c i • Dw σ l (x i) := by
  obtain ⟨L, hL⟩ := exists_word (isUnit_Jm ε) hσ l hl
  have := congrArg Subtype.val (map_sum L (fun i => c i • (⟨x i, hx i⟩ : smooth (Jm ε) σ)) Finset.univ)
  simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul, hL] at this
  exact this

theorem key (h : Std ε σ) {E : Fin k → Mx n} (hE : ∀ i, E i ∈ lieSet ε)
    (hx : ∀ X ∈ lieSet ε, X = ∑ i, ((X * (E i)ᴴ).trace).re • E i) (m : ℕ) {w : H} (hw : Sm ε σ w)
    (l : List (Mx n)) (hl : ∀ X ∈ l, X ∈ lieSet ε) :
    ∀ p : List (Mx n), (∀ X ∈ p, ∃ i, E i = X) → p.length + l.length ≤ m →
      ‖Dw σ (p ++ l) w‖ ≤ (l.map (cf E)).prod * sobNorm σ (allWords E m) w := by
  induction l with
  | nil =>
    intro p hp hm
    simpa using norm_Dw_le_sobNorm σ ((mem_allWords E m p).2 ⟨by simpa using hm, hp⟩) w
  | cons X l ih =>
    intro p hp hm
    have hX := hl X List.mem_cons_self
    have hl' := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
    have hp' : ∀ Y ∈ p, Y ∈ lieSet ε := fun Y hY => by
      obtain ⟨i, rfl⟩ := hp Y hY
      exact hE i
    have hs := hw.word h.1 hl'
    have e1 : Dw σ (p ++ X :: l) w =
        ∑ i, ((((X * (E i)ᴴ).trace).re : ℝ) : ℂ) • Dw σ ((p ++ [E i]) ++ l) w := by
      rw [Dw_append]
      show Dw σ p (dRep σ X (Dw σ l w)) = _
      conv_lhs => rw [hx X hX]
      rw [h.dRep_sum hE hs, Dw_sum h.1 hp' _ (fun i => dRep_mem (isUnit_Jm ε) h.1 hs (hE i))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Dw_append, Dw_append]
      rfl
    rw [e1, List.map_cons, List.prod_cons, mul_assoc, cf, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left (ih hl' _ ?_ ?_) (abs_nonneg _)
    · intro Y hY
      rcases List.mem_append.1 hY with hY | hY
      · exact hp Y hY
      · exact ⟨i, (List.mem_singleton.1 hY).symm⟩
    · simp only [List.length_append, List.length_cons, List.length_nil] at hm ⊢
      omega

theorem sob_le (h : Std ε σ) {E : Fin k → Mx n} (hE : ∀ i, E i ∈ lieSet ε)
    (hx : ∀ X ∈ lieSet ε, X = ∑ i, ((X * (E i)ᴴ).trace).re • E i) (m : ℕ) {w : H} (hw : Sm ε σ w)
    (S : List (List (Mx n))) (hS : Words (lieSet ε) S) (hm : ∀ l ∈ S, l.length ≤ m) :
    sobNorm σ S w ≤ (S.map fun l => (l.map (cf E)).prod).sum * sobNorm σ (allWords E m) w := by
  rw [← List.sum_map_mul_right]
  conv_lhs => unfold sobNorm
  refine List.sum_le_sum fun l hl => ?_
  simpa using key h hE hx m hw l (hS l hl) [] (by simp) (by simpa using hm l hl)

theorem exists_ctrl : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ S₀ : List (List (Mx n)), Words (lieSet ε) S₀ → ∃ S : List (List (Mx n)), Words (lieSet ε) S ∧ [] ∈ S ∧ Ctrl (lieSet ε) (UJset ε) σ S ∧ ∃ A : ℝ, 0 ≤ A ∧ ∀ w, Sm ε σ w → sobNorm σ S₀ w ≤ A * sobNorm σ S w := by
  intro n ε H _ _ _ σ h S₀ hS₀
  obtain ⟨E, hE, -, hx⟩ := GlobalTheory.LieONB.exists_orthonormal_basis n ε
  have hE' : ∀ i, E i ∈ lieSet ε := fun i => (hE i).1
  have hx' : ∀ X ∈ lieSet ε, X = ∑ i, ((X * (E i)ᴴ).trace).re • E i := fun X hX => by
    simpa only [Complex.coe_smul] using hx X hX
  set m := (S₀.map List.length).sum with hm
  have hW : Words (lieSet ε) (allWords E m) := fun l hl X hX => by
    obtain ⟨i, rfl⟩ := ((mem_allWords E m l).1 hl).2 X hX
    exact hE' i
  refine ⟨allWords E m, hW, (mem_allWords E m _).2 (by simp), ?_,
    (S₀.map fun l => (l.map (cf E)).prod).sum, ?_, fun w hw => sob_le h hE' hx' m hw S₀ hS₀ fun l hl => ?_⟩
  · refine ⟨fun g => ((allWords E m).map fun l => (l.map fun X => cf E (Jm ε * gᴴ * Jm ε * X * g)).prod).sum, ?_,
      fun g hg w hw => ?_⟩
    · refine continuous_list_sum _ fun l _ => continuous_list_prod _ fun X _ => ?_
      exact (continuous_cf E).comp (f := fun g : Mx n => Jm ε * gᴴ * Jm ε * X * g)
        (((((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul
          continuous_const).matrix_mul continuous_const)).matrix_mul continuous_id)
    · rw [sobNorm_translate h.1 hg hw hW]
      have := sob_le h hE' hx' m hw ((allWords E m).map fun l => l.map fun X => g⁻¹ * X * g) ?_ ?_
      · simpa only [List.map_map, Function.comp_def, inv_eq_UJ hg] using this
      · intro l hl X hX
        obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
        obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
        exact conj_mem_lie (isUnit_Jm ε) hg (hW l' hl' Y hY)
      · intro l hl
        obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
        simpa using ((mem_allWords E m l').1 hl').1
  · refine List.sum_nonneg fun x hx => ?_
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
    refine List.prod_nonneg fun y hy => ?_
    obtain ⟨X, -, rfl⟩ := List.mem_map.1 hy
    exact cf_nonneg E X
  · exact List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.2 ⟨l, hl, rfl⟩)

end GlobalTheory.TypeSumCtrl

end
