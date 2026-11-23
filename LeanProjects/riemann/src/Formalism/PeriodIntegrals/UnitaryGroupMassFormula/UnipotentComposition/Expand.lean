import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentComposition.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentComposition.HasDerivAtInvpow

open Matrix MvPolynomial

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCompose

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U Formalism.REAL Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem continuous_vars {N : ℕ} : Continuous (vars : Matrix (Fin N) (Fin N) ℂ → Vr N → ℂ) := by
  refine continuous_pi fun i => ?_
  rcases i with x | x
  · exact (continuous_apply x.2).comp (continuous_apply x.1)
  · exact continuous_star.comp ((continuous_apply x.2).comp (continuous_apply x.1))

theorem continuous_DjU (k j ρ : ℕ) : Continuous (DjU k j ρ) := by
  have h : DjU k j ρ = fun g => eval (vars g) (qD k j ρ) := funext fun g => (eval_qD g).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp continuous_vars

theorem mem_step {k j ρ : ℕ} {X : Mat k (j + ρ)} {L : FS k (j + ρ)}
    {e : SC (2 * (j + ρ) + k + 1) × List (Mat k (j + ρ))} (he : e ∈ step k j ρ X L) :
    ∃ e₀ ∈ L, e.2 = e₀.2 ∨ e.2 = X :: e₀.2 := by
  rw [step, List.mem_flatMap] at he
  obtain ⟨e₀, he₀, h⟩ := he
  refine ⟨e₀, he₀, ?_⟩
  simp only [stepOne, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> simp

theorem mem_steps {k j ρ : ℕ} {w : List (Mat k (j + ρ))} {L : FS k (j + ρ)} :
    ∀ {e : SC (2 * (j + ρ) + k + 1) × List (Mat k (j + ρ))}, e ∈ steps k j ρ w L →
    ∃ e₀ ∈ L, e.2.length ≤ e₀.2.length + w.length ∧ ∀ Y ∈ e.2, Y ∈ e₀.2 ∨ Y ∈ w := by
  induction w with
  | nil => intro e he; exact ⟨e, he, by simp, fun Y hY => Or.inl hY⟩
  | cons X w ih =>
    intro e he
    have he' : e ∈ step k j ρ X (steps k j ρ w L) := he
    obtain ⟨e₁, he₁, h1⟩ := mem_step he'
    obtain ⟨e₀, he₀, hl, hY⟩ := ih he₁
    refine ⟨e₀, he₀, ?_, ?_⟩
    · rcases h1 with h1 | h1 <;> rw [h1] <;> simp only [List.length_cons] <;> omega
    · intro Y hYm
      rcases h1 with h1 | h1
      · rw [h1] at hYm
        rcases hY Y hYm with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · rw [h1] at hYm
        rcases List.mem_cons.1 hYm with rfl | hYm
        · exact Or.inr (by simp)
        · rcases hY Y hYm with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem _ h)

section calc_

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem hasDerivAt_listSum {α : Type*} (L : List α) (f : α → ℝ → E) (f' : α → E)
    (h : ∀ a ∈ L, HasDerivAt (f a) (f' a) 0) :
    HasDerivAt (fun t => (L.map fun a => f a t).sum) (L.map f').sum 0 := by
  induction L with
  | nil => simpa using hasDerivAt_const (0 : ℝ) (0 : E)
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a (by simp)).add (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem RdV_eq_Dx {k r : ℕ} (X : Mat k r) (f : Mat k r → E) : RdV X f = Dx (false, X) f := by
  first
  | rfl
  | simp [Dx]

theorem ck_Rw {k r m : ℕ} {F : Mat k r → E} (hF : CkOn (m : ℕ∞) (GV k r) F) {v : List (Mat k r)}
    (hv : ∀ X ∈ v, inLie k r X) (n : ℕ) (hn : n + v.length ≤ m) : CkOn (n : ℕ∞) (GV k r) (Rw v F) := by
  rw [← Dw_wR]
  apply CkOn_Dw (fun x hx => by obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hx; exact hv X hX)
  simp only [wR, List.length_map]
  exact sCkOn_mono (by exact_mod_cast hn) hF

theorem step_eq {k j ρ m : ℕ} {F : Mat k (j + ρ) → E} (hF : CkOn (m : ℕ∞) (GV k (j + ρ)) F)
    {X : Mat k (j + ρ)} (hX : inLie k (j + ρ) X) {L : FS k (j + ρ)}
    (hL : ∀ e ∈ L, ∀ Y ∈ e.2, inLie k (j + ρ) Y) (hm : ∀ e ∈ L, e.2.length + 1 ≤ m)
    {g : Mat k (j + ρ)} (hg : g ∈ GV k (j + ρ)) (hD : DjU k j ρ g ≠ 0) :
    RdV X (shape k j ρ F L) g = shape k j ρ F (step k j ρ X L) g := by
  have hterm : ∀ e ∈ L, HasDerivAt
      (fun t => sv k j ρ e.1 (crv (false, X) g t) • Rw e.2 F (crv (false, X) g t))
      (sv k j ρ e.1 g • Dx (false, X) (Rw e.2 F) g +
        (sv k j ρ (dP X e.1.1, e.1.2.1, e.1.2.2) g
          + sv k j ρ (C (-(e.1.2.1 : ℂ)) * e.1.1 * dP X (qD k j ρ), e.1.2.1 + 1, e.1.2.2) g
          + sv k j ρ (C (-(e.1.2.2 : ℂ)) * e.1.1 * dP X (qDb k j ρ), e.1.2.1, e.1.2.2 + 1) g)
          • Rw e.2 F g) 0 := by
    intro e he
    have h1 := hasDerivAt_sv X g hD e.1
    have hc := ck_Rw hF (hL e he) 1 (by have := hm e he; omega)
    rw [Nat.cast_one] at hc
    have h2 : HasDerivAt (fun t => Rw e.2 F (crv (false, X) g t)) (Dx (false, X) (Rw e.2 F) g) 0 :=
      CkOn_diff (x := (false, X)) hX hc hg hg
    have h3 := h1.smul h2
    simp only [crv_zero] at h3
    exact h3
  have hsum := hasDerivAt_listSum L _ _ hterm
  have hsum' : HasDerivAt (fun t => shape k j ρ F L (crv (false, X) g t)) _ 0 := hsum
  rw [RdV_eq_Dx, Dx_eq, hsum'.deriv, step, shape_flatMap]
  congr 1
  apply List.map_congr_left
  intro e _
  simp only [shape, stepOne, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [show Rw (X :: e.2) F g = Dx (false, X) (Rw e.2 F) g by rw [← RdV_eq_Dx]; rfl]
  simp only [add_smul]
  abel

end calc_

theorem expand : Expand := by
  intro k j ρ E _ _ m F hF w
  induction w with
  | nil => intro L _ _ _ g _ _; rfl
  | cons X w ih =>
    intro L hw hL hm g hg hD
    have hO : IsOpen {g : Mat k (j + ρ) | DjU k j ρ g ≠ 0} :=
      isOpen_ne_fun (continuous_DjU k j ρ) continuous_const
    have hIH : ∀ g' ∈ GV k (j + ρ), g' ∈ {g : Mat k (j + ρ) | DjU k j ρ g ≠ 0} →
        Rw w (shape k j ρ F L) g' = shape k j ρ F (steps k j ρ w L) g' :=
      fun g' hg' hg'O => ih L (fun Y hY => hw Y (List.mem_cons_of_mem _ hY)) hL
        (fun e he => by have := hm e he; simp only [List.length_cons] at this; omega) g' hg' hg'O
    have hX := hw X List.mem_cons_self
    show RdV X (Rw w (shape k j ρ F L)) g = shape k j ρ F (step k j ρ X (steps k j ρ w L)) g
    rw [RdV_eq_Dx, Dx_congr_loc (x := (false, X)) hX hO hIH g hg hD, ← RdV_eq_Dx]
    refine step_eq hF hX (fun e he Y hY => ?_) (fun e he => ?_) hg hD
    · obtain ⟨e₀, he₀, _, hm'⟩ := mem_steps he
      rcases hm' Y hY with h | h
      · exact hL e₀ he₀ Y h
      · exact hw Y (List.mem_cons_of_mem _ h)
    · obtain ⟨e₀, he₀, hl, _⟩ := mem_steps he
      have := hm e₀ he₀
      simp only [List.length_cons] at this
      omega

end PI.UnitaryGroupMassFormula.UsCompose
