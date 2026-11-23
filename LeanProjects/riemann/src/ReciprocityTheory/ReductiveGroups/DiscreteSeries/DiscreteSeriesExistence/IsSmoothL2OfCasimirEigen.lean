import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RregRep
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.ClassTwoEntries

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def IsSmoothL2 (ε : Fin n → Bool) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  Formalism.REAL.SmoothOnG ε F ∧ ∀ w : List (Fin n × Fin n),
    MemLp (fun g : Formalism.REAL.UJ ε => Formalism.REAL.Eword ε w F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)

theorem eword_append_Eab (ε : Fin n → Bool) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (p : Fin n × Fin n) :
    ∀ w : List (Fin n × Fin n),
      Formalism.REAL.Eword ε w (Formalism.REAL.Eab ε p.1 p.2 F) = Formalism.REAL.Eword ε (w ++ [p]) F
  | [] => rfl
  | q :: w => by
      simp only [List.cons_append, Formalism.REAL.Eword]
      rw [eword_append_Eab ε F p w]

theorem IsSmoothL2.Eab {ε : Fin n → Bool} {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : IsSmoothL2 ε F)
    (a b : Fin n) : IsSmoothL2 ε (Formalism.REAL.Eab ε a b F) := by
  refine ⟨Formalism.REAL.smooth_lie_derivative a b hF.1, fun w => ?_⟩
  have h := eword_append_Eab ε F (a, b) w
  simp only at h
  rw [h]
  exact hF.2 _

theorem isSmoothL2_of_casimir_eigen (ε : Fin n → Bool) (W : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ)) (c : ℂ)
    (hW : FiniteDimensional ℂ W) (hsm : ∀ w ∈ W, Formalism.REAL.SmoothOnG ε w)
    (hK : ∀ w ∈ W, ∀ i j : Fin n, ε i = ε j → ∃ w' ∈ W, ∀ g, Formalism.REAL.inUJ ε g → Formalism.REAL.Eab ε i j w g = w' g)
    (hc : ∀ w ∈ W, ∀ g, Formalism.REAL.inUJ ε g → Formalism.REAL.CasF ε w g = c * w g)
    (hL2 : ∀ w ∈ W, MemLp (fun g : Formalism.REAL.UJ ε => w (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)) :
    ∀ w ∈ W, IsSmoothL2 ε w := by
  have hint : ∀ w ∈ W, Integrable (fun g : Formalism.REAL.UJ ε =>
      Real.exp (2 * (0:ℝ) * Formalism.REAL.hh (Formalism.REAL.toM g)) * ‖w (Formalism.REAL.toM g)‖ ^ 2) (Formalism.REAL.muG ε) := by
    intro w hw
    have := (hL2 w hw).integrable_norm_pow (by norm_num)
    simpa using this
  have key := r0bG n ε W c 0 hW le_rfl hsm hK hc hint
  intro f hf
  refine ⟨hsm f hf, fun w => ?_⟩
  obtain ⟨hs, hi, -⟩ := key w [] f f hf hf
  have hae : AEStronglyMeasurable (fun g : Formalism.REAL.UJ ε => Formalism.REAL.Eword ε w f (Formalism.MainNotions.S.umat g))
      (Formalism.REAL.muG ε) := (Formalism.REAL.continuous_smooth_on_group_eval hs).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hae]
  simpa using hi

end ReciprocityTheory.ChartRestriction.DS
