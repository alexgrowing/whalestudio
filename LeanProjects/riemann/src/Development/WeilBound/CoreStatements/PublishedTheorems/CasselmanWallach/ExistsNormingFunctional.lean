import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobBdSeminorm

noncomputable section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum

namespace PositivityTheory.CW

namespace ZeroOnDense

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)} {E : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [T2Space E]
  {p : ℕ → Seminorm ℂ E}

theorem zero_on (hp : WithSeminorms p) (hD : Dens ε σ) (Φ : H → E)
    (hsub : ∀ x y, Sm ε σ x → Sm ε σ y → Φ (x - y) = Φ x - Φ y)
    (hb : ∀ i, ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧
      ∀ u, Sm ε σ u → p i (Φ u) ≤ C * sobNorm σ S u)
    (h0 : ∀ v, IsKFin ε σ v → Φ v = 0) : ∀ w, Sm ε σ w → Φ w = 0 := by
  intro w hw
  by_contra hne
  obtain ⟨i, hi⟩ := hp.separating_of_T1 _ hne
  obtain ⟨S, C, hS, hC⟩ := hb i
  have key : ∀ δ : ℝ, 0 < δ → p i (Φ w) ≤ |C| * δ := by
    intro δ hδ
    obtain ⟨v, hv, hd⟩ := hD.2.2 w hw S hS δ hδ
    have hvs : Sm ε σ v := hD.1 v hv
    have hwv : Sm ε σ (w - v) := sm_iff.2 ((smooth (Jm ε) σ).sub_mem (sm_iff.1 hw) (sm_iff.1 hvs))
    have e : Φ w = Φ (w - v) := by rw [hsub w v hw hvs, h0 v hv, sub_zero]
    rw [e]
    calc p i (Φ (w - v)) ≤ C * sobNorm σ S (w - v) := hC _ hwv
      _ ≤ |C| * sobNorm σ S (w - v) := mul_le_mul_of_nonneg_right (le_abs_self C) (sobNorm_nonneg _ _ _)
      _ ≤ |C| * δ := mul_le_mul_of_nonneg_left hd.le (abs_nonneg C)
  have hpos : 0 < p i (Φ w) := lt_of_le_of_ne (apply_nonneg _ _) (Ne.symm hi)
  set x := p i (Φ w) with hx
  have h1 := key (x / (2 * (|C| + 1))) (by positivity)
  have h2 : |C| * (x / (2 * (|C| + 1))) < x := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg C]
  linarith

end ZeroOnDense

theorem d0 : D0 := by
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ hD T hT h0
  exact ZeroOnDense.zero_on hπ.withSeminorms hD T (fun x y _ _ => map_sub T x y) hT h0

end PositivityTheory.CW

end
