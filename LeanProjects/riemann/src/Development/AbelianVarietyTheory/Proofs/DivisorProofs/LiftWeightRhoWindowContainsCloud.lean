import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightCombinatorialDataULeUZero
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift

theorem GlobalTheory.ExpTie.Lift.window_cloud : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau), GlobalTheory.ExpTie.Lift.ValsAt L j τ → ((GlobalTheory.ExpTie.Lift.wts L j).c τ ≤ ((GlobalTheory.ExpTie.Lift.wts L j).xm τ : ℝ) ∧ (GlobalTheory.ExpTie.Lift.wts L j).xm τ ≤ (GlobalTheory.ExpTie.Lift.wts L j).xp τ ∧ ((GlobalTheory.ExpTie.Lift.wts L j).xp τ : ℝ) ≤ (GlobalTheory.ExpTie.Lift.wts L j).c τ + (GlobalTheory.ExpTie.parOf L j).S) ∧ ∀ a, a < Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) → (GlobalTheory.ExpTie.Lift.wts L j).xm τ ≤ (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ∧ (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ≤ (GlobalTheory.ExpTie.Lift.wts L j).xp τ := by
  intro D L j τ hv
  have hS : (GlobalTheory.ExpTie.parOf L j).S = L.Sc := rfl
  have hkc : Formalism.CohomologicalDescent.ShortWeightBounds.kc (GlobalTheory.ExpTie.parOf L j) = D.R.k - 1 := rfl
  have hxm : (GlobalTheory.ExpTie.Lift.wts L j).xm τ = ⌈(GlobalTheory.ExpTie.Lift.wts L j).c τ⌉ := rfl
  have hxp : (GlobalTheory.ExpTie.Lift.wts L j).xp τ = ⌊(GlobalTheory.ExpTie.Lift.wts L j).c τ + L.Sc⌋ := rfl

  have hrow : ∀ a, a < D.R.k - 1 →
      (GlobalTheory.ExpTie.Lift.wts L j).xm τ ≤ (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ∧
        (GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a ≤ (GlobalTheory.ExpTie.Lift.wts L j).xp τ := by
    intro a ha
    have h1 := hv.1 a ha
    have h2 := L.cloud_v τ ⟨a, ha⟩
    have hlo : (GlobalTheory.ExpTie.Lift.wts L j).c τ ≤ ((GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a : ℝ) := by
      have : (0 : ℝ) ≤ (((D.hc τ).v ⟨a, ha⟩ : ℚ) : ℝ) := by exact_mod_cast h2.1
      linarith
    have hhi : ((GlobalTheory.ExpTie.Lift.wts L j).U (GlobalTheory.ExpTie.parOf L j) τ a : ℝ) ≤ (GlobalTheory.ExpTie.Lift.wts L j).c τ + L.Sc := by
      have : (((D.hc τ).v ⟨a, ha⟩ : ℚ) : ℝ) ≤ L.Sc := by exact_mod_cast h2.2
      linarith
    rw [hxm, hxp]
    exact ⟨Int.ceil_le.2 hlo, Int.le_floor.2 hhi⟩
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have h0 := hrow 0 (by omega)
  refine ⟨⟨?_, le_trans h0.1 h0.2, ?_⟩, ?_⟩
  · rw [hxm]; exact Int.le_ceil _
  · rw [hxp, hS]; exact Int.floor_le _
  · intro a ha
    rw [hkc] at ha
    exact hrow a ha
