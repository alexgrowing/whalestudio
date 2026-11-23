import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.Bridge

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem decSm_of_decBoundJ {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : Formalism.MainNotions.S.IsCayleyU k r ε P) {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} (m N : ℕ)
    (hJ : DecBoundJ ε (fun g => σ (P⁻¹ * g * P)) m N) :
    ∃ (C : ℝ) (Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))),
      (∀ w ∈ Ws, w.length ≤ N ∧ ∀ X ∈ w, Formalism.MainNotions.S.InLieHpk k r X) ∧
      ∀ u ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ, ∀ v ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ,
        ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
          Formalism.FourierDecayAlt.B.gN (k := k) (r := r) g ^ m * ‖inner ℂ v (σ g u)‖ ≤
            C * (Ws.map fun w => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w u‖).sum *
              (Ws.map fun w => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v‖).sum := by
  obtain ⟨hinv, -, -, -⟩ := br_facts hP
  have hPPi : P * P⁻¹ = 1 := by
    rw [hinv]; exact (br_facts hP).2.1
  have hPiP : P⁻¹ * P = 1 := by
    rw [hinv]; exact (br_facts hP).2.2.1
  have hconj : ∀ X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      P * (P⁻¹ * X * P) * P⁻¹ = X := by
    intro X
    calc P * (P⁻¹ * X * P) * P⁻¹ = (P * P⁻¹) * X * (P * P⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = X := by rw [hPPi, Matrix.one_mul, Matrix.mul_one]
  have hconj' : ∀ g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      P⁻¹ * (P * g * P⁻¹) * P = g := by
    intro g
    calc P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) := by
          simp only [Matrix.mul_assoc]
      _ = g := by rw [hPiP, Matrix.one_mul, Matrix.mul_one]
  have hmapid : ∀ w : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
      ((w.map fun X => P⁻¹ * X * P).map fun X => P * X * P⁻¹) = w := by
    intro w
    rw [List.map_map]
    conv_rhs => rw [← List.map_id w]
    exact List.map_congr_left (fun X _ => hconj X)
  obtain ⟨C, Ws, hWs, hb⟩ := hJ
  refine ⟨C, Ws.map fun w => w.map fun X => P⁻¹ * X * P, ?_, ?_⟩
  · intro w' hw'
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hw'
    refine ⟨by rw [List.length_map]; exact (hWs w hw).1, ?_⟩
    intro X' hX'
    obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hX'
    rw [bridge_lie hP, hconj]
    exact (hWs w hw).2 X hX
  · intro u hu v hv g hg
    have hsum : ∀ x : H,
        ((Ws.map fun w => w.map fun X => P⁻¹ * X * P).map
            fun w => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w x‖).sum = nuJ (fun g => σ (P⁻¹ * g * P)) Ws x := by
      intro x
      unfold nuJ
      rw [List.map_map]
      congr 1
      refine List.map_congr_left (fun w _ => ?_)
      simp only [Function.comp_apply]
      rw [bridge_dsigW hP, hmapid]
    have key := hb u v ((bridge_smooth hP σ u).1 hu) ((bridge_smooth hP σ v).1 hv)
      (P * g * P⁻¹) ((bridge_group hP g).1 hg)
    simp only [] at key
    rw [hconj'] at key
    rw [hsum, hsum, bridge_gN hP]
    exact key

end ReciprocityTheory.ChartRestriction.DS.DecInf
