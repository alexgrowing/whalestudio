import Mathlib

noncomputable def UpperTheory.Reformulated.B.Yhb9.DenLE :
    {V H : Type} →
      [inst : MeasurableSpace V] →
        [inst_1 : MeasurableSpace H] → MeasureTheory.Measure V → MeasureTheory.Measure H → (V → H) → Set V → ENNReal → Prop :=
    fun {V H : Type} [MeasurableSpace V] [MeasurableSpace H] (μ : MeasureTheory.Measure V) (ν : MeasureTheory.Measure H)
        (q : V → H) (S : Set V) (C : ENNReal) ↦
      ∀ (Y : Set H), MeasurableSet Y → (μ : Set V → ENNReal) (S ∩ q ⁻¹' Y) ≤ C * (ν : Set H → ENNReal) Y

theorem UpperTheory.Reformulated.B.Yhb9.main :
    ∀ {V H : Type} [inst : MeasurableSpace V] [inst_1 : MeasurableSpace H] {μ : MeasureTheory.Measure V}
      {ν : MeasureTheory.Measure H} {q : V → H} {T : V → V} {τ : H → H},
      MeasurableEmbedding T →
        Measurable τ →
          (∀ (X : V), q (T X) = τ (q X)) →
            ∀ {a c : NNReal},
              a ≠ (0 : NNReal) →
                MeasureTheory.Measure.map T μ = a • μ →
                  MeasureTheory.Measure.map τ ν = c • ν →
                    ∀ {S : Set V} {C : ENNReal},
                      UpperTheory.Reformulated.B.Yhb9.DenLE μ ν q S C → UpperTheory.Reformulated.B.Yhb9.DenLE μ ν q (T '' S) ((↑(a⁻¹ * c) : ENNReal) * C) := by
  intro V H _ _ μ ν q T τ hT hτ hq a c ha hTμ hτν S C hS Y hY
  have h1 : T ⁻¹' (T '' S ∩ q ⁻¹' Y) = S ∩ q ⁻¹' (τ ⁻¹' Y) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_inter_iff, hT.injective.mem_set_image, hq]
  have h2 : (a : ENNReal) * μ (T '' S ∩ q ⁻¹' Y) = μ (S ∩ q ⁻¹' (τ ⁻¹' Y)) := by
    have := congrArg (fun m => m (T '' S ∩ q ⁻¹' Y)) hTμ
    rw [hT.map_apply, h1, MeasureTheory.Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at this
    exact this.symm
  have h3 : ν (τ ⁻¹' Y) = (c : ENNReal) * ν Y := by
    have := congrArg (fun m => m Y) hτν
    rw [MeasureTheory.Measure.map_apply hτ hY, MeasureTheory.Measure.smul_apply,
      ENNReal.smul_def, smul_eq_mul] at this
    exact this
  have h4 := hS (τ ⁻¹' Y) (hτ hY)
  rw [h3, ← h2] at h4
  have ha' : (a : ENNReal) ≠ 0 := by exact_mod_cast ha
  calc μ (T '' S ∩ q ⁻¹' Y) = (a : ENNReal)⁻¹ * ((a : ENNReal) * μ (T '' S ∩ q ⁻¹' Y)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel ha' ENNReal.coe_ne_top, one_mul]
    _ ≤ (a : ENNReal)⁻¹ * (C * ((c : ENNReal) * ν Y)) := by gcongr
    _ = _ := by rw [ENNReal.coe_mul, ENNReal.coe_inv ha]; ring
