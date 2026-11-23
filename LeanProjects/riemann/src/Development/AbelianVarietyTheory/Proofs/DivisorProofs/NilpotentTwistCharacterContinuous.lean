import Mathlib

namespace GlobalTheory

open Matrix

theorem scalar_eq_zero_of_isNilpotent_smul_one {d : ℕ} (hd : 0 < d) {c : ℂ}
    (h : IsNilpotent (c • (1 : Matrix (Fin d) (Fin d) ℂ))) : c = 0 := by
  obtain ⟨n, hn⟩ := h
  have h0 := congrFun (congrFun hn ⟨0, hd⟩) ⟨0, hd⟩
  rw [smul_pow, one_pow] at h0
  simp at h0
  exact h0.1

theorem scalar_part_character :
    ∀ (G : Type) [CommGroup G] [TopologicalSpace G] (H : Set G) (d : ℕ)
      (ρ : G →* Matrix (Fin d) (Fin d) ℂ) (χ : G → ℂ), 0 < d →
      (∀ s, IsNilpotent (ρ s - χ s • (1 : Matrix (Fin d) (Fin d) ℂ))) →
      (∀ γ ∈ H, ρ γ = 1) → (∀ i j, Continuous fun s => ρ s i j) →
      ∃ lam : G →* ℂˣ, (∀ s, ((lam s : ℂˣ) : ℂ) = χ s) ∧
        Continuous (fun s => ((lam s : ℂˣ) : ℂ)) ∧ ∀ γ ∈ H, lam γ = 1 := by
  intro G _ _ H d ρ χ hd hnil hH hcont

  have key : ∀ c : ℂ, IsNilpotent (c • (1 : Matrix (Fin d) (Fin d) ℂ)) → c = 0 :=
    fun c h => scalar_eq_zero_of_isNilpotent_smul_one hd h

  have htr : ∀ s, χ s = trace (ρ s) / (d : ℂ) := by
    intro s
    have h1 : IsNilpotent (trace (ρ s - χ s • (1 : Matrix (Fin d) (Fin d) ℂ))) :=
      Matrix.isNilpotent_trace_of_isNilpotent (hnil s)
    have h2 := h1.eq_zero
    rw [trace_sub, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul] at h2
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp
    linear_combination -h2
  have hχ1 : χ 1 = 1 := by
    have h := hnil 1
    rw [map_one] at h
    have : (1 : Matrix (Fin d) (Fin d) ℂ) - χ 1 • 1 = (1 - χ 1) • 1 := by
      rw [sub_smul, one_smul]
    rw [this] at h
    have := key _ h
    linear_combination -this
  have hmul : ∀ s t, χ (s * t) = χ s * χ t := by
    intro s t
    have hc : Commute (ρ s) (ρ t) := by
      show ρ s * ρ t = ρ t * ρ s
      rw [← map_mul, ← map_mul, mul_comm]
    set A := ρ s - χ s • (1 : Matrix (Fin d) (Fin d) ℂ)
    set B := ρ t - χ t • (1 : Matrix (Fin d) (Fin d) ℂ)
    have hAt : Commute A (ρ t) := by
      simp only [A]
      exact (hc.sub_left ((Commute.one_left _).smul_left _))
    have hAB : Commute (A * ρ t) (χ s • B) := by
      simp only [B]
      refine Commute.smul_right ?_ _
      refine Commute.sub_right ?_ ((Commute.one_right _).smul_right _)
      exact Commute.mul_left hAt (Commute.refl _)
    have hN1 : IsNilpotent (A * ρ t + χ s • B) := by
      refine Commute.isNilpotent_add hAB ?_ ?_
      · exact Commute.isNilpotent_mul_right hAt (hnil s)
      · exact (hnil t).smul _
    have heq1 : A * ρ t + χ s • B = ρ (s * t) - (χ s * χ t) • 1 := by
      simp only [A, B, map_mul, sub_mul, smul_mul_assoc, one_mul, smul_sub, mul_smul]
      abel
    rw [heq1] at hN1
    have hN2 := hnil (s * t)
    have hcomm : Commute (ρ (s * t) - (χ s * χ t) • (1 : Matrix (Fin d) (Fin d) ℂ))
        (ρ (s * t) - χ (s * t) • 1) := by
      refine Commute.sub_left ?_ ((Commute.one_left _).smul_left _)
      exact Commute.sub_right (Commute.refl _) ((Commute.one_right _).smul_right _)
    have hN3 := Commute.isNilpotent_sub hcomm hN1 hN2
    have : (ρ (s * t) - (χ s * χ t) • (1 : Matrix (Fin d) (Fin d) ℂ)) - (ρ (s * t) - χ (s * t) • 1)
        = (χ (s * t) - χ s * χ t) • 1 := by
      rw [sub_smul]; abel
    rw [this] at hN3
    have := key _ hN3
    linear_combination this
  let m : G →* ℂ := { toFun := χ, map_one' := hχ1, map_mul' := hmul }
  have hne : ∀ s, χ s ≠ 0 := by
    intro s h
    have := hmul s s⁻¹
    rw [mul_inv_cancel, hχ1, h, zero_mul] at this
    exact one_ne_zero this
  let lam : G →* ℂˣ := m.toHomUnits
  refine ⟨lam, fun s => rfl, ?_, ?_⟩
  · show Continuous χ
    have : χ = fun s => trace (ρ s) / (d : ℂ) := funext htr
    rw [this]
    refine Continuous.div_const ?_ _
    simp only [Matrix.trace, Matrix.diag]
    exact continuous_finset_sum _ (fun i _ => hcont i i)
  · intro γ hγ
    apply Units.ext
    show χ γ = 1
    have h := hnil γ
    rw [hH γ hγ] at h
    have : (1 : Matrix (Fin d) (Fin d) ℂ) - χ γ • 1 = (1 - χ γ) • 1 := by
      rw [sub_smul, one_smul]
    rw [this] at h
    have := key _ h
    linear_combination -this

end GlobalTheory
