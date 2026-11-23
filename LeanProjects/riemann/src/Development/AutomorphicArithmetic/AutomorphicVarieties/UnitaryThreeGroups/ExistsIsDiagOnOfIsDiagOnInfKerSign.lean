import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes

open Matrix UpperTheory.V

private theorem exists_char {Γ k : Type} [Group Γ] [Field k] (η : Γ →* ℤˣ) (Φ : Γ →* kˣ) (s : Γ) (hs : η s = -1)
    (x : k) (hx : x * x = (Φ s : k) * Φ s) :
    ∃ χ : Γ →* kˣ, (∀ g, η g = 1 → χ g = Φ g) ∧ (χ s : k) = x := by
  have hΦ : (Φ s : k) ≠ 0 := (Φ s).ne_zero
  have hsq : (x / Φ s) * (x / Φ s) = 1 := by
    rw [div_mul_div_comm, hx, div_self (mul_ne_zero hΦ hΦ)]
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · exact ⟨Φ, fun g _ => rfl, ((div_eq_one_iff_eq hΦ).mp h).symm⟩
  · refine ⟨Φ * (Units.map (Int.castRingHom k).toMonoidHom).comp η, fun g hg => by simp [hg], ?_⟩
    rw [div_eq_iff hΦ] at h
    simp [hs, h]

private theorem diag_sq {k : Type} [Field k] [CharZero k] (S : Matrix (Fin 2) (Fin 2) k) (a : k) (ha : a ≠ 0)
    (hS : S * S = Matrix.diagonal fun _ => a * a) :
    ∃ (P : GL (Fin 2) k) (x : Fin 2 → k), (∀ i, x i * x i = a * a) ∧
      (P : Matrix (Fin 2) (Fin 2) k) * S = Matrix.diagonal x * P := by
  have e : ∀ i j, (S * S) i j = (Matrix.diagonal fun _ : Fin 2 => a * a) i j := fun i j => by rw [hS]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal] at e00 e01 e10 e11
  have h2 : (2 : k) ≠ 0 := two_ne_zero
  by_cases hr : S 1 0 = 0
  · by_cases hq : S 0 1 = 0
    · refine ⟨1, ![S 0 0, S 1 1], ?_, ?_⟩
      · intro i
        fin_cases i
        · simp
          linear_combination e00 - S 1 0 * hq
        · simp
          linear_combination e11 - S 0 1 * hr
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [hq, hr]
    · have ht : S 1 1 = -S 0 0 := by
        have : S 0 1 * (S 0 0 + S 1 1) = 0 := by linear_combination e01
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hq
        · linear_combination h
      have hp2 : S 0 0 * S 0 0 = a * a := by linear_combination e00 - S 0 1 * hr
      have hp : S 0 0 ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hp2
        exact mul_ne_zero ha ha hp2.symm
      have hd : Matrix.det !![2 * S 0 0, S 0 1; 0, 1] ≠ 0 := by
        rw [Matrix.det_fin_two_of]
        simpa using mul_ne_zero h2 hp
      refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, ![S 0 0, -S 0 0], ?_, ?_⟩
      · intro i
        fin_cases i <;> simpa using hp2
      · show !![2 * S 0 0, S 0 1; 0, 1] * S = Matrix.diagonal ![S 0 0, -S 0 0] * !![2 * S 0 0, S 0 1; 0, 1]
        ext i j
        fin_cases i <;> fin_cases j
        · simp [Matrix.mul_apply, Fin.sum_univ_two]
          linear_combination S 0 1 * hr
        · simp [Matrix.mul_apply, Fin.sum_univ_two]
          linear_combination S 0 1 * ht
        · simp [Matrix.mul_apply, Fin.sum_univ_two]
          linear_combination hr
        · simp [Matrix.mul_apply, Fin.sum_univ_two]
          linear_combination ht
  · have ht : S 1 1 = -S 0 0 := by
      have : S 1 0 * (S 0 0 + S 1 1) = 0 := by linear_combination e10
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hr
      · linear_combination h
    have hd : Matrix.det !![S 1 0, a - S 0 0; S 1 0, -a - S 0 0] ≠ 0 := by
      rw [Matrix.det_fin_two_of]
      have : S 1 0 * (-a - S 0 0) - (a - S 0 0) * S 1 0 = -(2 * (a * S 1 0)) := by ring
      rw [this, neg_ne_zero]
      exact mul_ne_zero h2 (mul_ne_zero ha hr)
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, ![a, -a], ?_, ?_⟩
    · intro i
      fin_cases i <;> simp
    · show !![S 1 0, a - S 0 0; S 1 0, -a - S 0 0] * S = Matrix.diagonal ![a, -a] * !![S 1 0, a - S 0 0; S 1 0, -a - S 0 0]
      ext i j
      fin_cases i <;> fin_cases j
      · simp [Matrix.mul_apply, Fin.sum_univ_two]
        ring
      · simp [Matrix.mul_apply, Fin.sum_univ_two]
        linear_combination e00 + (a - S 0 0) * ht
      · simp [Matrix.mul_apply, Fin.sum_univ_two]
        ring
      · simp [Matrix.mul_apply, Fin.sum_univ_two]
        linear_combination e00 + (-a - S 0 0) * ht

private theorem diag_ext {Γ k : Type} [Group Γ] [Field k] (H : Subgroup Γ) (η : Γ →* ℤˣ) (W : Γ →* GL (Fin 2) k)
    (χ : Fin 2 → Γ →* kˣ) (g : GL (Fin 2) k) (s : Γ) (hsH : s ∈ H) (hs : η s = -1)
    (h0 : ∀ t ∈ H, η t = 1 → ((g * W t * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      Matrix.diagonal fun i => (χ i t : k))
    (h1 : ((g * W s * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = Matrix.diagonal fun i => (χ i s : k)) :
    Af.IsDiagOn W H χ := by
  refine ⟨g, fun t ht => ?_⟩
  rcases Int.units_eq_one_or (η t) with h | h
  · exact h0 t ht h
  · have hu : s⁻¹ * t ∈ H := H.mul_mem (H.inv_mem hsH) ht
    have hη : η (s⁻¹ * t) = 1 := by simp [hs, h]
    have key : g * W t * g⁻¹ = (g * W s * g⁻¹) * (g * W (s⁻¹ * t) * g⁻¹) := by
      rw [map_mul, map_inv]; group
    rw [key, Units.val_mul, h1, h0 _ hu hη, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel_left]

theorem UpperTheory.exists_isDiagOn_of_isDiagOn_inf_ker_sign :
    ∀ {Γ k : Type} [Group Γ] [Field k] [CharZero k] (H : Subgroup Γ) (η : Γ →* ℤˣ) (W : Γ →* GL (Fin 2) k) (Ψ : Γ →* kˣ), Af.IsDiagOn W (H ⊓ η.ker) ![Ψ, Ψ⁻¹] → ∃ χ : Fin 2 → Γ →* kˣ, (∀ i g, Ψ g = 1 → η g = 1 → χ i g = 1) ∧ Af.IsDiagOn W H χ := by
  intro Γ k _ _ _ H η W Ψ hD
  obtain ⟨g, hg⟩ := hD
  by_cases hex : ∃ s ∈ H, η s = -1
  swap
  · push_neg at hex
    refine ⟨![Ψ, Ψ⁻¹], ?_, g, fun t ht => hg t ⟨ht, MonoidHom.mem_ker.mpr ?_⟩⟩
    · intro i x hΨ _
      fin_cases i <;> simp [hΨ]
    · rcases Int.units_eq_one_or (η t) with h | h
      · exact h
      · exact absurd h (hex t ht)
  obtain ⟨s, hsH, hs⟩ := hex
  have hmul : ∀ a b : Γ, ((g * W (a * b) * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      ((g * W a * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *
        ((g * W b * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) := by
    intro a b
    rw [← Units.val_mul, map_mul]
    congr 1
    group
  have hconj : ∀ (φ : Γ →* kˣ) (t : Γ), φ (s * t * s⁻¹) = φ t := by
    intro φ t
    rw [map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]
  have hmemk : ∀ t, t ∈ H ⊓ η.ker ↔ t ∈ H ∧ η t = 1 := fun t => by
    simp [Subgroup.mem_inf, MonoidHom.mem_ker]
  have hss : s * s ∈ H ⊓ η.ker := (hmemk _).mpr ⟨H.mul_mem hsH hsH, by rw [map_mul, hs]; decide⟩
  have hcomm : ∀ t ∈ H ⊓ η.ker, ((g * W s * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *
      Matrix.diagonal (fun i => ((![Ψ, Ψ⁻¹] i t : kˣ) : k)) =
      Matrix.diagonal (fun i => ((![Ψ, Ψ⁻¹] i t : kˣ) : k)) *
        ((g * W s * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) := by
    intro t ht
    obtain ⟨htH, htk⟩ := (hmemk t).mp ht
    have hm : s * t * s⁻¹ ∈ H ⊓ η.ker :=
      (hmemk _).mpr ⟨H.mul_mem (H.mul_mem hsH htH) (H.inv_mem hsH), by simp [htk]⟩
    have e2 := hg _ hm
    simp only [hconj] at e2
    conv_rhs => rw [← e2]
    rw [← hg t ht, ← hmul, ← hmul, inv_mul_cancel_right]
  obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin 2) (Fin 2) k,
      ((g * W s * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = S := ⟨_, rfl⟩
  have hSS : S * S = Matrix.diagonal (fun i => ((![Ψ, Ψ⁻¹] i (s * s) : kˣ) : k)) := by
    rw [← hS, ← hmul, hg _ hss]
  by_cases hdist : ∃ t ∈ H ⊓ η.ker, ((Ψ t : kˣ) : k) ≠ (((Ψ⁻¹) t : kˣ) : k)
  · obtain ⟨t0, ht0, hne⟩ := hdist
    have hc := hcomm t0 ht0
    rw [hS] at hc
    have c01 := congrFun (congrFun hc 0) 1
    have c10 := congrFun (congrFun hc 1) 0
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] at c01 c10
    have h01 : S 0 1 = 0 := by
      have : S 0 1 * (((Ψ t0 : kˣ) : k) - (((Ψ⁻¹) t0 : kˣ) : k)) = 0 := by linear_combination -c01
      exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
    have h10 : S 1 0 = 0 := by
      have : S 1 0 * (((Ψ t0 : kˣ) : k) - (((Ψ⁻¹) t0 : kˣ) : k)) = 0 := by linear_combination c10
      exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
    have d0 := congrFun (congrFun hSS 0) 0
    have d1 := congrFun (congrFun hSS 1) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply_eq, h01, h10, mul_zero,
      add_zero, zero_mul, zero_add, map_mul, Units.val_mul] at d0 d1
    have hxi : ∀ i, S i i * S i i = ((![Ψ, Ψ⁻¹] i s : kˣ) : k) * ((![Ψ, Ψ⁻¹] i s : kˣ) : k) := by
      intro i
      fin_cases i
      · exact d0
      · exact d1
    choose χ hχ1 hχ2 using fun i => exists_char η (![Ψ, Ψ⁻¹] i) s hs (S i i) (hxi i)
    refine ⟨χ, ?_, diag_ext H η W χ g s hsH hs ?_ ?_⟩
    · intro i x hΨ hη
      rw [hχ1 i x hη]
      fin_cases i <;> simp [hΨ]
    · intro t htH htη
      rw [hg t ((hmemk t).mpr ⟨htH, htη⟩)]
      congr 1
      funext i
      rw [hχ1 i t htη]
    · rw [hS]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, hχ2, h01, h10]
  · push_neg at hdist
    have hDt : ∀ t ∈ H ⊓ η.ker, Matrix.diagonal (fun i => ((![Ψ, Ψ⁻¹] i t : kˣ) : k)) =
        Matrix.diagonal (fun _ => ((Ψ t : kˣ) : k)) := by
      intro t ht
      congr 1
      funext i
      fin_cases i
      · rfl
      · exact (hdist t ht).symm
    have hSS' : S * S = Matrix.diagonal (fun _ => ((Ψ s : kˣ) : k) * ((Ψ s : kˣ) : k)) := by
      rw [hSS, hDt _ hss, map_mul, Units.val_mul]
    obtain ⟨P, x, hx, hP⟩ := diag_sq S _ (Ψ s).ne_zero hSS'
    choose χ hχ1 hχ2 using fun i => exists_char η Ψ s hs (x i) (hx i)
    have hconjP : ∀ t, (((P * g) * W t * (P * g)⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
        (P : Matrix (Fin 2) (Fin 2) k) * ((g * W t * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *
          ((P⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) := by
      intro t
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    have hPinv : (P : Matrix (Fin 2) (Fin 2) k) * ((P⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    refine ⟨χ, ?_, diag_ext H η W χ (P * g) s hsH hs ?_ ?_⟩
    · intro i y hΨ hη
      rw [hχ1 i y hη, hΨ]
    · intro t htH htη
      have ht : t ∈ H ⊓ η.ker := (hmemk t).mpr ⟨htH, htη⟩
      have hsc : (P : Matrix (Fin 2) (Fin 2) k) * Matrix.diagonal (fun _ => ((Ψ t : kˣ) : k)) =
          Matrix.diagonal (fun _ => ((Ψ t : kˣ) : k)) * (P : Matrix (Fin 2) (Fin 2) k) := by
        ext i j
        simp [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]
      rw [hconjP, hg t ht, hDt t ht, hsc, mul_assoc, hPinv, mul_one]
      congr 1
      funext i
      rw [hχ1 i t htη]
    · rw [hconjP, hS, hP, mul_assoc, hPinv, mul_one]
      congr 1
      funext i
      rw [hχ2 i]
