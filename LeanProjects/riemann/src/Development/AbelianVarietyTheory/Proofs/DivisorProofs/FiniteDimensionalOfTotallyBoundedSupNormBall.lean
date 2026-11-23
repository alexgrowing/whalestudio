import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology

namespace GlobalTheory

theorem finiteDimensional_of_totallyBounded_supBall :
    ∀ (T : Type) (V : Submodule ℂ (T → ℂ)) (B : Set T), (∀ φ ∈ V, (∀ x ∈ B, φ x = 0) → φ = 0) →
      (∀ φ ∈ V, ∃ M : ℝ, ∀ x ∈ B, ‖φ x‖ ≤ M) →
      (∀ ε : ℝ, 0 < ε → ∃ F : Finset (T → ℂ), ∀ φ ∈ V, (∀ x ∈ B, ‖φ x‖ ≤ 1) →
        ∃ ψ ∈ F, ∀ x ∈ B, ‖φ x - ψ x‖ ≤ ε) → FiniteDimensional ℂ V := by
  intro T V B hinj hbdd htb
  classical
  have hmem : ∀ φ : V, Memℓp (fun x : B => (φ : T → ℂ) x) (⊤ : ENNReal) := by
    intro φ
    obtain ⟨M, hM⟩ := hbdd φ φ.2
    apply memℓp_infty
    refine ⟨M, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hM x x.2
  let L : V →ₗ[ℂ] lp (fun _ : B => ℂ) (⊤ : ENNReal) :=
    { toFun := fun φ => ⟨fun x : B => (φ : T → ℂ) x, hmem φ⟩
      map_add' := fun φ ψ => lp.ext (funext fun _ => rfl)
      map_smul' := fun c φ => lp.ext (funext fun _ => rfl) }
  have hLapp : ∀ (φ : V) (x : B), (L φ) x = (φ : T → ℂ) x := fun _ _ => rfl
  have hL : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).2 fun φ hφ => ?_
    have h0 : ∀ x ∈ B, (φ : T → ℂ) x = 0 := by
      intro x hx
      rw [← hLapp φ ⟨x, hx⟩, hφ]
      rfl
    exact Subtype.ext (hinj φ φ.2 h0)
  haveI : FiniteDimensional ℂ (LinearMap.range L) := by
    by_contra hfin
    obtain ⟨R, f, hR, hfR, hsep⟩ := exists_seq_norm_le_one_le_norm_sub hfin
    have hRpos : 0 < R := by linarith
    obtain ⟨F, hF⟩ := htb (1 / (3 * R)) (by positivity)
    have hpre : ∀ n, ∃ φ : V, L φ = (f n : lp (fun _ : B => ℂ) (⊤ : ENNReal)) := fun n => (f n).2
    choose φ hφ using hpre
    have hφle : ∀ n, ∀ x ∈ B, ‖(φ n : T → ℂ) x‖ ≤ R := by
      intro n x hx
      rw [← hLapp (φ n) ⟨x, hx⟩, hφ n]
      exact (lp.norm_apply_le_norm ENNReal.top_ne_zero _ _).trans (hfR n)
    have hball : ∀ n, ∀ x ∈ B, ‖((R : ℂ)⁻¹ • (φ n : T → ℂ)) x‖ ≤ 1 := by
      intro n x hx
      rw [Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hRpos.le]
      rw [inv_mul_le_iff₀ hRpos, mul_one]
      exact hφle n x hx
    have hch : ∀ n, ∃ ψ ∈ F, ∀ x ∈ B, ‖((R : ℂ)⁻¹ • (φ n : T → ℂ)) x - ψ x‖ ≤ 1 / (3 * R) :=
      fun n => hF _ (V.smul_mem _ (φ n).2) (hball n)
    choose ψ hψF hψ using hch
    obtain ⟨m, n, hmn, hmn'⟩ :=
      Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => (⟨ψ k, hψF k⟩ : F))
    have hψeq : ψ m = ψ n := congrArg Subtype.val hmn'
    have hpt : ∀ x ∈ B, ‖(φ m : T → ℂ) x - (φ n : T → ℂ) x‖ ≤ 2 / 3 := by
      intro x hx
      have h1 := hψ m x hx
      have h2 := hψ n x hx
      rw [hψeq] at h1
      have h3 : ‖((R : ℂ)⁻¹ • (φ m : T → ℂ)) x - ((R : ℂ)⁻¹ • (φ n : T → ℂ)) x‖ ≤ 2 / (3 * R) := by
        calc _ = ‖(((R : ℂ)⁻¹ • (φ m : T → ℂ)) x - ψ n x) - (((R : ℂ)⁻¹ • (φ n : T → ℂ)) x - ψ n x)‖ := by
                congr 1; ring
          _ ≤ _ := norm_sub_le _ _
          _ ≤ 1 / (3 * R) + 1 / (3 * R) := add_le_add h1 h2
          _ = 2 / (3 * R) := by ring
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_sub, norm_mul, norm_inv,
        Complex.norm_real, Real.norm_of_nonneg hRpos.le] at h3
      rw [inv_mul_le_iff₀ hRpos] at h3
      calc _ ≤ R * (2 / (3 * R)) := h3
        _ = 2 / 3 := by field_simp
    have hnorm : ‖f m - f n‖ ≤ 2 / 3 := by
      show ‖((f m : lp (fun _ : B => ℂ) (⊤ : ENNReal)) - (f n : lp (fun _ : B => ℂ) (⊤ : ENNReal)))‖ ≤ 2 / 3
      rw [← hφ m, ← hφ n]
      refine lp.norm_le_of_forall_le (by norm_num) fun x => ?_
      rw [lp.coeFn_sub, Pi.sub_apply, hLapp, hLapp]
      exact hpt x x.2
    have := hsep hmn
    linarith
  exact LinearEquiv.finiteDimensional (LinearEquiv.ofInjective L hL).symm

end GlobalTheory
