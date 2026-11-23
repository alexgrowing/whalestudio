import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StrYMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.framePoint_fiber_nonempty :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∀ (Q : Type) [CommRing Q] [Algebra k Q] (ρ : NRep F 2 Q), ρ.IsBar (algebraMap k Q) → ρ.triM = ⊥ → (∀ i j, IsLocallyConstant fun g => ρ.r g i j) → (fun g => ρ.r g 1 0) ∈ F.strS Q := by
  intro l _ k _ _ F C₀ hF Q _ _ ρ hbar htri hlc
  have hd0 : ∀ g : F.G0, ρ.r g 0 0 = algebraMap k Q ((F.Ψ (g : F.Γ) : k)) := by
    intro g
    have h := hbar.1 g 0
    simpa [w] using h
  have hd1 : ∀ g : F.G0, ρ.r g 1 1 = algebraMap k Q ((F.Ψ (g : F.Γ) : k))⁻¹ := by
    intro g
    have h := hbar.1 g 1
    simpa [w] using h
  have hup : ∀ g : F.G0, ρ.r g 0 1 = 0 := by
    intro g
    have h : ρ.r g 0 1 ∈ ρ.triM := Ideal.subset_span ⟨g, 0, 1, by decide, rfl⟩
    rw [htri, Ideal.mem_bot] at h
    exact h
  have hψ0 : ∀ v (s : F.Gv v), ((ρ.ψ v 0 s : Qˣ) : Q) = algebraMap k Q ((F.Ψ (F.loc v s) : k)) := by
    intro v s
    have h := hbar.2 v 0 s
    simpa [w] using h
  have hψ1 : ∀ v (s : F.Gv v), ((ρ.ψ v 1 s : Qˣ) : Q) = algebraMap k Q ((F.Ψ (F.loc v s) : k))⁻¹ := by
    intro v s
    have h := hbar.2 v 1 s
    simpa [w] using h
  refine ⟨hlc 1 0, ?_, ?_, ?_⟩
  · intro g h
    simp only [map_mul, Matrix.mul_apply, Fin.sum_univ_two, Algebra.smul_def, Units.val_inv_eq_inv_val]
    rw [hd0, hd1]
    ring
  · intro g
    show ρ.r (F.star g) 1 0 = ρ.r g 1 0
    rw [(UpperTheory.V.Fr.star hF).2.2.2.2 ρ g 1 0]
    rfl
  · intro v
    obtain ⟨t, ht⟩ := hF.f3 v
    set d : k := ((F.Ψ (F.loc v t) : k)) - ((F.Ψ (F.loc v t) : k))⁻¹ with hdd
    have hne := Units.ne_zero (F.Ψ (F.loc v t))
    have hd : d ≠ 0 := by
      intro h
      apply ht
      rw [hdd, sub_eq_zero] at h
      rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, pow_two]
      calc ((F.Ψ (F.loc v t) : k)) * (F.Ψ (F.loc v t) : k)
          = (F.Ψ (F.loc v t) : k) * ((F.Ψ (F.loc v t) : k))⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ hne
    refine ⟨algebraMap k Q d⁻¹ * ρ.r (F.loc0 v t) 1 0, fun s => ?_⟩
    have h10 := congrFun (congrFun (ρ.ord v ![s, t]) 1) 0
    simp only [ordProd, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.succ_zero_eq_one, (by decide : (1 : Fin 2) ≠ 0), if_false, if_true, smul_zero,
      sub_zero, smul_eq_mul, mul_one] at h10
    have hl : ∀ s, ((F.loc0 v s : F.G0) : F.Γ) = F.loc v s := fun _ => rfl
    rw [hd0, hd1, hψ0, hψ1, hl, hl] at h10
    simp only [mul_zero, sub_zero] at h10
    have hinv : (algebraMap k Q ((F.Ψ (F.loc v t) : k)) - algebraMap k Q ((F.Ψ (F.loc v t) : k))⁻¹)
        * algebraMap k Q d⁻¹ = 1 := by
      rw [← map_sub, ← map_mul, ← hdd, mul_inv_cancel₀ hd, map_one]
    simp only [Algebra.smul_def, Units.val_inv_eq_inv_val, map_sub]
    linear_combination algebraMap k Q d⁻¹ * h10 - ρ.r (F.loc0 v s) 1 0 * hinv
