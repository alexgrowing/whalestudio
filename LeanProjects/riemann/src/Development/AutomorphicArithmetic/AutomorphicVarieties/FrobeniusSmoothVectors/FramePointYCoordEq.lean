import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StrYMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.framePoint_y_coord_eq :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∀ (Q : Type) [CommRing Q] [Algebra k Q] (ρ : NRep F 3 Q), ρ.IsBar (algebraMap k Q) → ρ.triM = ⊥ → (∀ i j, IsLocallyConstant fun g => ρ.r g i j) → (fun g => ρ.r g 1 0) ∈ F.strY Q := by
  intro l _ k _ _ F C₀ hF Q _ _ ρ hbar htri hlc
  have hd0 : ∀ g : F.G0, ρ.r g 0 0 = algebraMap k Q ((F.Ψ (g : F.Γ) : k)) := by
    intro g
    have h := hbar.1 g 0
    simpa [w] using h
  have hd1 : ∀ g : F.G0, ρ.r g 1 1 = 1 := by
    intro g
    have h := hbar.1 g 1
    simpa [w] using h
  have hd2 : ∀ g : F.G0, ρ.r g 2 2 = algebraMap k Q ((F.Ψ (g : F.Γ) : k))⁻¹ := by
    intro g
    have h := hbar.1 g 2
    simpa [w] using h
  have hup : ∀ (g : F.G0) (i j : Fin 3), i < j → ρ.r g i j = 0 := by
    intro g i j hij
    have h : ρ.r g i j ∈ ρ.triM := Ideal.subset_span ⟨g, i, j, hij, rfl⟩
    rw [htri, Ideal.mem_bot] at h
    exact h
  have h01 := fun g => hup g 0 1 (by decide)
  have h02 := fun g => hup g 0 2 (by decide)
  have h12 := fun g => hup g 1 2 (by decide)
  have hψ0 : ∀ v (s : F.Gv v), ((ρ.ψ v 0 s : Qˣ) : Q) = algebraMap k Q ((F.Ψ (F.loc v s) : k)) := by
    intro v s
    have h := hbar.2 v 0 s
    simpa [w] using h
  have hψ1 : ∀ v (s : F.Gv v), ((ρ.ψ v 1 s : Qˣ) : Q) = 1 := by
    intro v s
    have h := hbar.2 v 1 s
    simpa [w] using h
  have hψ2 : ∀ v (s : F.Gv v), ((ρ.ψ v 2 s : Qˣ) : Q) = algebraMap k Q ((F.Ψ (F.loc v s) : k))⁻¹ := by
    intro v s
    have h := hbar.2 v 2 s
    simpa [w] using h
  refine ⟨hlc 1 0, ?_, ?_, ?_, ?_⟩
  · intro g h
    simp only [map_mul, Matrix.mul_apply, Fin.sum_univ_three, Algebra.smul_def]
    rw [hd0, hd1, h12]
    ring
  · have h := ρ.diag 1 0 (by decide)
    rw [Matrix.sub_apply, sub_eq_zero] at h
    exact h
  · intro v
    obtain ⟨t, ht⟩ := hF.f3 v
    have hne := Units.ne_zero (F.Ψ (F.loc v t))
    have hsq : ((F.Ψ (F.loc v t) : k)) * (F.Ψ (F.loc v t) : k) ≠ 1 := by
      intro h
      apply ht
      rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, pow_two, h]
    have hf : ((F.Ψ (F.loc v t) : k)) - 1 ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      apply hsq
      rw [h, one_mul]
    have he : ((F.Ψ (F.loc v t) : k)) - ((F.Ψ (F.loc v t) : k))⁻¹ ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      apply hsq
      calc ((F.Ψ (F.loc v t) : k)) * (F.Ψ (F.loc v t) : k)
          = (F.Ψ (F.loc v t) : k) * ((F.Ψ (F.loc v t) : k))⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ hne
    have hl : ∀ s, ((F.loc0 v s : F.G0) : F.Γ) = F.loc v s := fun _ => rfl
    refine ⟨algebraMap k Q (((F.Ψ (F.loc v t) : k)) - 1)⁻¹ * ρ.r (F.loc0 v t) 1 0, fun s => ?_⟩
    have h10 := congrFun (congrFun (ρ.ord v ![t, s, t]) 1) 0
    simp [ordProd, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, hd0, hd1, hd2, h01, h02, h12,
      hψ0, hψ1, hψ2, hl] at h10
    simp only [Algebra.smul_def, mul_one] at h10
    have hE : (algebraMap k Q ((F.Ψ (F.loc v t) : k)) - algebraMap k Q ((F.Ψ (F.loc v t) : k))⁻¹) * algebraMap k Q (((F.Ψ (F.loc v t) : k)) - ((F.Ψ (F.loc v t) : k))⁻¹)⁻¹ = 1 := by
      rw [← map_sub, ← map_mul, mul_inv_cancel₀ he, map_one]
    have hF : (algebraMap k Q ((F.Ψ (F.loc v t) : k)) - 1) * algebraMap k Q (((F.Ψ (F.loc v t) : k)) - 1)⁻¹ = 1 := by
      rw [← map_one (algebraMap k Q), ← map_sub, ← map_mul, mul_inv_cancel₀ hf, map_one]
    simp only [Algebra.smul_def, map_sub, map_one]
    linear_combination (-(algebraMap k Q (((F.Ψ (F.loc v t) : k)) - ((F.Ψ (F.loc v t) : k))⁻¹)⁻¹ * algebraMap k Q (((F.Ψ (F.loc v t) : k)) - 1)⁻¹)) * h10
      + ((algebraMap k Q ((F.Ψ (F.loc v s) : k)) - 1) * algebraMap k Q (((F.Ψ (F.loc v t) : k)) - 1)⁻¹ * ρ.r (F.loc0 v t) 1 0 - ρ.r (F.loc0 v s) 1 0) * hE
      - algebraMap k Q (((F.Ψ (F.loc v t) : k)) - ((F.Ψ (F.loc v t) : k))⁻¹)⁻¹ * (algebraMap k Q ((F.Ψ (F.loc v t) : k)) - algebraMap k Q ((F.Ψ (F.loc v t) : k))⁻¹) * ρ.r (F.loc0 v s) 1 0 * hF
  · intro v
    obtain ⟨t, ht⟩ := hF.f3 v
    have hne := Units.ne_zero (F.Ψ (F.loc v t))
    have hsq : ((F.Ψ (F.loc v t) : k)) * (F.Ψ (F.loc v t) : k) ≠ 1 := by
      intro h
      apply ht
      rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, pow_two, h]
    have hf : ((F.Ψ (F.loc v t) : k)) - 1 ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      apply hsq
      rw [h, one_mul]
    have he : ((F.Ψ (F.loc v t) : k)) - ((F.Ψ (F.loc v t) : k))⁻¹ ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      apply hsq
      calc ((F.Ψ (F.loc v t) : k)) * (F.Ψ (F.loc v t) : k)
          = (F.Ψ (F.loc v t) : k) * ((F.Ψ (F.loc v t) : k))⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ hne
    have hl : ∀ s, ((F.loc0 v s : F.G0) : F.Γ) = F.loc v s := fun _ => rfl
    have hg : 1 - ((F.Ψ (F.loc v t) : k))⁻¹ ≠ 0 := by
      rw [sub_ne_zero]
      intro h
      exact hf (by rw [← inv_eq_one.mp h.symm, sub_self])
    refine ⟨algebraMap k Q (1 - ((F.Ψ (F.loc v t) : k))⁻¹)⁻¹ * ρ.r (F.loc0 v t) 2 1, fun s => ?_⟩
    have h21 := congrFun (congrFun (ρ.ord v ![t, s, t]) 2) 1
    simp [ordProd, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, hd0, hd1, hd2, h01, h02, h12,
      hψ0, hψ1, hψ2, hl] at h21
    simp only [Algebra.smul_def, mul_one] at h21
    have hD : (algebraMap k Q ((F.Ψ (F.loc v t) : k))⁻¹ - algebraMap k Q ((F.Ψ (F.loc v t) : k))) * algebraMap k Q (((F.Ψ (F.loc v t) : k))⁻¹ - ((F.Ψ (F.loc v t) : k)))⁻¹ = 1 := by
      rw [← map_sub, ← map_mul, mul_inv_cancel₀ (by rw [← neg_sub]; exact neg_ne_zero.mpr he), map_one]
    have hG : (1 - algebraMap k Q ((F.Ψ (F.loc v t) : k))⁻¹) * algebraMap k Q (1 - ((F.Ψ (F.loc v t) : k))⁻¹)⁻¹ = 1 := by
      rw [← map_one (algebraMap k Q), ← map_sub, ← map_mul, mul_inv_cancel₀ hg, map_one]
    show ρ.r (F.star (F.loc0 v s)) 1 0 = _
    rw [(UpperTheory.V.Fr.star hF).2.2.2.2 ρ _ 1 0]
    change ρ.r (F.loc0 v s) 2 1 = _
    simp only [Algebra.smul_def, map_sub, map_one, Units.val_inv_eq_inv_val]
    linear_combination (algebraMap k Q (((F.Ψ (F.loc v t) : k))⁻¹ - ((F.Ψ (F.loc v t) : k)))⁻¹ * algebraMap k Q (1 - ((F.Ψ (F.loc v t) : k))⁻¹)⁻¹) * h21
      + ((1 - algebraMap k Q ((F.Ψ (F.loc v s) : k))⁻¹) * algebraMap k Q (1 - ((F.Ψ (F.loc v t) : k))⁻¹)⁻¹ * ρ.r (F.loc0 v t) 2 1 - ρ.r (F.loc0 v s) 2 1) * hD
      - algebraMap k Q (((F.Ψ (F.loc v t) : k))⁻¹ - ((F.Ψ (F.loc v t) : k)))⁻¹ * (algebraMap k Q ((F.Ψ (F.loc v t) : k))⁻¹ - algebraMap k Q ((F.Ψ (F.loc v t) : k))) * ρ.r (F.loc0 v s) 2 1 * hG
