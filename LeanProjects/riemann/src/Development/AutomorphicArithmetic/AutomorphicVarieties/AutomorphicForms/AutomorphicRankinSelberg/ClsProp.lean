import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

open UpperHalfPlane hiding I
open scoped MatrixGroups

namespace UpperTheory.V.Af.Rs

private theorem cls_rep (hR : RowRep) (L : ℕ) [NeZero L] (v : Fin 2 → ZMod L) :
    ∃ (n : ℕ) (γ : SL(2, ℤ)), v = cls L ((n : ℤ) • row γ) := by
  obtain ⟨n, γ, h⟩ := hR (fun i => ((v i).val : ℤ))
  refine ⟨n, γ, ?_⟩
  rw [← h]
  funext i
  simp [cls]

private theorem cls_smul (L : ℕ) (m n : ℕ) (x : Fin 2 → ℤ) :
    (m : ZMod L) • cls L ((n : ℤ) • x) = cls L (((m * n : ℕ) : ℤ) • x) := by
  funext i
  simp only [cls, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

private theorem norm_char_le {L : ℕ} [NeZero L] (ψ : DirichletCharacter ℂ L) (a : ZMod L) : ‖ψ a‖ ≤ 1 :=
  ψ.norm_le_one a

end UpperTheory.V.Af.Rs

theorem UpperTheory.V.Af.Rs.clsProp :
    UpperTheory.V.Af.Rs.RowRep → UpperTheory.V.Af.Rs.ClsProp := by
  intro hR L _ ψ F G hG
  have hscale : ∀ (a : ZMod L) (v : Fin 2 → ZMod L) (z : ℍ), G (a • v) z = ψ a * G v z := by
    intro a v z
    obtain ⟨n, γ, rfl⟩ := cls_rep hR L v
    rw [← ZMod.natCast_zmod_val a, cls_smul, hG, hG]
    push_cast
    rw [map_mul]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hFc, C, hC⟩
    refine ⟨?_, C, ?_⟩
    · intro v
      obtain ⟨n, γ, rfl⟩ := cls_rep hR L v
      have hγ : Continuous (fun z : ℍ => γ • z) :=
        continuous_const_smul (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ))
      have : (fun z => G (cls L ((n : ℤ) • row γ)) z) = fun z => ψ n * F (γ • z) := by
        funext z; exact hG n γ z
      change Continuous (fun z => G (cls L ((n : ℤ) • row γ)) z)
      rw [this]
      exact continuous_const.mul (hFc.comp hγ)
    · intro v z hz
      obtain ⟨n, γ, rfl⟩ := cls_rep hR L v
      rw [hG, norm_mul, mul_assoc]
      have h1 := hC γ z hz
      have h0 : 0 ≤ ‖F (γ • z)‖ * z.im ^ 3 := by
        have : 0 < z.im := z.im_pos
        positivity
      exact (mul_le_of_le_one_left h0 (norm_char_le ψ _)).trans h1
  · intro hψ z
    obtain ⟨u, hu⟩ := MulChar.ne_one_iff.mp hψ
    let e : (Fin 2 → ZMod L) ≃ (Fin 2 → ZMod L) :=
      { toFun := fun v => (u : ZMod L) • v
        invFun := fun v => ((u⁻¹ : (ZMod L)ˣ) : ZMod L) • v
        left_inv := fun v => by simp [smul_smul]
        right_inv := fun v => by simp [smul_smul] }
    have hs : ∑ v, G v z = ∑ v, G ((u : ZMod L) • v) z :=
      Fintype.sum_equiv e.symm _ _ (fun v => by simp [e, smul_smul])
    have hs2 : ∑ v, G v z = ψ u * ∑ v, G v z := by
      rw [Finset.mul_sum]
      conv_lhs => rw [hs]
      exact Finset.sum_congr rfl (fun v _ => hscale _ v z)
    have hne : (1 : ℂ) - ψ u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
    have : ((1 : ℂ) - ψ u) * ∑ v, G v z = 0 := by rw [sub_mul, one_mul, ← hs2, sub_self]
    exact (mul_eq_zero.mp this).resolve_left hne
  · intro hψ hF0 hFpos
    have hval : ∀ n : ℕ, ψ n = 0 ∨ ψ n = 1 := by
      intro n
      subst hψ
      by_cases h : IsUnit (n : ZMod L)
      · exact Or.inr (MulChar.one_apply h)
      · exact Or.inl (MulChar.map_nonunit _ h)
    refine ⟨?_, ?_⟩
    · intro v z
      obtain ⟨n, γ, rfl⟩ := cls_rep hR L v
      rw [hG]
      rcases hval n with h | h <;> simp [h, hF0]
    · obtain ⟨z0, hz0⟩ := hFpos
      obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z0
      refine ⟨cls L (((1 : ℕ) : ℤ) • row g⁻¹), g • z0, hg, ?_⟩
      rw [hG, inv_smul_smul]
      subst hψ
      simpa using hz0
