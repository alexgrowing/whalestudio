import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.RhoFrob
open Formalism.ConjugateSelfDual UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ

private theorem UpperTheory.pow_val_mul_zmod {K : Type*} [Monoid K] {m : ℕ} (z : K) (hz : z ^ m = 1) (a b : ZMod m) :
    (z ^ a.val) ^ b.val = z ^ (a * b).val := by
  rw [← pow_mul, ZMod.val_mul, ← pow_eq_pow_mod _ hz]

private theorem UpperTheory.norm_dirichlet_character_le_one {l : ℕ} [Fact l.Prime] {m : ℕ} [NeZero m] (ψ : DirichletCharacter (Qbar l) m)
    (b : (ZMod m)ˣ) : ‖ψ b‖ ≤ 1 := by
  have h1 : (ψ b) ^ (Fintype.card (ZMod m)ˣ) = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
  have h2 : ‖ψ b‖ ^ (Fintype.card (ZMod m)ˣ) = 1 := by rw [← norm_pow, h1, norm_one]
  exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) Fintype.card_ne_zero).1 h2).le

theorem UpperTheory.gaussSum_twist_congr_of_measure :
    ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (N : (ZMod (l ^ r) → Qbar l) →ₗ[Qbar l] Qbar l) (L : PowerSeries (Qbar l)),
      (∀ g g' : ZMod (l ^ r) → Qbar l, (∀ x, IsUnit x → g x = g' x) → N g = N g') →
      (∀ z : Qbar l, z ^ (l ^ r) = 1 → Cg (2 * r) (tval L (l ^ (3 * r)) z) (N (fun x => z ^ x.val))) →
      ∀ (ψ' : DirichletCharacter (Qbar l) (l ^ r)) (z : Qbar l), z ^ (l ^ r) = 1 →
        Cg (2 * r) (∑ b : (ZMod (l ^ r))ˣ, ψ' b * tval L (l ^ (3 * r)) (z ^ (b : ZMod (l ^ r)).val))
          ((∑ b : (ZMod (l ^ r))ˣ, ψ' b * z ^ (b : ZMod (l ^ r)).val) * N (fun x => ψ'⁻¹ x)) := by
  intro l _ r N L hN hL ψ' z hz
  have key : (∑ b : (ZMod (l ^ r))ˣ, ψ' b * z ^ (b : ZMod (l ^ r)).val) * N (fun x => ψ'⁻¹ x) =
      ∑ b : (ZMod (l ^ r))ˣ, ψ' b * N (fun x => (z ^ (b : ZMod (l ^ r)).val) ^ x.val) := by
    simp only [← smul_eq_mul (α := Qbar l) _ (N _), ← map_smul, ← map_sum]
    apply hN
    rintro _ ⟨x, rfl⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_mul, ← Equiv.sum_comp (Equiv.mulRight x)]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hx : ψ' x * ψ'⁻¹ x = 1 := by
      rw [← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply_coe]
    rw [UpperTheory.pow_val_mul_zmod z hz]
    simp only [Equiv.coe_mulRight, Units.val_mul, map_mul]
    linear_combination (ψ' b * z ^ ((b : ZMod (l ^ r)) * x).val) * hx
  rw [key]
  unfold Cg at hL ⊢
  rw [← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun b _ => ?_
  rw [← mul_sub, norm_mul]
  have h1 := hL (z ^ (b : ZMod (l ^ r)).val) (by rw [← pow_mul, mul_comm, pow_mul, hz, one_pow])
  calc _ ≤ 1 * _ := mul_le_mul (UpperTheory.norm_dirichlet_character_le_one ψ' b) h1 (norm_nonneg _) zero_le_one
    _ = _ := one_mul _
