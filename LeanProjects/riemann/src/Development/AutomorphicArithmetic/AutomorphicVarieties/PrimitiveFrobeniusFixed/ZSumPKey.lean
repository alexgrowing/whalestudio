import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem zSumP_key {Ω : Type} [Field Ω] [Algebra ℚ Ω] (F : ℕ) [NeZero F] (t d : (ZMod F)ˣ) (g h k : G ℚ Ω)
    (hg : Lifts F t g) (hh : Lifts F d h) (hk : Lifts F (t * d) k) : k⁻¹ * (g * h) ∈ fixMu ℚ Ω F := by
  have hg' : ∀ x : Ω, x ^ F = 1 → g x = x ^ (t : ZMod F).val := hg
  have hh' : ∀ x : Ω, x ^ F = 1 → h x = x ^ (d : ZMod F).val := hh
  have hk' : ∀ x : Ω, x ^ F = 1 → k x = x ^ ((t * d : (ZMod F)ˣ) : ZMod F).val := hk
  show ∀ x : Ω, x ^ F = 1 → (k⁻¹ * (g * h)) x = x
  intro x hx
  have hgh : (g * h) x = k x := by
    rw [AlgEquiv.mul_apply, hh' x hx, map_pow, hg' x hx, ← pow_mul, hk' x hx, Units.val_mul, ZMod.val_mul]
    conv_lhs => rw [← Nat.mod_add_div ((t : ZMod F).val * (d : ZMod F).val) F]
    rw [pow_add, pow_mul, hx, one_pow, mul_one]
  rw [AlgEquiv.mul_apply, hgh, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

theorem UpperTheory.V.ML.zSumP :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (O : Type) [CommRing O] (F a : ℕ) [NeZero F] (I : O) (α : G ℚ Ω →* Oˣ), (∀ g ∈ fixMu ℚ Ω F, I ∣ (α g : O) - 1) → ∀ σ : (ZMod F)ˣ → G ℚ Ω, (∀ t, Lifts F t (σ t)) →
    ∀ (k : (ZMod F)ˣ → ℤ), (∀ (d : (ZMod F)ˣ) (δ : G ℚ Ω), Lifts F d δ → I ∣ zSum α σ (fun t => k (t * d) - a * k t) - ((α δ : O) - a) * zSum α σ k) ∧
    ∀ n : ℤ, zSum α σ (fun t => n * k t) = n * zSum α σ k := by
  intro Ω _ _ _ O _ F a _ I α hI σ hσ k
  refine ⟨fun d δ hδ => ?_, fun n => ?_⟩
  · have hre : ∑ t, (k t : O) * (((α (σ t))⁻¹ : Oˣ) : O) = ∑ t, (k (t * d) : O) * (((α (σ (t * d)))⁻¹ : Oˣ) : O) :=
      (Fintype.sum_equiv (Equiv.mulRight d) _ _ (fun t => rfl)).symm
    have h1 : zSum α σ (fun t => k (t * d) - a * k t) - ((α δ : O) - a) * zSum α σ k
        = ∑ t, (k (t * d) : O) * (((α (σ t))⁻¹ : Oˣ) : O) - (α δ : O) * ∑ t, (k t : O) * (((α (σ t))⁻¹ : Oˣ) : O) := by
      simp only [zSum, Int.cast_sub, Int.cast_mul, Int.cast_natCast, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
      ring
    have h2 : ∑ t, (k (t * d) : O) * (((α (σ t))⁻¹ : Oˣ) : O) - (α δ : O) * ∑ t, (k (t * d) : O) * (((α (σ (t * d)))⁻¹ : Oˣ) : O)
        = ∑ t, (k (t * d) : O) * (((α (σ t))⁻¹ : Oˣ) : O) * (1 - (α ((σ (t * d))⁻¹ * (σ t * δ)) : O)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      have hu : (((α (σ t))⁻¹ : Oˣ) : O) * (α (σ t) : O) = 1 := Units.inv_mul _
      simp only [map_mul, map_inv, Units.val_mul]
      linear_combination ((α δ : O) * (k (t * d) : O) * (((α (σ (t * d)))⁻¹ : Oˣ) : O)) * hu
    rw [h1, hre, h2]
    refine Finset.dvd_sum fun t _ => Dvd.dvd.mul_left ?_ _
    exact dvd_sub_comm.mp (hI _ (zSumP_key F t d (σ t) δ (σ (t * d)) (hσ t) hδ (hσ (t * d))))
  · simp only [zSum, Int.cast_mul, mul_assoc, Finset.mul_sum]
