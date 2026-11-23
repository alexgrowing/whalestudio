import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.ImportsAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.Normkill

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem jv_eq (M a : ℕ) [NeZero M] (ha : a.Coprime M) (b : ZMod M) :
    (M : ℤ) * jv M a b = (a : ℤ) * ((yCl a b).val : ℤ) - (b.val : ℤ) := by
  unfold jv
  have hdiv : (M : ℤ) ∣ (a : ℤ) * ((yCl a b).val : ℤ) - (b.val : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
    unfold yCl
    rw [← mul_assoc, ZMod.coe_mul_inv_eq_one a ha, one_mul, sub_self]
  exact Int.mul_ediv_cancel' hdiv

theorem UpperTheory.V.Odd.clKill :
    ∀ (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (a : ℕ), Odd a → a.Coprime M → ∀ c : Additive (ClassGroup (𝓞 K)), ∑ b : (ZMod M)ˣ, Eone M a b • Stick.clRep K (Stick.sg M K b)⁻¹ c = 0 := by
  intro M _ K _ _ _ a ha hcop c
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {M} ℚ K
  have hterm : ∀ b : (ZMod M)ˣ, Eone M a b • Stick.clRep K (Stick.sg M K b)⁻¹ c =
      Additive.ofMul ((clMap ((Stick.sg M K) b)⁻¹.toRingEquiv (Additive.toMul c)) ^ (Eone M a b)) := by
    intro b
    rfl
  rw [Finset.sum_congr rfl (fun b _ => hterm b), ← ofMul_prod]
  show Additive.ofMul _ = Additive.ofMul 1
  congr 1
  have hnorm : ∏ b : (ZMod M)ˣ, clMap ((Stick.sg M K) b)⁻¹.toRingEquiv (Additive.toMul c) = 1 := by
    rw [← Stk.prod_galois_classGroup_map_eq_one K (Additive.toMul c)]
    exact Fintype.prod_equiv ((Stick.sg M K).toEquiv.trans (Equiv.inv _)) _ _ (fun b => rfl)
  let u : (ZMod M)ˣ := ZMod.unitOfCoprime a hcop
  let β : (ZMod M)ˣ → ℤ := fun s => (if s = u⁻¹ then (a : ℤ) else 0) - (if s = 1 then 1 else 0)
  have hβ : ∀ t : (ZMod M)ˣ, (M : ℤ) * jv M a (t : ZMod M) =
      ∑ s, β s * (((s : ZMod M) * (t : ZMod M)).val : ℤ) := by
    intro t
    rw [jv_eq M a hcop t]
    have hy : yCl a (t : ZMod M) = ((u⁻¹ : (ZMod M)ˣ) : ZMod M) * t := by
      unfold yCl
      rw [← ZMod.inv_coe_unit]
      rfl
    simp only [β, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, one_mul, Units.val_one]
    rw [hy]
  have hj := (Stick.coef M K (Additive.toMul c)).2 β (fun t => jv M a (t : ZMod M)) hβ
  calc ∏ b : (ZMod M)ˣ, clMap ((Stick.sg M K) b)⁻¹.toRingEquiv (Additive.toMul c) ^ Eone M a b
      = ∏ b : (ZMod M)ˣ, (clMap ((Stick.sg M K) b)⁻¹.toRingEquiv (Additive.toMul c) ^ (((a : ℤ) - 1) / 2) *
          (clMap ((Stick.sg M K) b)⁻¹.toRingEquiv (Additive.toMul c) ^ jv M a (b : ZMod M))⁻¹) := by
        refine Finset.prod_congr rfl (fun b _ => ?_)
        unfold Eone
        rw [zpow_sub]
    _ = (∏ b : (ZMod M)ˣ, clMap ((Stick.sg M K) b)⁻¹.toRingEquiv (Additive.toMul c)) ^ (((a : ℤ) - 1) / 2) *
          (∏ b : (ZMod M)ˣ, clMap ((Stick.sg M K) b)⁻¹.toRingEquiv (Additive.toMul c) ^ jv M a (b : ZMod M))⁻¹ := by
        rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_zpow]
    _ = 1 := by
        rw [hnorm, hj, one_zpow, inv_one, one_mul]
