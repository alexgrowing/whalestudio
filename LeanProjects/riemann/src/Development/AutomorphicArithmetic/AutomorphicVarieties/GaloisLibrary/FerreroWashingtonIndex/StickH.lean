import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CycRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.ThetaFull
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.ImportsAlt

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

theorem UpperTheory.V.FW.stickH :
    ∀ (M c : ℕ) [NeZero M] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {M} ℚ L], c.Coprime M → Odd c → 2 < M → (cycRep M L).asAlgebraHom (thetaH M c * (1 - MonoidAlgebra.of ℤ _ (-1 : (ZMod M)ˣ))) = 0 := by
  intro M c _ L _ _ _ hc hodd hM
  rw [(thetaFull M c hc hodd hM).1, map_sum]
  refine LinearMap.ext fun x => ?_
  simp only [Representation.asAlgebraHom_single, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.zero_apply]
  have key : ∀ y : Cl L, ∑ s : (ZMod M)ˣ, gc M c ↑s • (cycRep M L s) (Additive.ofMul y) = 0 := by
    intro y
    simp only [cycRep_apply, ← ofMul_zpow, ← ofMul_prod, clA, ofMul_eq_zero]
    haveI : Fact (1 < M) := ⟨by omega⟩
    set u : (ZMod M)ˣ := ZMod.unitOfCoprime c hc with hu_def
    set k : ℤ := (((c - 1) / 2 : ℕ) : ℤ) with hk
    refine (Stick.coef M L y).2
      (fun s => (c : ℤ) * (if s = u⁻¹ then 1 else 0) - (k + 1) * (if s = 1 then 1 else 0)
        - k * (if s = -1 then 1 else 0)) (fun t => gc M c ↑t) ?_
    intro t
    haveI : NeZero (t : ZMod M) := ⟨t.ne_zero⟩
    have hlt := ZMod.val_lt (t : ZMod M)
    have hneg : ((-(t : ZMod M)).val : ℤ) = M - (t : ZMod M).val := by
      rw [ZMod.val_neg_of_ne_zero (t : ZMod M), Nat.cast_sub hlt.le]
    have hu : ((u⁻¹ : (ZMod M)ˣ) : ZMod M) = (c : ZMod M)⁻¹ := by
      rw [← ZMod.inv_coe_unit]
      rfl
    have hmod : c * ((c : ZMod M)⁻¹ * t).val % M = (t : ZMod M).val := by
      rw [← ZMod.val_natCast, Nat.cast_mul, ZMod.natCast_zmod_val, ← mul_assoc,
        ZMod.coe_mul_inv_eq_one c hc, one_mul]
    have hdiv := Nat.div_add_mod (c * ((c : ZMod M)⁻¹ * t).val) M
    rw [hmod] at hdiv
    simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Units.val_one, Units.val_neg,
      neg_one_mul, hu, hneg, gc]
    generalize c * ((c : ZMod M)⁻¹ * t).val / M = q at hdiv ⊢
    have hz : (M : ℤ) * q + ((t : ZMod M).val : ℤ) = c * (((c : ZMod M)⁻¹ * t).val : ℤ) := by
      exact_mod_cast hdiv
    linear_combination hz
  exact key (Additive.toMul x)
