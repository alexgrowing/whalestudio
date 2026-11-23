import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CycRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.AmbIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.RelCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.GamGen

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

theorem UpperTheory.V.FW.ambCyc :
    ∀ (l : ℕ) [Fact l.Prime] (f : ℕ), f.Coprime l → ∃ B : ℕ, ∀ (n : ℕ) [NeZero (f * l ^ n)] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {f * l ^ n} ℚ L] (γ : (ZMod (f * l ^ n))ˣ), 2 ≤ n → (γ : ZMod (f * l ^ n)) = 1 + f * l ^ ee l → (powR (Cl L) l ⊔ difR (clA (f * l ^ n) L γ)).index ≤ B := by
  intro l hl f hf
  have hl1 : 1 < l := hl.out.one_lt
  have hlpos : 0 < l := hl.out.pos
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hf
    omega
  have hfpos : 0 < f := Nat.pos_of_ne_zero hf0
  have he1 : 1 ≤ ee l := by unfold ee; split_ifs <;> omega
  have he2 : ee l ≤ 2 := by unfold ee; split_ifs <;> omega
  haveI : NeZero (f * l ^ ee l) := ⟨by positivity⟩
  haveI : NeZero ((f * l ^ ee l : ℕ) : ℚ) := ⟨by exact_mod_cast (show f * l ^ ee l ≠ 0 by positivity)⟩
  haveI : IsCyclotomicExtension {f * l ^ ee l} ℚ (CyclotomicField (f * l ^ ee l) ℚ) := by
    convert CyclotomicField.isCyclotomicExtension (f * l ^ ee l) ℚ
    · rfl
    · exact Subsingleton.elim _ _
  haveI : NumberField (CyclotomicField (f * l ^ ee l) ℚ) :=
    IsCyclotomicExtension.numberField {f * l ^ ee l} ℚ _
  obtain ⟨z, hz⟩ : ∃ z : CyclotomicField (f * l ^ ee l) ℚ, IsPrimitiveRoot z (f * l ^ ee l) :=
    ⟨_, IsCyclotomicExtension.zeta_spec _ ℚ _⟩
  have hsplit : f * l ^ ee l = l * (f * l ^ (ee l - 1)) := by
    rw [mul_comm l, mul_assoc, ← pow_succ, Nat.sub_add_cancel he1]
  have hzl : IsPrimitiveRoot (z ^ (f * l ^ (ee l - 1))) l := by
    have h := hz.pow_of_dvd (by positivity) (Dvd.intro_left l hsplit.symm)
    rwa [Nat.div_eq_of_eq_mul_left (by positivity) hsplit] at h
  obtain ⟨B, hB⟩ := amb (CyclotomicField (f * l ^ ee l) ℚ) l _ hzl
  refine ⟨B, ?_⟩
  intro n _ L _ _ _ γ hn hγ
  have hen : ee l ≤ n := le_trans he2 hn
  have h : f * l ^ ee l ∣ f * l ^ n := mul_dvd_mul_left f (pow_dvd_pow l hen)
  obtain ⟨alg, hcycL, hall, hex⟩ := relCyc l f (ee l) n h (CyclotomicField (f * l ^ ee l) ℚ) L hf
  obtain ⟨hker, -⟩ := gamGen l f n h γ hf hen hγ
  letI := alg
  haveI := hcycL
  have hγinv : γ⁻¹ ∈ (ZMod.unitsMap h).ker := by
    rw [hker]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers γ)
  obtain ⟨τ, hτ⟩ := hex γ⁻¹ hγinv
  have hbig : 2 < f * l ^ n := by
    have h4 : 4 ≤ l ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ l ^ 2 := Nat.pow_le_pow_left hl.out.two_le 2
        _ ≤ l ^ n := Nat.pow_le_pow_right hlpos hn
    nlinarith
  have htc : IsTotallyComplex L := IsCyclotomicExtension.Rat.isTotallyComplex (n := f * l ^ n) L hbig
  let ρF : Gal(L/CyclotomicField (f * l ^ ee l) ℚ) →* (L ≃+* L) :=
    { toFun := fun σ => σ.toRingEquiv, map_one' := rfl, map_mul' := fun _ _ => rfl }
  let ρQ : Gal(L/ℚ) →* (L ≃+* L) :=
    { toFun := fun σ => σ.toRingEquiv, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hgen : ∀ σ : Gal(L/CyclotomicField (f * l ^ ee l) ℚ), σ ∈ Subgroup.zpowers τ := by
    intro σ
    obtain ⟨t, ht, hσ⟩ := hall σ
    rw [hker] at ht
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    refine Subgroup.mem_zpowers_iff.mpr ⟨-k, ?_⟩
    have e1 : ρF σ = ρQ (sg (f * l ^ n) L (γ ^ k)) := hσ
    have e2 : ρF τ = ρQ (sg (f * l ^ n) L γ⁻¹) := hτ
    have e3 : ρF σ = ρF (τ ^ (-k)) := by
      rw [e1, map_zpow ρF, e2, ← map_zpow, ← map_zpow, inv_zpow', neg_neg]
    exact AlgEquiv.ext fun x => (congrArg (fun r : L ≃+* L => r x) e3).symm
  have hcl : clA (f * l ^ n) L γ = clMap τ.toRingEquiv := by
    rw [hτ, map_inv]
    rfl
  rw [hcl]
  exact hB n L τ htc hgen
