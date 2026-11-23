import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PotOfFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.PowEqOneOfKills

open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Sd

private theorem flag_exp {U : Type} [CommGroup U] (x y c : U) (a b : ℕ) (p q : ℤ) (ha : 0 < a) (hb : 0 < b)
    (hpq : p ≠ q + 1) (hinf : ∀ k : ℕ, k ≠ 0 → c ^ k ≠ 1)
    (hx : x ^ a = (c ^ p) ^ a) (hy : y ^ a = (c ^ q) ^ a) (h : x ^ b = (y * c) ^ b) : False := by
  have e : (x ^ a) ^ b = (y ^ a) ^ b * (c ^ a) ^ b := by
    rw [← pow_mul, ← pow_mul, ← pow_mul, ← mul_pow, mul_comm a b, pow_mul x b a, h, ← pow_mul, mul_comm b a,
      pow_mul (y * c) a b, mul_pow]
  rw [hx, hy] at e
  simp only [← zpow_natCast, ← zpow_mul] at e
  rw [← zpow_add] at e
  set m : ℤ := p * a * b - (q * a * b + a * b) with hm
  have h1 : c ^ m = 1 := by rw [hm, zpow_sub, e, mul_inv_cancel]
  have hm0 : m ≠ 0 := by
    have : m = (p - q - 1) * ((a : ℤ) * b) := by rw [hm]; ring
    rw [this]
    refine mul_ne_zero (by omega) (mul_ne_zero (by exact_mod_cast ha.ne') (by exact_mod_cast hb.ne'))
  apply hinf m.natAbs (Int.natAbs_ne_zero.mpr hm0)
  rcases Int.natAbs_eq m with hn | hn
  · rw [hn, zpow_natCast] at h1; exact h1
  · rw [hn, zpow_neg, zpow_natCast, inv_eq_one] at h1; exact h1

private theorem pow_fix {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [Algebra ℚ Ω] [IsScalarTower ℚ F Ω]
    (σ : G ℚ Ω) : ∃ n : ℕ, 0 < n ∧ ∀ x : F, (σ ^ n) (algebraMap F Ω x) = algebraMap F Ω x := by
  let ι : F →ₐ[ℚ] Ω := IsScalarTower.toAlgHom ℚ F Ω
  let f : ℕ → (F →ₐ[ℚ] Ω) := fun k => (((σ : Ω ≃ₐ[ℚ] Ω) ^ k : Ω ≃ₐ[ℚ] Ω) : Ω →ₐ[ℚ] Ω).comp ι
  have key : ∀ i j : ℕ, i < j → f i = f j →
      ∃ n : ℕ, 0 < n ∧ ∀ x : F, (σ ^ n) (algebraMap F Ω x) = algebraMap F Ω x := by
    intro i j hlt he
    refine ⟨j - i, by omega, fun x => ?_⟩
    have hx : ((σ : Ω ≃ₐ[ℚ] Ω) ^ i) (algebraMap F Ω x) = ((σ : Ω ≃ₐ[ℚ] Ω) ^ j) (algebraMap F Ω x) :=
      congrArg (fun φ : F →ₐ[ℚ] Ω => φ x) he
    apply ((σ : Ω ≃ₐ[ℚ] Ω) ^ i).injective
    show ((σ : Ω ≃ₐ[ℚ] Ω) ^ i) (((σ : Ω ≃ₐ[ℚ] Ω) ^ (j - i)) (algebraMap F Ω x)) = _
    rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' hlt.le]
    exact hx.symm
  obtain ⟨i, j, hij, he⟩ := Finite.exists_ne_map_eq_of_infinite f
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact key i j hlt he
  · exact key j i hlt he.symm

private theorem cyc_inf_over (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [hl : Fact l.Prime] (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) :
    ∃ s ∈ Ine (F := F) A, ∀ k : ℕ, k ≠ 0 → cycBar F Ω l s ^ k ≠ 1 := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsAlgClosure ℚ Ω := ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.trans ℚ F Ω⟩
  have hl2 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hnorm : ‖((1 + l : ℕ) : ℤ_[l])‖ = 1 := by
    push_cast
    have hne : ‖(1 : ℤ_[l])‖ ≠ ‖(l : ℤ_[l])‖ := by
      rw [norm_one, PadicInt.norm_p]
      exact ne_of_gt (inv_lt_one_of_one_lt₀ hl2)
    rw [PadicInt.norm_add_eq_max_of_ne hne, norm_one, PadicInt.norm_p]
    exact max_eq_left (inv_lt_one_of_one_lt₀ hl2).le
  let u : ℤ_[l]ˣ := (PadicInt.isUnit_iff.mpr hnorm).unit
  obtain ⟨σ, hσ, hσu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA u
  obtain ⟨n, hn, hfix⟩ := pow_fix (F := F) σ
  let s : G F Ω := AlgEquiv.ofRingEquiv (f := ((σ ^ n : G ℚ Ω) : Ω ≃ₐ[ℚ] Ω).toRingEquiv) hfix
  have hσn : σ ^ n ∈ Ine (F := ℚ) A := Subgroup.pow_mem _ hσ n
  refine ⟨s, ⟨hσn.1, hσn.2⟩, ?_⟩
  intro k hk h1
  have hr : cycZ F Ω l s = u ^ n := by
    rw [← hσu, ← map_pow]
    show cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G F Ω) Ω s) =
      cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω (σ ^ n))
    congr 1
  have h2 : cycBar F Ω l s = Units.map (((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom :
      ℤ_[l] →+* Qbar l) : ℤ_[l] →* Qbar l) (u ^ n) := by
    show Units.map _ (cycZ F Ω l s) = _
    rw [hr]
    rfl
  rw [h2, ← map_pow, ← pow_mul] at h1
  have h3 := congrArg Units.val h1
  rw [Units.coe_map, Units.val_one] at h3
  have hinj : Function.Injective ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom) :=
    (algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective
  have h4 : ((u ^ (n * k) : ℤ_[l]ˣ) : ℤ_[l]) = 1 := hinj (by rw [map_one]; exact h3)
  rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, ← Nat.cast_pow] at h4
  have h5 : (1 + l) ^ (n * k) = 1 := by exact_mod_cast h4
  have h6 : 1 < (1 + l) ^ (n * k) :=
    Nat.one_lt_pow (Nat.mul_ne_zero hn.ne' hk) (by have := hl.out.one_lt; omega)
  omega

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.potOfFlag :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.PotOfFlag := by
  intro F Ω _ _ _ _ _ l _ n r m hm v hv H A hA
  obtain ⟨κ, a, ha, hflag, hκ⟩ := H A hA
  refine ⟨κ, hflag, fun i j b hb h => ?_⟩
  have hAl : A.valuation (l : Ω) < 1 := by
    have h1 := (hA ((l : ℕ) : 𝓞 F)).2 hv
    simpa using h1
  obtain ⟨s, hs, hinf⟩ := cyc_inf_over F Ω l A hAl
  let t : ↥(Dec (F := F) A) := ⟨s, Ine_le_Dec A hs⟩
  have h1 : κ i t ^ b = (κ j t * cycBar F Ω l s) ^ b := DFunLike.congr_fun h t
  exact flag_exp (κ i t) (κ j t) (cycBar F Ω l s) a b (m i) (m j) ha hb (hm i j) hinf (hκ i t hs) (hκ j t hs) h1
