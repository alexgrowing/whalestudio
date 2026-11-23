import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostNumber
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised

open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia

private theorem prim4 {L : Type} [Field L] [CharZero L] {i : L} (hi : i * i = -1) : IsPrimitiveRoot i (2 ^ 2) := by
  have hne : (1 : L) ≠ -1 := by
    intro h
    have h2 : (2 : L) = 0 := by linear_combination h
    exact two_ne_zero h2
  rw [IsPrimitiveRoot.iff (by norm_num)]
  refine ⟨by linear_combination (i * i - 1) * hi, ?_⟩
  intro l hl hl4
  norm_num at hl4
  interval_cases l
  · intro h1
    exact hne (by linear_combination hi - (i + 1) * h1)
  · intro h2
    exact hne (by linear_combination hi - h2)
  · intro h3
    exact hne (by linear_combination (1 - i ^ 2 + i) * hi + (i - 1) * h3)

private theorem adj_top {K : Type} [Field K] [NumberField K] (h : Module.finrank ℚ K = 2) {i : K} (hi : i * i = -1) :
    Algebra.adjoin ℚ {i} = ⊤ := by
  have hnb : i ∉ (⊥ : Subalgebra ℚ K) := by
    rw [Algebra.mem_bot]
    rintro ⟨q, hq⟩
    have hq2 : algebraMap ℚ K (q * q) = algebraMap ℚ K (-1) := by
      rw [map_mul, hq, hi, map_neg, map_one]
    have hq3 := (algebraMap ℚ K).injective hq2
    nlinarith [mul_self_nonneg q]
  have hS : Algebra.adjoin ℚ {i} ≠ ⊥ := by
    intro hb
    apply hnb
    rw [← hb]
    exact Algebra.subset_adjoin rfl
  have hle : Module.finrank ℚ (Subalgebra.toSubmodule (Algebra.adjoin ℚ {i})) ≤ 2 :=
    h ▸ Submodule.finrank_le _
  have hpos : 0 < Module.finrank ℚ (Algebra.adjoin ℚ {i}) := Module.finrank_pos
  have hne1 : Module.finrank ℚ (Algebra.adjoin ℚ {i}) ≠ 1 :=
    fun h1 => hS (Subalgebra.finrank_eq_one_iff.mp h1)
  have h2 : Module.finrank ℚ (Subalgebra.toSubmodule (Algebra.adjoin ℚ {i})) = Module.finrank ℚ K := by
    have : Module.finrank ℚ (Subalgebra.toSubmodule (Algebra.adjoin ℚ {i})) =
        Module.finrank ℚ (Algebra.adjoin ℚ {i}) := rfl
    omega
  apply Subalgebra.toSubmodule_injective
  rw [Algebra.top_toSubmodule]
  exact Submodule.eq_top_of_finrank_eq h2

open UpperTheory.V UpperTheory.V.Base in
private theorem fix_iff (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ζ : Ω) (hζ : IsPrimitiveRoot ζ 4)
    (σ : G ℚ Ω) : σ ζ = ζ ↔ eta4 Ω σ = 1 := by
  have hspec := UpperTheory.V.Chr.cls_spec (k := ℚ) 4 σ ζ hζ.pow_eq_one
  have key : ∀ u : (ZMod 4)ˣ, u = 1 ∨ u = -1 := by decide
  have heta : eta4 Ω σ = MulChar.toUnitHom ZMod.χ₄ (UpperTheory.V.Chr.cls ℚ Ω 4 σ) := rfl
  rcases key (UpperTheory.V.Chr.cls ℚ Ω 4 σ) with hu | hu
  · rw [heta, hu, map_one]
    simp only [iff_true]
    rw [hspec, hu, Units.val_one, show ZMod.val (1 : ZMod 4) = 1 from rfl, pow_one]
  · rw [heta, hu]
    have hm : MulChar.toUnitHom ZMod.χ₄ (-1) ≠ 1 := by
      intro h
      have h' := congrArg (fun x : ℤˣ => (x : ℤ)) h
      simp only [MulChar.coe_toUnitHom, Units.val_neg, Units.val_one] at h'
      revert h'
      decide
    have hz : σ ζ ≠ ζ := by
      rw [hspec, hu]
      have h3 : (((-1 : (ZMod 4)ˣ) : ZMod 4)).val = 3 := rfl
      rw [h3]
      intro h
      have hζ0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
      have hsq : ζ ^ 2 = 1 := by
        apply mul_right_cancel₀ hζ0
        linear_combination h
      exact hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num) hsq
    exact iff_of_false hz hm

theorem UpperTheory.V.UnitaryThreeInertia.gaussian_field_range_eq_ker_quartic_char :
    (∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K), IsQi K) ∧ ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsScalarTower ℚ K Ω], IsQi K →
      (Base.galEmb ℚ K Ω).range = (eta4 Ω).ker ∧ discr K = -4 := by
  have sq_of_prim : ∀ {L : Type} [Field L] {z : L}, IsPrimitiveRoot z 4 → z * z = -1 := by
    intro L _ z hz
    have h4 : z ^ 4 = 1 := hz.pow_eq_one
    have h2 : z ^ 2 ≠ 1 := hz.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
    have hprod : (z ^ 2 - 1) * (z ^ 2 + 1) = 0 := by linear_combination h4
    rcases mul_eq_zero.mp hprod with h | h
    · exact absurd (sub_eq_zero.mp h) h2
    · linear_combination h
  refine ⟨⟨CyclotomicField 4 ℚ, inferInstance, inferInstance, ?_, ?_⟩, ?_⟩
  · exact IsCyclotomicExtension.Rat.isCMField (CyclotomicField 4 ℚ) (S := {4}) ⟨4, rfl, by norm_num⟩
  · refine ⟨?_, ⟨IsCyclotomicExtension.zeta 4 ℚ (CyclotomicField 4 ℚ),
      sq_of_prim (IsCyclotomicExtension.zeta_spec 4 ℚ (CyclotomicField 4 ℚ))⟩⟩
    rw [IsCyclotomicExtension.Rat.finrank 4 (CyclotomicField 4 ℚ)]
    decide
  · intro Ω _ _ _ K _ _ _ _ hK
    obtain ⟨hrank, i, hi⟩ := hK
    have hadj := adj_top hrank hi
    have hprim : IsPrimitiveRoot (algebraMap K Ω i) 4 := by
      have := prim4 (L := Ω) (i := algebraMap K Ω i) (by rw [← map_mul, hi, map_neg, map_one])
      simpa using this
    refine ⟨?_, ?_⟩
    · ext σ
      rw [MonoidHom.mem_ker, ← fix_iff Ω _ hprim σ, UpperTheory.V.Base.range_galEmb,
        UpperTheory.V.Base.mem_galOf]
      constructor
      · intro h
        exact h i
      · intro h x
        have hφ : (σ.toAlgHom).comp (IsScalarTower.toAlgHom ℚ K Ω) = IsScalarTower.toAlgHom ℚ K Ω := by
          apply AlgHom.ext_of_adjoin_eq_top hadj
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact h
        exact congrArg (fun φ : K →ₐ[ℚ] Ω => φ x) hφ
    · haveI : IsCyclotomicExtension {2 ^ 2} ℚ K := by
        rw [IsCyclotomicExtension.iff_singleton]
        refine ⟨⟨i, prim4 hi⟩, ?_⟩
        intro x
        have hle : Algebra.adjoin ℚ {i} ≤ Algebra.adjoin ℚ {b : K | b ^ (2 ^ 2) = 1} := by
          apply Algebra.adjoin_mono
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact (prim4 hi).pow_eq_one
        apply hle
        rw [hadj]
        trivial
      rw [IsCyclotomicExtension.Rat.discr_prime_pow 2 2 K]
      have ht : Nat.totient (2 ^ 2) = 2 := by decide
      rw [ht]
      norm_num
