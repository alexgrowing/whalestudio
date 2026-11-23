import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.FnCycMap

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.layerFn :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ), (∃ ζ : F, IsPrimitiveRoot ζ l) → ∃ m, m ≤ n ∧ IsLayer l m F (Fn F Ω l n) := by
  intro F Ω _ _ _ _ _ l _ n hz
  obtain ⟨ζ0, hζ0⟩ := hz
  have hp : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hl : l ^ n ≠ 0 := pow_ne_zero _ hp.ne_zero
  haveI : NeZero ((l ^ n : ℕ) : Ω) := ⟨by exact_mod_cast hl⟩
  haveI : NeZero (l ^ n) := ⟨hl⟩
  have key : Fn F Ω l n = IntermediateField.adjoin F {b : Ω | ∃ k ∈ ({l ^ n} : Set ℕ), k ≠ 0 ∧ b ^ k = 1} := by
    unfold Fn
    congr 1
    ext x
    simp only [Polynomial.mem_rootSet, Set.mem_singleton_iff, Set.mem_setOf_eq, exists_eq_left]
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, sub_eq_zero, ne_eq, hl, not_false_eq_true, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨fun h0 => ?_, h⟩
      have := congrArg Polynomial.natDegree h0
      simp at this
      exact hp.ne_zero this.1
  haveI hcyc : IsCyclotomicExtension {l ^ n} F (Fn F Ω l n) := by
    rw [key]
    apply IntermediateField.isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot
    rintro k rfl -
    exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  haveI : FiniteDimensional F (Fn F Ω l n) := IsCyclotomicExtension.finiteDimensional {l ^ n} F _
  haveI : IsGalois F (Fn F Ω l n) := IsCyclotomicExtension.isGalois {l ^ n} F _
  obtain ⟨μ, hμ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot F (Fn F Ω l n) (Set.mem_singleton (l ^ n)) hl
  set f := hμ.autToPow F with hf
  have hinj : Function.Injective f := hμ.autToPow_injective F
  have hcardG : Nat.card Gal((Fn F Ω l n)/F) = Nat.card f.range :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have h0 := hζ0.map_of_injective (algebraMap F (Fn F Ω l n)).injective
  have hdvd : Nat.card Gal((Fn F Ω l n)/F) ∣ l ^ n := by
    rcases n with _ | k
    · rw [hcardG]
      have : Nat.card f.range ∣ Nat.card (ZMod (l ^ 0))ˣ := Subgroup.card_subgroup_dvd_card _
      have h1 : Nat.card (ZMod (l ^ 0))ˣ = 1 := by
        rw [pow_zero]
        exact Nat.card_unique
      exact (this.trans h1.dvd).trans (one_dvd _)
    · have hd : l ∣ l ^ (k + 1) := dvd_pow_self l (Nat.succ_ne_zero k)
      set g := ZMod.unitsMap hd with hg
      have hle : f.range ≤ g.ker := by
        rintro _ ⟨σ, rfl⟩
        rw [MonoidHom.mem_ker]
        have hω := hμ.pow_of_dvd (pow_ne_zero k hp.ne_zero) (pow_dvd_pow l (Nat.le_succ k))
        have hlk : l ^ (k + 1) / l ^ k = l := by
          rw [pow_succ, Nat.mul_div_cancel_left _ (pow_pos hp.pos k)]
        rw [hlk] at hω
        haveI : NeZero l := ⟨hp.ne_zero⟩
        obtain ⟨i, -, hi⟩ := h0.eq_pow_of_pow_eq_one hω.pow_eq_one
        have hfix : σ (μ ^ l ^ k) = μ ^ l ^ k := by
          rw [← hi, map_pow, AlgEquiv.commutes]
        rw [map_pow, ← IsPrimitiveRoot.autToPow_spec F hμ σ, ← pow_mul, mul_comm, pow_mul] at hfix
        rw [← hf] at hfix
        generalize f σ = u at hfix ⊢
        obtain ⟨ω, hωd⟩ : ∃ ω, ω = μ ^ l ^ k := ⟨_, rfl⟩
        rw [← hωd] at hfix hω
        have hmod : (u : ZMod (l ^ (k + 1))).val ≡ 1 [MOD l] := by
          generalize (u : ZMod (l ^ (k + 1))).val = v at hfix ⊢
          rcases Nat.eq_zero_or_pos v with rfl | hv
          · exfalso
            rw [pow_zero] at hfix
            exact hω.ne_one hp.one_lt hfix.symm
          · have hω0 : ω ≠ 0 := hω.ne_zero hp.ne_zero
            have h3 : ω ^ (v - 1) = 1 := by
              have h4 := hfix
              rw [← Nat.sub_add_cancel hv, pow_succ] at h4
              exact mul_right_cancel₀ hω0 (h4.trans (one_mul ω).symm)
            exact ((Nat.modEq_iff_dvd' hv).mpr ((hω.pow_eq_one_iff_dvd _).mp h3)).symm
        have hc := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
        ext
        rw [hg, ZMod.unitsMap_def]
        simp only [Units.coe_map, MonoidHom.coe_coe, ZMod.castHom_apply, Units.val_one]
        rw [← ZMod.natCast_val]
        simpa using hc
      have hsurj : Function.Surjective g := ZMod.unitsMap_surjective hd
      have hidx : g.ker.index = l - 1 := by
        rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top,
          Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp]
      have hker : Nat.card g.ker = l ^ k := by
        have h1 := Subgroup.card_mul_index g.ker
        rw [hidx, Nat.card_eq_fintype_card (α := (ZMod (l ^ (k + 1)))ˣ), ZMod.card_units_eq_totient,
          Nat.totient_prime_pow hp (Nat.succ_pos k)] at h1
        try simp only [Nat.add_sub_cancel] at h1
        exact Nat.eq_of_mul_eq_mul_right (Nat.sub_pos_of_lt hp.one_lt) h1
      rw [hcardG]
      calc Nat.card f.range ∣ Nat.card g.ker := Subgroup.card_dvd_of_le hle
        _ = l ^ k := hker
        _ ∣ l ^ (k + 1) := pow_dvd_pow l (Nat.le_succ k)
  obtain ⟨m, hm, hmeq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  refine ⟨m, hm, ⟨n, hcyc⟩, ?_⟩
  rw [← IsGalois.card_aut_eq_finrank, hmeq]
