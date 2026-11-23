import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CycRepApply

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

private theorem UpperTheory.V.FW.relCyc_compat {m N : ℕ} [NeZero m] [NeZero N] (h : m ∣ N) (K : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {m} ℚ K] (C : Type) [Field C] [NumberField C] [IsCyclotomicExtension {N} ℚ C]
    (i : K →ₐ[ℚ] C) (a : (ZMod N)ˣ) (x : K) :
    sg N C a (i x) = i (sg m K (ZMod.unitsMap h a) x) := by
  have hz := IsCyclotomicExtension.zeta_spec m ℚ K
  have key : ((sg N C a : C →ₐ[ℚ] C)).comp i = i.comp (sg m K (ZMod.unitsMap h a) : K →ₐ[ℚ] K) := by
    apply (hz.powerBasis ℚ).algHom_ext
    rw [IsPrimitiveRoot.powerBasis_gen]
    set z := IsCyclotomicExtension.zeta m ℚ K
    have h1 : z ^ m = 1 := hz.pow_eq_one
    have h2 : (i z) ^ m = 1 := by rw [← map_pow, h1, map_one]
    have h3 : (i z) ^ N = 1 := by
      obtain ⟨k, rfl⟩ := h
      rw [pow_mul, h2, one_pow]
    change sg N C a (i z) = i (sg m K (ZMod.unitsMap h a) z)
    rw [sg_apply N C a h3, sg_apply m K _ h1, map_pow]
    have : ((ZMod.unitsMap h a : (ZMod m)ˣ) : ZMod m).val = (a : ZMod N).val % m := by
      rw [ZMod.unitsMap_val, ZMod.cast_eq_val, ZMod.val_natCast]
    rw [this]
    exact pow_eq_pow_mod _ h2
  exact DFunLike.congr_fun key x

theorem UpperTheory.V.FW.relCyc :
    ∀ (l f e n : ℕ) [NeZero (f * l ^ n)] (h : f * l ^ e ∣ f * l ^ n) (F : Type) [Field F] [NumberField F] [IsCyclotomicExtension {f * l ^ e} ℚ F] (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {f * l ^ n} ℚ L], f.Coprime l → ∃ _ : Algebra F L, IsCyclotomicExtension {l ^ n} F L ∧ (∀ σ : Gal(L/F), ∃ t ∈ (ZMod.unitsMap h).ker, σ.toRingEquiv = (sg (f * l ^ n) L t).toRingEquiv) ∧ ∀ t ∈ (ZMod.unitsMap h).ker, ∃ σ : Gal(L/F), σ.toRingEquiv = (sg (f * l ^ n) L t).toRingEquiv := by
  intro l f e n _ h F _ _ _ L _ _ _ hfl
  have hM : 0 < f * l ^ n := NeZero.pos _
  have hM0 : 0 < f * l ^ e := Nat.pos_of_dvd_of_pos h hM
  haveI : NeZero (f * l ^ e) := ⟨hM0.ne'⟩
  have hf : 0 < f := Nat.pos_of_mul_pos_right hM
  have hln : 0 < l ^ n := Nat.pos_of_mul_pos_left hM
  haveI : NeZero (l ^ n) := ⟨hln.ne'⟩
  have hζ := IsCyclotomicExtension.zeta_spec (f * l ^ n) ℚ L
  set ζ := IsCyclotomicExtension.zeta (f * l ^ n) ℚ L
  have hz := IsCyclotomicExtension.zeta_spec (f * l ^ e) ℚ F
  set z := IsCyclotomicExtension.zeta (f * l ^ e) ℚ F with hzdef
  obtain ⟨k, hk⟩ := id h
  have hk' : l ^ n = k * l ^ e := by
    apply Nat.eq_of_mul_eq_mul_left hf
    rw [hk]; ring
  obtain ⟨i, hi⟩ : ∃ i : F →ₐ[ℚ] L, i z = ζ ^ k := by
    have hξ : IsPrimitiveRoot (ζ ^ k) (f * l ^ e) := hζ.pow hM (by rw [hk, mul_comm])
    refine ⟨(hz.powerBasis ℚ).lift (ζ ^ k) ?_, ?_⟩
    · rw [IsPrimitiveRoot.powerBasis_gen, ← Polynomial.cyclotomic_eq_minpoly_rat hz hM0,
        Polynomial.cyclotomic_eq_minpoly_rat hξ hM0]
      exact minpoly.aeval ℚ _
    · exact (congrArg _ (IsPrimitiveRoot.powerBasis_gen ℚ hz).symm).trans ((hz.powerBasis ℚ).lift_gen (ζ ^ k) _)
  letI : Algebra F L := i.toRingHom.toAlgebra
  have hal : ∀ x, algebraMap F L x = i x := fun _ => rfl
  refine ⟨this, ?_, ?_, ?_⟩
  · have hη : IsPrimitiveRoot (ζ ^ f) (l ^ n) := hζ.pow hM rfl
    rw [IsCyclotomicExtension.iff_singleton]
    refine ⟨⟨_, hη⟩, fun x => ?_⟩
    set A := Algebra.adjoin F {b : L | b ^ l ^ n = 1}
    have h1 : ζ ^ f ∈ A := Algebra.subset_adjoin hη.pow_eq_one
    have h2 : ζ ^ l ^ n ∈ A := by
      rw [hk', pow_mul, ← hi, ← hal]
      exact A.pow_mem (A.algebraMap_mem z) _
    have h3 : ζ ∈ A := by
      have hc : Nat.Coprime f (l ^ n) := hfl.pow_right n
      have hc' : Nat.Coprime (f + l ^ n) (f * l ^ n) :=
        Nat.Coprime.mul_right (by simpa using hc.symm) (by simpa using hc)
      obtain ⟨a, -, ha⟩ := (hζ.pow_of_coprime _ hc').eq_pow_of_pow_eq_one hζ.pow_eq_one
      rw [← ha, pow_add]
      exact A.pow_mem (A.mul_mem h1 h2) a
    have h4 : Algebra.adjoin ℚ {ζ} = ⊤ := IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ
    have h5 : x ∈ Algebra.adjoin ℚ {ζ} := h4 ▸ Algebra.mem_top
    have h6 : Algebra.adjoin ℚ {ζ} ≤ A.restrictScalars ℚ := Algebra.adjoin_le (by simpa using h3)
    exact h6 h5
  · intro σ
    obtain ⟨t, ht⟩ := (sg (f * l ^ n) L).surjective (σ.restrictScalars ℚ)
    refine ⟨t, ?_, by rw [ht]; rfl⟩
    rw [MonoidHom.mem_ker, ← map_eq_one_iff _ (sg (f * l ^ e) F).injective]
    ext y
    apply i.injective
    have := relCyc_compat h F L i t y
    rw [ht] at this
    exact this.symm.trans (σ.commutes y)
  · intro t ht
    refine ⟨{ (sg (f * l ^ n) L t).toRingEquiv with commutes' := fun y => ?_ }, rfl⟩
    have := relCyc_compat h F L i t y
    rw [MonoidHom.mem_ker.1 ht, map_one] at this
    exact this
