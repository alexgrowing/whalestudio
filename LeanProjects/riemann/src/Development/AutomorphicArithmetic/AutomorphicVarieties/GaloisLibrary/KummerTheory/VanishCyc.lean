import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem exists_level_pow_dvd_of_not_finOrder (l : ℕ) [hl : Fact l.Prime] (u : ℤ_[l]ˣ) (hu : ¬ IsOfFinOrder u) (a : ℕ) :
    ∃ j : ℕ, ∀ m : ℤ, PadicInt.toZModPow j ((u ^ m : ℤ_[l]ˣ) : ℤ_[l]) = 1 → (l : ℤ) ^ (a + 1) ∣ m := by
  by_contra h
  push_neg at h
  apply hu
  have hK : 0 < l ^ a * (l - 1) :=
    Nat.mul_pos (pow_pos hl.out.pos a) (Nat.sub_pos_of_lt hl.out.one_lt)
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨l ^ a * (l - 1), hK, ?_⟩
  apply Units.ext
  apply PadicInt.ext_of_toZModPow.mp
  intro j
  obtain ⟨m, hm, hnd⟩ := h j
  obtain ⟨w, hwdef⟩ : ∃ w : (ZMod (l ^ j))ˣ, w = Units.map (PadicInt.toZModPow j).toMonoidHom u :=
    ⟨_, rfl⟩
  have hw : ∀ n : ℤ, ((w ^ n : (ZMod (l ^ j))ˣ) : ZMod (l ^ j)) =
      PadicInt.toZModPow j ((u ^ n : ℤ_[l]ˣ) : ℤ_[l]) := by
    intro n
    rw [hwdef, ← map_zpow]
    rfl
  have hwm : w ^ m = 1 := by
    apply Units.ext
    rw [hw, hm, Units.val_one]
  have hom : (orderOf w : ℤ) ∣ m := orderOf_dvd_iff_zpow_eq_one.mpr hwm
  haveI : NeZero (l ^ j) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  have hcard : orderOf w ∣ (l ^ j).totient := by
    rw [← ZMod.card_units_eq_totient]
    exact orderOf_dvd_card
  have hdiv : orderOf w ∣ l ^ a * (l - 1) := by
    rcases j with _ | i
    · simp only [pow_zero, Nat.totient_one, Nat.dvd_one] at hcard
      rw [hcard]
      exact one_dvd _
    · rw [Nat.totient_prime_pow_succ hl.out] at hcard
      rw [← Nat.dvd_gcd_mul_iff_dvd_mul] at hcard
      obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hl.out).mp (Nat.gcd_dvd_right (orderOf w) (l ^ i))
      have hba : b ≤ a := by
        by_contra hba
        push_neg at hba
        apply hnd
        have h1 : (l : ℤ) ^ b ∣ m := by
          have : l ^ b ∣ orderOf w := hb ▸ Nat.gcd_dvd_left _ _
          exact dvd_trans (by exact_mod_cast this) hom
        exact dvd_trans (pow_dvd_pow _ hba) h1
      rw [hb] at hcard
      exact hcard.trans (Nat.mul_dvd_mul_right (pow_dvd_pow l hba) _)
  have hwK : w ^ (l ^ a * (l - 1)) = 1 := orderOf_dvd_iff_pow_eq_one.mp hdiv
  have := hw ((l ^ a * (l - 1) : ℕ) : ℤ)
  rw [zpow_natCast, zpow_natCast, hwK, Units.val_one] at this
  rw [← this, Units.val_one, map_one]

private theorem exists_open_subgroup_cycZ_trivial_mod_pow (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [hl : Fact l.Prime] (j : ℕ) :
    ∃ H : Subgroup (G F Ω), IsOpen (H : Set (G F Ω)) ∧
      ∀ g ∈ H, PadicInt.toZModPow j ((cycZ F Ω l g : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.mpr hl.out.ne_zero⟩
  haveI : NeZero (l ^ j) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ j)
  haveI : FiniteDimensional F (IntermediateField.adjoin F ({ζ} : Set Ω)) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  refine ⟨(IntermediateField.adjoin F ({ζ} : Set Ω)).fixingSubgroup,
    IntermediateField.fixingSubgroup_isOpen _, fun g hg => ?_⟩
  have hgζ : g ζ = ζ :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg ζ (IntermediateField.mem_adjoin_simple_self F ζ)
  have hspec := cyclotomicCharacter.spec l (n := j) (MulSemiringAction.toRingAut (G F Ω) Ω g) ζ hζ.pow_eq_one
  change PadicInt.toZModPow j ((cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G F Ω) Ω g) : ℤ_[l]ˣ) : ℤ_[l]) = 1
  generalize PadicInt.toZModPow j ((cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G F Ω) Ω g) : ℤ_[l]ˣ) : ℤ_[l]) = z at hspec ⊢
  have h1 : ζ ^ 1 = ζ ^ z.val := by
    rw [pow_one, ← hspec]
    exact hgζ.symm
  have hu := hζ.isUnit_unit (NeZero.ne (l ^ j))
  have h1' : (hζ.isUnit (NeZero.ne (l ^ j))).unit ^ 1 = (hζ.isUnit (NeZero.ne (l ^ j))).unit ^ z.val := by
    apply Units.ext
    simpa using h1
  rw [pow_eq_pow_iff_modEq, ← hu.eq_orderOf] at h1'
  have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h1'.symm
  rw [ZMod.natCast_val, ZMod.cast_id', id, Nat.cast_one] at h2
  exact h2

theorem UpperTheory.V.Kum.vanishCyc :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] (φ : Uinf F Ω l → M) (γ : G F Ω), IsLocallyConstant φ → (∀ a b, φ (a * b) = φ a + φ b) → (∀ m : M, ∃ k : ℕ, l ^ k • m = 0) → ¬ IsOfFinOrder (cycZ F Ω l γ) →
    ∀ x : Uinf F Ω l, x.1 ∈ (Subgroup.zpowers γ).topologicalClosure → φ x = 0 := by
  intro F Ω _ _ _ _ _ l hl M _ φ γ hφ hmul htor hγ x hx
  have h1 : φ 1 = 0 := by simpa using hmul 1 1
  have hpow : ∀ y : Uinf F Ω l, ∀ n : ℕ, φ (y ^ n) = n • φ y := by
    intro y n
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ, hmul, ih, succ_nsmul]
  obtain ⟨W, hWo, hWeq⟩ := isOpen_induced_iff.mp (hφ.isOpen_fiber 0)
  have hW1 : (1 : G F Ω) ∈ W := by
    have : (1 : Uinf F Ω l) ∈ Subtype.val ⁻¹' W := by
      rw [hWeq]
      exact h1
    exact this
  obtain ⟨E, hE, hEW⟩ := (krullTopology_mem_nhds_one_iff F Ω W).mp (hWo.mem_nhds hW1)
  haveI := hE
  have hN : IsOpen (E.fixingSubgroup : Set (G F Ω)) := IntermediateField.fixingSubgroup_isOpen E
  have hNφ : ∀ y : Uinf F Ω l, y.1 ∈ E.fixingSubgroup → φ y = 0 := by
    intro y hy
    have : y ∈ Subtype.val ⁻¹' W := hEW hy
    rw [hWeq] at this
    exact this
  haveI : Finite (G F Ω ⧸ E.fixingSubgroup) := Subgroup.quotient_finite_of_isOpen _ hN
  obtain ⟨d, hd0, -, hdN⟩ := Subgroup.exists_pow_mem_of_index_ne_zero (Subgroup.index_ne_zero_of_finite (H := E.fixingSubgroup)) γ
  obtain ⟨a, d', hd'l, hdd⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd0.ne' l hl.out.ne_one
  obtain ⟨j, hj⟩ := exists_level_pow_dvd_of_not_finOrder l (cycZ F Ω l γ) hγ a
  obtain ⟨H, hHo, hH⟩ := exists_open_subgroup_cycZ_trivial_mod_pow F Ω l j
  have ho : IsOpen ((fun g => x.1⁻¹ * g) ⁻¹' ((E.fixingSubgroup : Set (G F Ω)) ∩ (H : Set (G F Ω)))) :=
    (hN.inter hHo).preimage (continuous_const.mul continuous_id)
  have hxo : x.1 ∈ (fun g => x.1⁻¹ * g) ⁻¹' ((E.fixingSubgroup : Set (G F Ω)) ∩ (H : Set (G F Ω))) := by
    simp only [Set.mem_preimage, inv_mul_cancel, Set.mem_inter_iff, SetLike.mem_coe]
    exact ⟨one_mem _, one_mem _⟩
  have hx' : x.1 ∈ closure ((Subgroup.zpowers γ : Subgroup (G F Ω)) : Set (G F Ω)) := by
    rw [← Subgroup.topologicalClosure_coe]
    exact hx
  obtain ⟨g, hgo, hgz⟩ := mem_closure_iff.mp hx' _ ho hxo
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hgz
  obtain ⟨hνN, hνH⟩ := hgo
  have hcx : cycZ F Ω l x.1 = 1 := (Subgroup.mem_inf.mp x.2).2
  have hcyc : PadicInt.toZModPow j ((cycZ F Ω l γ ^ m : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
    have := hH _ hνH
    rwa [map_mul, map_inv, hcx, inv_one, one_mul, map_zpow] at this
  have hma : (l : ℤ) ^ a ∣ m := (pow_dvd_pow _ (Nat.le_succ a)).trans (hj m hcyc)
  have hcl : closure ((Subgroup.zpowers γ : Subgroup (G F Ω)) : Set (G F Ω)) ⊆ {y | y * γ = γ * y} := by
    apply closure_minimal
    · intro y hy
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.self_zpow γ i).symm.eq
    · exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  have hxγ : Commute x.1 γ := hcl hx'
  have hxν : Commute x.1 (x.1⁻¹ * γ ^ m) := (Commute.refl x.1).inv_right.mul_right (hxγ.zpow_right m)
  have hexp : (γ ^ m) ^ d' = x.1 ^ d' * (x.1⁻¹ * γ ^ m) ^ d' := by
    rw [← hxν.mul_pow, mul_inv_cancel_left]
  have hγN : (γ ^ m) ^ d' ∈ E.fixingSubgroup := by
    obtain ⟨t, ht⟩ := hma
    have : (γ ^ m) ^ d' = (γ ^ d) ^ t := by
      rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, ht, hdd]
      congr 1
      push_cast
      ring
    rw [this]
    exact zpow_mem hdN t
  have hxN : (x ^ d').1 ∈ E.fixingSubgroup := by
    have : (x ^ d').1 = (γ ^ m) ^ d' * ((x.1⁻¹ * γ ^ m) ^ d')⁻¹ := by
      rw [hexp, mul_inv_cancel_right]
      rfl
    rw [this]
    exact mul_mem hγN (inv_mem (pow_mem hνN d'))
  have h0 : d' • φ x = 0 := by
    rw [← hpow]
    exact hNφ _ hxN
  obtain ⟨k, hk⟩ := htor (φ x)
  have ho1 : addOrderOf (φ x) ∣ d' := addOrderOf_dvd_of_nsmul_eq_zero h0
  have ho2 : addOrderOf (φ x) ∣ l ^ k := addOrderOf_dvd_of_nsmul_eq_zero hk
  have hcop : Nat.Coprime d' (l ^ k) :=
    Nat.Coprime.pow_right _ (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hl.out).mpr hd'l))
  exact AddMonoid.addOrderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one (by rw [← hcop.gcd_eq_one]; exact Nat.dvd_gcd ho1 ho2))
