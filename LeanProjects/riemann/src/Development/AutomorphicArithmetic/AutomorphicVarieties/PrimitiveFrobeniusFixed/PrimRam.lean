import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsPrimitiveRootPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelLeIne

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem primRam_lift (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (r : ℕ) (hr : r.Prime)
    (A : ValuationSubring Ω) (hA : A.valuation (r : Ω) < 1) (u : (ZMod N)ˣ)
    (hu : u ∈ (ZMod.unitsMap (Nat.ordCompl_dvd N r)).ker) :
    ∃ σ ∈ Ine (F := ℚ) A, Chr.cls ℚ Ω N σ = u := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨v, hv⟩ := KStar.TotallyRealRoots.redPow_surjective (l := r) (N.factorization r)
    (ZMod.unitsMap (Nat.ordProj_dvd N r) u)
  obtain ⟨σ, hσ, hσv⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω r A hA v
  refine ⟨σ, hσ, ?_⟩
  apply (Chr.clsFacts ℚ Ω N).2.2.1
  refine (LDataCardLeFinrank.classIff Ω r N σ.toRingEquiv u).2 ⟨?_, ?_⟩
  · intro ζ hζ
    have hcop : (N / r ^ N.factorization r).Coprime r :=
      (Nat.coprime_ordCompl hr (NeZero.ne N)).symm
    have hfix := (LDataCardLeFinrank.ineFixRoots ℚ Ω r A hA (N / r ^ N.factorization r) hcop ζ hζ).2 σ hσ
    rw [MonoidHom.mem_ker.mp hu, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ,
      pow_one]
    exact hfix
  · rw [← hv, ← hσv]
    rfl

private theorem primRam_l (l : ℕ) [Fact l.Prime] (c : HV.Coef l) : ¬ IsUnit (l : c.O) := by
  intro hu
  haveI := c.fin
  haveI : Algebra.IsIntegral ℤ_[l] c.O := Algebra.IsIntegral.of_finite ℤ_[l] c.O
  have hker : RingHom.ker (algebraMap ℤ_[l] c.O) ≤ IsLocalRing.maximalIdeal ℤ_[l] :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
  obtain ⟨Q, hQ, hQc⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (IsLocalRing.maximalIdeal ℤ_[l]) hker
  have hl : ((l : ℤ_[l])) ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.subset_span rfl
  rw [← hQc, Ideal.mem_comap, map_natCast] at hl
  exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem Q hl hu)

private theorem primRam_unit (l : ℕ) [Fact l.Prime] (c : HV.Coef l) (n : ℕ) (hn : ¬ l ∣ n) (x : c.O) (hx : x ^ n = 1)
    (h1 : x ≠ 1) : IsUnit (x - 1) := by
  haveI := c.dvr
  by_contra hne
  have hm : x - 1 ∈ IsLocalRing.maximalIdeal c.O := (IsLocalRing.mem_maximalIdeal _).2 hne
  have hsum : ∑ i ∈ Finset.range n, x ^ i = 0 := by
    have h := mul_geom_sum x n
    rw [hx, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr h1)
  have hdiff : ∑ i ∈ Finset.range n, (x ^ i - 1) ∈ IsLocalRing.maximalIdeal c.O := by
    refine Ideal.sum_mem _ fun i _ => ?_
    obtain ⟨y, hy⟩ := sub_dvd_pow_sub_pow x 1 i
    rw [one_pow] at hy
    rw [hy]
    exact Ideal.mul_mem_right _ _ hm
  rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    zero_sub, neg_mem_iff] at hdiff
  have hlm : (l : c.O) ∈ IsLocalRing.maximalIdeal c.O :=
    (IsLocalRing.mem_maximalIdeal _).2 (primRam_l l c)
  have hcop : IsCoprime ((l : ℤ)) (n : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd (Fact.out)).2 hn)
  obtain ⟨a, b, hab⟩ := hcop.map (Int.castRingHom c.O)
  simp only [eq_intCast, Int.cast_natCast] at hab
  have h1m : (1 : c.O) ∈ IsLocalRing.maximalIdeal c.O := by
    rw [← hab]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hlm) (Ideal.mul_mem_left _ _ hdiff)
  exact (IsLocalRing.maximalIdeal.isMaximal c.O).ne_top ((Ideal.eq_top_iff_one _).2 h1m)

private theorem exists_prime_dvd_over_of_over_mul_iff (Ω : Type) [Field Ω] (A : ValuationSubring Ω)
    (hmul : ∀ m n : ℕ, Over A (m * n) ↔ Over A m ∨ Over A n) (n : ℕ) (hn : n ≠ 0) (h : Over A n) :
    ∃ r, r.Prime ∧ r ∣ n ∧ Over A r := by
  refine Nat.recOnMul (motive := fun n => n ≠ 0 → Over A n → ∃ r, r.Prime ∧ r ∣ n ∧ Over A r)
    ?_ ?_ ?_ ?_ n hn h
  · intro h0
    exact absurd rfl h0
  · intro _ h1
    simp [Over] at h1
  · intro p hp _ hpA
    exact ⟨p, hp, dvd_rfl, hpA⟩
  · intro a b iha ihb hab hAab
    rcases (hmul a b).1 hAab with ha | hb
    · obtain ⟨r, hr, hra, hrA⟩ := iha (left_ne_zero_of_mul hab) ha
      exact ⟨r, hr, hra.mul_right b, hrA⟩
    · obtain ⟨r, hr, hrb, hrA⟩ := ihb (right_ne_zero_of_mul hab) hb
      exact ⟨r, hr, hrb.mul_left a, hrA⟩

theorem UpperTheory.V.ML.primRam :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : HV.Coef l) (f : ℕ) [NeZero f] (ψ : DirichletCharacter c.O f), ψ.IsPrimitive → ¬ l ∣ orderOf ψ →
    (∀ A : ValuationSubring Ω, Over A f → ∃ g ∈ Ine (F := ℚ) A, IsUnit (((Chr.dirG ℚ Ω ψ g : c.Oˣ) : c.O) - 1)) ∧
    (∀ A : ValuationSubring Ω, ¬ Over A f → ∀ g ∈ Ine (F := ℚ) A, Chr.dirG ℚ Ω ψ g = 1) ∧ ∀ g : G ℚ Ω, Chr.dirG ℚ Ω ψ g ≠ 1 → IsUnit (((Chr.dirG ℚ Ω ψ g : c.Oˣ) : c.O) - 1) := by
  intro Ω _ inst _ l _ c f _ ψ hprim hord
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  have hpb := placeBasic Ω
  have hC : ∀ g : G ℚ Ω, Chr.dirG ℚ Ω ψ g ≠ 1 →
      IsUnit (((Chr.dirG ℚ Ω ψ g : c.Oˣ) : c.O) - 1) := by
    intro g hg
    apply primRam_unit l c (orderOf ψ) hord
    · show ((MulChar.toUnitHom ψ (Chr.cls ℚ Ω f g) : c.Oˣ) : c.O) ^ orderOf ψ = 1
      rw [MulChar.coe_toUnitHom, ← MulChar.pow_apply_coe, pow_orderOf_eq_one,
        MulChar.one_apply_coe]
    · intro h
      exact hg (Units.val_eq_one.mp h)
  refine ⟨?_, ?_, hC⟩
  · intro A hA
    obtain ⟨r, hr, hrf, hAr⟩ := exists_prime_dvd_over_of_over_mul_iff Ω A (hpb.2.2.1 A) f (NeZero.ne f) hA
    have hsub : ¬ (ZMod.unitsMap (Nat.ordCompl_dvd f r)).ker ≤ (MulChar.toUnitHom ψ).ker := by
      intro hle
      have hft := (DirichletCharacter.factorsThrough_iff_ker_unitsMap (χ := ψ)
        (Nat.ordCompl_dvd f r)).2 hle
      have hdvd := DirichletCharacter.conductor_dvd_of_mem_conductorSet ψ hft
      rw [(DirichletCharacter.isPrimitive_def ψ).1 hprim] at hdvd
      have hpos : 0 < f / r ^ f.factorization r := Nat.ordCompl_pos r (NeZero.ne f)
      have hlt : f / r ^ f.factorization r < f :=
        Nat.div_lt_self (Nat.pos_of_ne_zero (NeZero.ne f))
          (Nat.one_lt_pow (hr.factorization_pos_of_dvd (NeZero.ne f) hrf).ne' hr.one_lt)
      exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.2 hlt)
    obtain ⟨u, hu, hψu⟩ := SetLike.not_le_iff_exists.mp hsub
    obtain ⟨σ, hσ, hσu⟩ := primRam_lift Ω f r hr A hAr u hu
    refine ⟨σ, hσ, hC σ ?_⟩
    show MulChar.toUnitHom ψ (Chr.cls ℚ Ω f σ) ≠ 1
    rw [hσu]
    exact fun h => hψu (MonoidHom.mem_ker.mpr h)
  · intro A hA g hg
    have hk := (Chr.clsFacts ℚ Ω f).2.2.2.2 A hA hg
    show MulChar.toUnitHom ψ (Chr.cls ℚ Ω f g) = 1
    rw [MonoidHom.mem_ker.mp hk, map_one]
