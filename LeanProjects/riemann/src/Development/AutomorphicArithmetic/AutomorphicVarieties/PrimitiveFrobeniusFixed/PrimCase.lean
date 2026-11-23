import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsPrimitiveRootPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.RatPlace
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ShaToShT
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.FrobFix
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ZeNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PrimRam
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.GalBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Primeq
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Primmem

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem valuation_natCast_le_one_primitive_frobenius_fixed {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (n : ℕ) :
    A.valuation (n : Ω) ≤ 1 := by
  have h := A.valuation_le_one (n : A)
  simpa using h

private theorem over_mul {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (m n : ℕ) :
    Over A (m * n) ↔ Over A m ∨ Over A n := by
  have hm := valuation_natCast_le_one_primitive_frobenius_fixed A m
  have hn := valuation_natCast_le_one_primitive_frobenius_fixed A n
  simp only [Over, Nat.cast_mul, map_mul]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have h1 : A.valuation (m : Ω) = 1 := le_antisymm hm hc.1
    have h2 : A.valuation (n : Ω) = 1 := le_antisymm hn hc.2
    rw [h1, h2, one_mul] at h
    exact lt_irrefl _ h
  · rintro (h | h)
    · calc A.valuation (m : Ω) * A.valuation (n : Ω) ≤ A.valuation (m : Ω) * 1 := mul_le_mul' le_rfl hn
        _ = A.valuation (m : Ω) := mul_one _
        _ < 1 := h
    · calc A.valuation (m : Ω) * A.valuation (n : Ω) ≤ 1 * A.valuation (n : Ω) := mul_le_mul' hm le_rfl
        _ = A.valuation (n : Ω) := one_mul _
        _ < 1 := h

private theorem over_pow {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (l k : ℕ) (h : Over A (l ^ k)) : Over A l := by
  by_contra hc
  have h1 : A.valuation (l : Ω) = 1 := le_antisymm (valuation_natCast_le_one_primitive_frobenius_fixed A l) (not_lt.mp hc)
  simp only [Over, Nat.cast_pow, map_pow, h1, one_pow] at h
  exact lt_irrefl _ h

private theorem over_pow_iff_over_of_one_le {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (l m : ℕ) (hm : 1 ≤ m) :
    Over A (l ^ m) ↔ Over A l := by
  constructor
  · exact over_pow A l m
  · intro h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [pow_add, pow_one, over_mul]
    exact Or.inl h

private theorem over_lev {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (l f m : ℕ) (hm : 1 ≤ m) :
    Over A (ordCompl[l] f * l ^ m) ↔ Over A (f * l) := by
  have hf : f * l = ordCompl[l] f * l ^ f.factorization l * l := by
    rw [mul_comm (ordCompl[l] f), Nat.ordProj_mul_ordCompl_eq_self]
  rw [hf, over_mul A (ordCompl[l] f * l ^ f.factorization l) l, over_mul A (ordCompl[l] f) (l ^ f.factorization l),
    over_mul A (ordCompl[l] f) (l ^ m), over_pow_iff_over_of_one_le A l m hm]
  constructor
  · rintro (h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
  · rintro ((h | h) | h)
    · exact Or.inl h
    · exact Or.inr (over_pow A l _ h)
    · exact Or.inr h

private theorem shT_congr {Ω : Type} [Field Ω] [Algebra ℚ Ω] {O W : Type} [CommRing O] [AddCommGroup W] [Module O W]
    (α : G ℚ Ω →* Oˣ) (δ : G ℚ Ω) {F F' : ℕ} (h : ∀ A : ValuationSubring Ω, Over A F ↔ Over A F') (a : O) :
    ShT W α δ F a = ShT W α δ F' a := by
  ext c
  show (_ ∧ _ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _ ∧ _ ∧ _)
  simp only [h]

private theorem isUnit_inv_sub_one_iff_isUnit_sub_one {R : Type} [CommRing R] (u : Rˣ) :
    IsUnit ((↑u⁻¹ : R) - 1) ↔ IsUnit ((u : R) - 1) := by
  have hx : ((↑u⁻¹ : R) - 1) = -(↑u⁻¹ : R) * ((u : R) - 1) := by
    rw [neg_mul, mul_sub, Units.inv_mul, mul_one, neg_sub]
  rw [hx, IsUnit.mul_iff]
  exact ⟨fun h => h.2, fun h => ⟨(Units.isUnit _).neg, h⟩⟩

private theorem prim_case (hR : Rec) (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [hl : Fact l.Prime]
    (c : HV.Coef l) (h2 : l ≠ 2) (f : ℕ) [NeZero f] (ψ : DirichletCharacter c.O f) (e : ℕ) (he : 1 ≤ e)
    (hp : ψ.IsPrimitive) (ho : ¬ l ∣ orderOf ψ) (hs : ψ (-1) = (-1) ^ (e + 1)) (a : c.O)
    (ha : (a : PadicAlgCl l) = alN (e + 1) (ψ.ringHomComp c.O.val.toRingHom)) :
    Chr.V l e (Chr.dirG ℚ Ω ψ) ≤ IsDiscreteValuationRing.addVal c.O a := by
  haveI := c.dvr
  haveI := c.fin
  have hl2 : ¬ l ∣ 2 := by
    intro h
    exact h2 ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).mp h)
  obtain ⟨hram, hunr, hunit⟩ := primRam Ω l c f ψ hp ho
  have hχ : ∀ A : ValuationSubring Ω, ¬ Over A l → ∀ g ∈ Ine A, chiO ℚ Ω l c.O g = 1 := by
    intro A hA g hg
    have hk := (places ℚ Ω l A).2.2.2 hA hg
    rw [MonoidHom.mem_ker] at hk
    simp [chiO, hk]
  have hαg : ∀ g, chiO ℚ Ω l c.O g = 1 →
      (Chr.Psi l e (Chr.dirG ℚ Ω ψ))⁻¹ g = (Chr.dirG ℚ Ω ψ g)⁻¹ := by
    intro g hg
    simp [Chr.Psi, hg]
  unfold Chr.V Chr.VS
  rw [Chr.rho_eq]
  by_cases hex : ∃ g, IsUnit ((((Chr.Psi l e (Chr.dirG ℚ Ω ψ))⁻¹ g : c.Oˣ) : c.O) - ((chiO ℚ Ω l c.O g : c.Oˣ) : c.O))
  · have hfacts := dvrFacts l c.O
    have hlnu : ¬ IsUnit (l : c.O) := by
      rintro ⟨u, hu⟩
      have h0 := IsDiscreteValuationRing.addVal_eq_zero_of_unit u
      rw [hu, ← hfacts.2.2.2.2.2.2.2.1] at h0
      exact hfacts.2.2.2.2.2.1 h0
    obtain ⟨m₁, b₁, hNZ₁, σ₁, hD₁, -, -, -, -⟩ := zEval Ω l c h2 f ψ e he hp hs hex a ha 1 one_ne_zero
    obtain ⟨δ, hδ⟩ := (galBasic Ω (f / l ^ f.factorization l * l ^ m₁) (NeZero.ne _)).2.2.2.1 (-1)
    have hodd := hD₁.odd δ hδ
    have hδu : IsUnit ((((Chr.Psi l e (Chr.dirG ℚ Ω ψ))⁻¹ δ : c.Oˣ) : c.O) - 1) := by
      have hmax : ((((Chr.Psi l e (Chr.dirG ℚ Ω ψ))⁻¹ δ : c.Oˣ) : c.O) + 1) ∈ IsLocalRing.maximalIdeal c.O := by
        obtain ⟨k, hk⟩ := hodd
        rw [hk, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        apply hlnu
        have hpow : IsUnit ((l : c.O) ^ m₁) := isUnit_of_mul_isUnit_left hu
        exact (isUnit_pow_iff (by have := hD₁.pos; omega)).mp hpow
      by_contra hnu
      have h2m : ((((Chr.Psi l e (Chr.dirG ℚ Ω ψ))⁻¹ δ : c.Oˣ) : c.O) - 1) ∈ IsLocalRing.maximalIdeal c.O :=
        (IsLocalRing.mem_maximalIdeal _).mpr hnu
      have hsub := Ideal.sub_mem _ hmax h2m
      rw [show ((((Chr.Psi l e (Chr.dirG ℚ Ω ψ))⁻¹ δ : c.Oˣ) : c.O) + 1) -
          ((((Chr.Psi l e (Chr.dirG ℚ Ω ψ))⁻¹ δ : c.Oˣ) : c.O) - 1) = ((2 : ℕ) : c.O) by push_cast; ring] at hsub
      exact (IsLocalRing.mem_maximalIdeal _).mp hsub (hfacts.2.2.2.2.2.2.2.2 2 hl2)
    refine shaToShT Ω l c.O _ δ hδu (f * l) (Nat.mul_ne_zero (NeZero.ne f) hl.out.ne_zero) ?_ ?_ _ ?_
    · intro A hA g hg
      rw [over_mul, not_or] at hA
      rw [hαg g (hχ A hA.2 g hg), hunr A hA.1 g hg, inv_one]
    · intro A hA hAl
      have hf : Over A f := by
        rcases (over_mul A f l).mp hA with h | h
        · exact h
        · exact absurd h hAl
      obtain ⟨g, hg, hu⟩ := hram A hf
      refine ⟨g, hg, ?_⟩
      rw [hαg g (hχ A hAl g hg), isUnit_inv_sub_one_iff_isUnit_sub_one]
      exact hu
    · intro a₀ ha₀
      obtain ⟨m, b, hNZ, σ, hD, hb, hσ, hdiv, hza⟩ := zEval Ω l c h2 f ψ e he hp hs hex a ha a₀ ha₀
      have hc := count hR Ω l c.O (f / l ^ f.factorization l) m _ b _ hD hb δ hδu σ hσ a₀ hdiv
      rw [shT_congr _ δ (F' := f * l) (fun A => over_lev A l f m hD.pos)] at hc
      exact hc.trans (IsDiscreteValuationRing.addVal_le_iff_dvd.mpr hza)
  · push_neg at hex
    rw [exc Ω l c.O h2 _ hex ?_, Module.length_bot]
    · exact zero_le
    · intro A hA g hg
      rw [hαg g (hχ A hA g hg)]
      by_contra hne
      have h1 : Chr.dirG ℚ Ω ψ g ≠ 1 := fun h => hne (by rw [h, inv_one])
      have hx := hex g
      rw [hαg g (hχ A hA g hg), hχ A hA g hg, Units.val_one, isUnit_inv_sub_one_iff_isUnit_sub_one] at hx
      exact hx (hunit g h1)

private theorem lev_case (hR : Rec) (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [hl : Fact l.Prime]
    (c : HV.Coef l) (h2 : l ≠ 2) (f N : ℕ) [NeZero f] [NeZero N] (h : f ∣ N) (φ : DirichletCharacter c.O f) (e : ℕ)
    (he : 1 ≤ e) (hp : φ.IsPrimitive) (ho : ¬ l ∣ orderOf (DirichletCharacter.changeLevel h φ))
    (hs : DirichletCharacter.changeLevel h φ (-1) = (-1) ^ (e + 1)) (a : c.O)
    (ha : (a : PadicAlgCl l) = alN (e + 1) ((DirichletCharacter.changeLevel h φ).ringHomComp c.O.val.toRingHom)) :
    Chr.V l e (Chr.dirG ℚ Ω (DirichletCharacter.changeLevel h φ)) ≤ IsDiscreteValuationRing.addVal c.O a := by
  haveI := c.dvr
  haveI := c.fin
  have hG : Chr.dirG ℚ Ω (DirichletCharacter.changeLevel h φ) = Chr.dirG ℚ Ω φ := by
    unfold Chr.dirG
    rw [DirichletCharacter.changeLevel_toUnitHom, MonoidHom.comp_assoc, (Chr.clsFacts ℚ Ω N).2.1 f h]
  have ho' : ¬ l ∣ orderOf φ := by
    rwa [orderOf_injective _ (DirichletCharacter.changeLevel_injective h) φ] at ho
  have hs' : φ (-1) = (-1) ^ (e + 1) := by
    have hc := DirichletCharacter.changeLevel_eq_cast_of_dvd' (χ := φ) h (a := -1) isCoprime_one_left.neg_left
    push_cast at hc
    rw [← hc]
    exact hs
  have hrc : (DirichletCharacter.changeLevel h φ).ringHomComp c.O.val.toRingHom =
      DirichletCharacter.changeLevel h (φ.ringHomComp c.O.val.toRingHom) := by
    ext u
    simp [MulChar.ringHomComp_apply, DirichletCharacter.changeLevel_eq_cast_of_dvd]
  have hmem : alN (e + 1) (φ.ringHomComp c.O.val.toRingHom) ∈ c.O :=
    (Bern.b_primmem (e + 1) (φ.ringHomComp c.O.val.toRingHom)).2.1 c.O.toSubring
      (fun u => by simp [MulChar.ringHomComp_apply])
  obtain ⟨k, hk⟩ := Bern.den_dvd h (e + 1)
  have hdvd : (⟨_, hmem⟩ : c.O) ∣ a := by
    refine ⟨(k : c.O), Subtype.ext ?_⟩
    rw [ha, hrc]
    simp only [alN, ((Bern.b_primeq (e + 1) (φ.ringHomComp c.O.val.toRingHom)).2 N h).1, hk]
    push_cast
    ring
  have hP := prim_case hR Ω l c h2 f φ e he hp ho' hs' ⟨_, hmem⟩ rfl
  rw [hG]
  exact hP.trans (IsDiscreteValuationRing.addVal_le_iff_dvd.mpr hdvd)

theorem UpperTheory.V.ML.vChar :
    Rec → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : HV.Coef l), l ≠ 2 → ∀ (N : ℕ) [NeZero N] (ψ : DirichletCharacter c.O N) (e : ℕ), 1 ≤ e → ¬ l ∣ orderOf ψ → ψ (-1) = (-1) ^ (e + 1) →
    ∀ a : c.O, (a : PadicAlgCl l) = alN (e + 1) (ψ.ringHomComp c.O.val.toRingHom) → Chr.V l e (Chr.dirG ℚ Ω ψ) ≤ IsDiscreteValuationRing.addVal c.O a := by
  intro hR Ω _ _ _ l _ c h2 N _ ψ e he ho hs a ha
  haveI : NeZero ψ.conductor := ⟨ψ.conductor_ne_zero⟩
  have key := lev_case hR Ω l c h2 ψ.conductor N ψ.conductor_dvd_level ψ.primitiveCharacter e he
    ψ.primitiveCharacter_isPrimitive
  rw [DirichletCharacter.changeLevel_primitiveCharacter] at key
  exact key ho hs a ha
