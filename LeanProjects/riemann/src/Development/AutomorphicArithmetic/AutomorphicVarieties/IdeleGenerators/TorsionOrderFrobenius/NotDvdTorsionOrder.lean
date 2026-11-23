import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.ExtAlg
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal UpperTheory.V.Base

private theorem glue {G H : Type*} [CommGroup G] [CommGroup H] (p : G →* H)
    (f : G →* ℂˣ) (h : ∀ x, p x = 1 → f x = 1) : ∃ F : H →* ℂˣ, ∀ x, F (p x) = f x := by
  have hker : p.rangeRestrict.ker ≤ f.ker := by
    intro c hc
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hc
    rw [MonoidHom.mem_ker]
    exact h c hc
  let ω' : p.range →* ℂˣ :=
    p.rangeRestrict.liftOfSurjective p.rangeRestrict_surjective ⟨f, hker⟩
  have hω' : ∀ c, ω' (p.rangeRestrict c) = f c := fun c =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ c
  obtain ⟨F, hF⟩ := KStar.Choice.isDiv_complex_circle.1.exists_extension p.range ω'
  refine ⟨F, fun c => ?_⟩
  rw [← hω', ← hF]
  rfl

private theorem all_torsion (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (h2 : Module.finrank ℚ K = 2) (u : (𝓞 K)ˣ) : u ∈ Units.torsion K := by
  have hc : Fintype.card (InfinitePlace K) = 1 := by
    have := IsTotallyComplex.finrank K
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero]
    omega
  haveI : Subsingleton (InfinitePlace K) := Fintype.card_le_one_iff_subsingleton.1 hc.le
  rw [← Units.dirichletUnitTheorem.logEmbedding_eq_zero_iff]
  funext w
  exact absurd (Subsingleton.elim _ _) w.2

private theorem not_dvd_torsionOrder (K : Type) [Field K] [NumberField K] (l : ℕ) (hl : l.Prime) (hl2 : l ≠ 2)
    (hd : ¬ (l : ℤ) ∣ discr K) : ¬ l ∣ Units.torsionOrder K := by
  intro h
  haveI := Fact.mk hl
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Units.torsion K) l h
  have h1 : IsPrimitiveRoot x l := hx ▸ IsPrimitiveRoot.orderOf x
  have h2 : IsPrimitiveRoot (algebraMap (𝓞 K) K ((x : (𝓞 K)ˣ) : 𝓞 K)) l :=
    (IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.coe_submonoidClass_iff.2 h1)).map_of_injective
      (RingOfIntegers.coe_injective)
  have h3 := h2.intermediateField_adjoin_isCyclotomicExtension ℚ
  refine hd (Dvd.dvd.trans ?_ (discr_dvd_discr (IntermediateField.adjoin ℚ
    {algebraMap (𝓞 K) K ((x : (𝓞 K)ˣ) : 𝓞 K)}) K))
  rw [@IsCyclotomicExtension.Rat.discr_prime l _ _ _ _ (by convert h3 <;> first | rfl | exact Subsingleton.elim _ _)]
  have := hl.two_le
  exact Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) _

private theorem unit_eq (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (h2 : Module.finrank ℚ K = 2) {N : ℕ} (hN : 3 ≤ N) (u : (𝓞 K)ˣ) (n : ℕ)
    (h : (N : 𝓞 K) ∣ (u : 𝓞 K) - n) : u = 1 ∨ u = -1 := by
  haveI : Algebra.IsQuadraticExtension ℚ K := { finrank_eq_two' := h2 }
  haveI : IsCMField K := IsCMField.ofCMExtension ℚ K
  have hu := all_torsion K h2 u
  obtain ⟨y, hy⟩ := h
  have hyK : ((u : 𝓞 K) : K) - n = N * (y : K) := by
    simpa using congrArg (algebraMap (𝓞 K) K) hy
  have hc : ((u : 𝓞 K) : K)⁻¹ - n = N * IsCMField.complexConj K (y : K) := by
    have := congrArg (IsCMField.complexConj K) hyK
    rw [map_sub, map_mul, map_natCast, map_natCast] at this
    rw [← this]
    congr 1
    exact (IsCMField.complexConj_torsion K ⟨u, hu⟩).symm
  have hint : IsIntegral ℤ ((y : K) - IsCMField.complexConj K (y : K)) :=
    (y - IsCMField.ringOfIntegersComplexConj K y).isIntegral_coe
  have e : ((u : 𝓞 K) : K) - ((u : 𝓞 K) : K)⁻¹ = N * ((y : K) - IsCMField.complexConj K (y : K)) := by
    linear_combination hyK - hc
  have hlt : ∀ φ : K →+* ℂ, ‖φ ((y : K) - IsCMField.complexConj K (y : K))‖ < 1 := fun φ => by
    have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
    have h1 : ‖φ ((u : 𝓞 K) : K)‖ = 1 := (Units.mem_torsion K).1 hu (InfinitePlace.mk φ)
    have h4 := congrArg (fun t => ‖φ t‖) e
    simp only [map_mul, norm_mul, map_natCast, Complex.norm_natCast] at h4
    have h5 := norm_sub_le (φ ((u : 𝓞 K) : K)) (φ ((u : 𝓞 K) : K))⁻¹
    rw [norm_inv, h1, ← map_inv₀, ← map_sub, h4] at h5
    have := norm_nonneg (φ ((y : K) - IsCMField.complexConj K (y : K)))
    nlinarith
  have h0 : (y : K) - IsCMField.complexConj K (y : K) = 0 := by
    by_contra hb0
    obtain ⟨n, hn, hp⟩ := NumberField.Embeddings.pow_eq_one_of_norm_le_one K ℂ hb0 hint fun φ => (hlt φ).le
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    exact (hlt φ).ne (Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hp, map_one]) hn.ne')
  rw [h0, mul_zero, sub_eq_zero, eq_comm, inv_eq_iff_eq_inv, eq_comm, inv_eq_self₀] at e
  rcases e with e | e | e
  · right
    apply Units.ext
    apply RingOfIntegers.coe_injective
    simpa using e
  · exact absurd e (by simp)
  · left
    apply Units.ext
    apply RingOfIntegers.coe_injective
    simpa using e

private theorem int_dvd (K : Type) [Field K] [NumberField K] (N : ℕ) (a : ℤ) (h : (N : 𝓞 K) ∣ (a : 𝓞 K)) :
    (N : ℤ) ∣ a := by
  have := Ideal.comap_map_eq_self_of_faithfullyFlat (B := 𝓞 K) (Ideal.span {(N : ℤ)})
  rw [← Ideal.mem_span_singleton, ← this, Ideal.mem_comap, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton]
  simpa using h

theorem UpperTheory.V.Sd.Tw.fin :
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (l : ℕ), l.Prime → l ≠ 2 →
        ¬ (l : ℤ) ∣ discr K → ∀ (N : ℕ), 3 ≤ N → ∀ (χ : (ZMod N)ˣ →* ℂˣ), χ ^ 2 = 1 → χ (-1) = -1 → ∀ τ : K →+* ℂ,
        ∃ (e : (𝓞 K ⧸ Ideal.span {(N : 𝓞 K)})ˣ →* ℂˣ) (m : ℕ), 0 < m ∧ ¬ l ∣ m ∧ (∀ x, e x ^ m = 1) ∧
          (∀ u : (𝓞 K)ˣ, ((e (Units.map (Ideal.Quotient.mk (Ideal.span {(N : 𝓞 K)})).toMonoidHom u) : ℂˣ) : ℂ) =
            τ ((u : 𝓞 K) : K)) ∧
          ∀ (x : (𝓞 K ⧸ Ideal.span {(N : 𝓞 K)})ˣ) (n : ℕ) (h : n.Coprime N),
            (x : 𝓞 K ⧸ Ideal.span {(N : 𝓞 K)}) = (n : 𝓞 K ⧸ Ideal.span {(N : 𝓞 K)}) → e x = χ (ZMod.unitOfCoprime n h) := by
  intro K _ _ _ h2 l hl hl2 hd N hN χ hχ hχ1 τ
  haveI : NeZero N := ⟨by omega⟩
  have hN0 : (N : 𝓞 K ⧸ Ideal.span {(N : 𝓞 K)}) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(N : 𝓞 K)})), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  haveI := ringChar.charP (𝓞 K ⧸ Ideal.span {(N : 𝓞 K)})
  let j : ZMod N →+* 𝓞 K ⧸ Ideal.span {(N : 𝓞 K)} := ZMod.castHom (ringChar.dvd hN0) _
  have hj : Function.Injective j := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective a
    rw [map_intCast, ← map_intCast (Ideal.Quotient.mk (Ideal.span {(N : 𝓞 K)})), Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton] at ha
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd n N).2 (int_dvd K N n ha)
  let t : (𝓞 K)ˣ →* ℂˣ := Units.map (τ.comp (algebraMap (𝓞 K) K)).toMonoidHom
  obtain ⟨F, hF⟩ := glue ((Units.map j.toMonoidHom).coprod
    (Units.map (Ideal.Quotient.mk (Ideal.span {(N : 𝓞 K)})).toMonoidHom)) (χ.coprod t) (by
      rintro ⟨a, u⟩ h
      have h' : j a * Ideal.Quotient.mk (Ideal.span {(N : 𝓞 K)}) u = 1 := congrArg Units.val h
      change χ a * t u = 1
      have h3 : Ideal.Quotient.mk (Ideal.span {(N : 𝓞 K)}) u = j (a⁻¹ : (ZMod N)ˣ) := by
        have : j (a⁻¹ : (ZMod N)ˣ) * j a = 1 := by rw [← map_mul, Units.inv_mul, map_one]
        linear_combination j (a⁻¹ : (ZMod N)ˣ) * h' - Ideal.Quotient.mk (Ideal.span {(N : 𝓞 K)}) u * this
      have h4 := h3
      rw [← ZMod.natCast_zmod_val ((a⁻¹ : (ZMod N)ˣ) : ZMod N), map_natCast,
        ← map_natCast (Ideal.Quotient.mk (Ideal.span {(N : 𝓞 K)})), Ideal.Quotient.eq, Ideal.mem_span_singleton] at h4
      rcases unit_eq K h2 hN u _ h4 with rfl | rfl
      · have : a = 1 := by
          apply Units.ext
          apply hj
          simpa using h'
        rw [this, map_one, map_one, one_mul]
      · have : a = -1 := by
          apply Units.ext
          apply hj
          simpa [neg_eq_iff_eq_neg] using h'
        have ht : t (-1) = -1 := Units.ext (by simp [t])
        rw [this, hχ1, ht]
        simp)
  haveI : Finite (𝓞 K ⧸ Ideal.span {(N : 𝓞 K)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.2 (by omega))
  have hM : Nat.card (𝓞 K ⧸ Ideal.span {(N : 𝓞 K)})ˣ ≠ 0 := Nat.card_pos.ne'
  obtain ⟨s, m, hm, hsm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM l hl.ne_one
  have hw := not_dvd_torsionOrder K l hl hl2 hd
  have hw0 : Units.torsionOrder K ≠ 0 := fun h => hw (h ▸ dvd_zero _)
  have hcop : (l ^ s).Coprime (2 * Units.torsionOrder K) := by
    refine Nat.Coprime.pow_left _ (Nat.Coprime.mul_right ?_ ((Nat.Prime.coprime_iff_not_dvd hl).2 hw))
    exact (Nat.coprime_primes hl Nat.prime_two).2 hl2
  have hk := Nat.ModEq.pow_totient hcop
  have hφ : (2 * Units.torsionOrder K).totient ≠ 0 := (Nat.totient_pos.2 (by omega)).ne'
  obtain ⟨c, hc⟩ : l ^ s ∣ (l ^ s) ^ (2 * Units.torsionOrder K).totient := dvd_pow_self _ hφ
  have key : ∀ z : ℂˣ, z ^ (2 * Units.torsionOrder K) = 1 →
      z ^ ((l ^ s) ^ (2 * Units.torsionOrder K).totient) = z := fun z hz => by
    rw [pow_eq_pow_of_modEq hk hz, pow_one]
  refine ⟨F ^ ((l ^ s) ^ (2 * Units.torsionOrder K).totient), m, Nat.pos_of_ne_zero (fun h => hm (h ▸ dvd_zero _)),
    hm, fun x => ?_, fun u => ?_, fun x n h hx => ?_⟩
  · rw [MonoidHom.pow_apply, ← pow_mul, hc, mul_right_comm, ← hsm, pow_mul, ← map_pow, pow_card_eq_one', map_one,
      one_pow]
  · have h1 : F (Units.map (Ideal.Quotient.mk (Ideal.span {(N : 𝓞 K)})).toMonoidHom u) = t u := by
      simpa using hF (1, u)
    have h3 : u ^ Units.torsionOrder K = 1 := by
      have := all_torsion K h2 u
      rw [← Units.rootsOfUnity_eq_torsion] at this
      exact this
    rw [MonoidHom.pow_apply, h1, key _ (by rw [mul_comm, pow_mul, ← map_pow, h3, map_one, one_pow])]
    rfl
  · have h1 : x = Units.map j.toMonoidHom (ZMod.unitOfCoprime n h) := by
      apply Units.ext
      rw [hx]
      exact (map_natCast j n).symm
    have h3 : F x = χ (ZMod.unitOfCoprime n h) := by
      rw [h1]
      simpa using hF (ZMod.unitOfCoprime n h, 1)
    have h4 : χ (ZMod.unitOfCoprime n h) ^ 2 = 1 := DFunLike.congr_fun hχ _
    rw [MonoidHom.pow_apply, h3, key _ (by rw [pow_mul, h4, one_pow])]
