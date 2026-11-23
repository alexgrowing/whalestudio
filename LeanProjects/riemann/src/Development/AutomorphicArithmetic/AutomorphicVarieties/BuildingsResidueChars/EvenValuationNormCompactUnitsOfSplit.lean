import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IrreducibleParity.Fv

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PS

section SlopeTestRemainingChoices

variable {K : Type} [Field K] {τ r r' : K}

private def phiK (τ r : K) (h : r * r = -1 + τ * r) : Etau K τ →ₐ[K] K where
  toFun x := x.re + x.im * r
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' x y := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    linear_combination (-(x.im * y.im)) * h
  map_zero' := by simp
  map_add' x y := by simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]; ring
  commutes' a := by simp [QuadraticAlgebra.algebraMap_eq]

private lemma phiK_apply (h : r * r = -1 + τ * r) (x : Etau K τ) : phiK τ r h x = x.re + x.im * r := rfl

private lemma phiK_star (h : r * r = -1 + τ * r) (h' : r' * r' = -1 + τ * r') (hs : r + r' = τ) (x : Etau K τ) :
    phiK τ r h (star x) = phiK τ r' h' x := by
  simp only [phiK_apply, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
  linear_combination (-x.im) * hs

private lemma phiK_norm (h : r * r = -1 + τ * r) (h' : r' * r' = -1 + τ * r') (hs : r + r' = τ) (hp : r * r' = 1)
    (x : Etau K τ) : QuadraticAlgebra.norm x = phiK τ r h x * phiK τ r' h' x := by
  simp only [phiK_apply, QuadraticAlgebra.norm_def]
  linear_combination (-(x.re * x.im)) * hs - x.im ^ 2 * hp

private lemma phiK_ne (h : r * r = -1 + τ * r) (x : (Etau K τ)ˣ) : phiK τ r h (x : Etau K τ) ≠ 0 :=
  (x.isUnit.map (phiK τ r h)).ne_zero

private lemma phiK_inv (h : r * r = -1 + τ * r) (x : (Etau K τ)ˣ) :
    phiK τ r h ((x⁻¹ : (Etau K τ)ˣ) : Etau K τ) = (phiK τ r h (x : Etau K τ))⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, Units.inv_mul, map_one]

private lemma phiK_quo (h : r * r = -1 + τ * r) (h' : r' * r' = -1 + τ * r') (hs : r + r' = τ) (x : (Etau K τ)ˣ) :
    phiK τ r h (quo x) = phiK τ r h (x : Etau K τ) * (phiK τ r' h' (x : Etau K τ))⁻¹ := by
  rw [quo, map_mul, phiK_star h h' hs, phiK_inv]

private lemma phiK_inj (h : r * r = -1 + τ * r) (h' : r' * r' = -1 + τ * r') (hne : r ≠ r') :
    Function.Injective ((phiK τ r h).prod (phiK τ r' h')) := by
  intro x y hxy
  have h1 : x.re + x.im * r = y.re + y.im * r := congrArg Prod.fst hxy
  have h2 : x.re + x.im * r' = y.re + y.im * r' := congrArg Prod.snd hxy
  have h3 : x.im = y.im := by
    have : (x.im - y.im) * (r - r') = 0 := by linear_combination h1 - h2
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hne))
  ext
  · rw [h3] at h1; exact add_right_cancel h1
  · exact h3

private lemma phiK_surj (h : r * r = -1 + τ * r) (h' : r' * r' = -1 + τ * r') (hne : r ≠ r') (a b : K) :
    ∃ x : Etau K τ, phiK τ r h x = a ∧ phiK τ r' h' x = b := by
  have := sub_ne_zero.2 hne
  refine ⟨⟨a - (a - b) / (r - r') * r, (a - b) / (r - r')⟩, ?_, ?_⟩
  · simp [phiK_apply]
  · simp only [phiK_apply]; field_simp; ring

private lemma phiK_surjU (h : r * r = -1 + τ * r) (h' : r' * r' = -1 + τ * r') (hne : r ≠ r') (a b : K)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ x : (Etau K τ)ˣ, phiK τ r h x = a ∧ phiK τ r' h' x = b := by
  obtain ⟨x, hx1, hx2⟩ := phiK_surj h h' hne a b
  obtain ⟨y, hy1, hy2⟩ := phiK_surj h h' hne a⁻¹ b⁻¹
  have hxy : x * y = 1 := by
    apply phiK_inj h h' hne
    refine Prod.ext ?_ ?_
    · simp only [AlgHom.prod_apply, map_mul, map_one, hx1, hy1]
      exact mul_inv_cancel₀ ha
    · simp only [AlgHom.prod_apply, map_mul, map_one, hx2, hy2]
      exact mul_inv_cancel₀ hb
  exact ⟨⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, hx1, hx2⟩

private lemma phiK_int (O : Type) [CommRing O] [Algebra O K]
    (h : r * r = -1 + τ * r) (h' : r' * r' = -1 + τ * r') (hne : r ≠ r') (x : Etau K τ) :
    IsIntegral O x ↔ IsIntegral O (phiK τ r h x) ∧ IsIntegral O (phiK τ r' h' x) := by
  constructor
  · intro hx
    exact ⟨hx.map ((phiK τ r h).restrictScalars O), hx.map ((phiK τ r' h').restrictScalars O)⟩
  · rintro ⟨ha, hb⟩
    set a := phiK τ r h x
    set b := phiK τ r' h' x
    let f : K →ₐ[O] Etau K τ := IsScalarTower.toAlgHom O K (Etau K τ)
    have ha' : IsIntegral O (algebraMap K (Etau K τ) a) := ha.map f
    have hb' : IsIntegral O (algebraMap K (Etau K τ) b) := hb.map f
    have hroot : (x - algebraMap K (Etau K τ) a) * (x - algebraMap K (Etau K τ) b) = 0 := by
      apply phiK_inj h h' hne
      refine Prod.ext ?_ ?_
      · simp only [AlgHom.prod_apply, map_mul, map_sub, AlgHom.commutes, map_zero, Prod.fst_zero]
        simp [a]
      · simp only [AlgHom.prod_apply, map_mul, map_sub, AlgHom.commutes, map_zero, Prod.snd_zero]
        simp [b]
    let C := integralClosure O (Etau K τ)
    have hxC : IsIntegral C x := by
      refine ⟨(Polynomial.X - Polynomial.C (⟨_, ha'⟩ : C)) * (Polynomial.X - Polynomial.C (⟨_, hb'⟩ : C)),
        (Polynomial.monic_X_sub_C _).mul (Polynomial.monic_X_sub_C _), ?_⟩
      simp only [Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C]
      exact hroot
    exact isIntegral_trans x hxC

end SlopeTestRemainingChoices

theorem UpperTheory.evenValuation_norm_compactUnits_of_split :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → IsSquare (τ ^ 2 - 4) → (∀ c ∈ Cint O τ, EvenVal O (QuadraticAlgebra.norm ((c : (Etau K τ)ˣ) : Etau K τ))) ∧ ∀ y : (Etau K τ)ˣ, EvenVal O (QuadraticAlgebra.norm (y : Etau K τ)) → ∃ z : (Etau K τ)ˣ, ∃ c ∈ Cint O τ, y = c * z ^ 2 := by
  intro O K _ _ _ _ _ Δ τ hL hτ hsq
  haveI := hL.frac
  have h2 : (2 : K) ≠ 0 := by
    have e := (hL.two).map (algebraMap O K)
    rw [map_ofNat] at e
    exact e.ne_zero
  obtain ⟨s, hs⟩ := hsq
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hτ
    rw [hs, mul_zero]
  set r : K := (τ + s) / 2 with hrE
  set r' : K := (τ - s) / 2 with hr'E
  have hr : r * r = -1 + τ * r := by
    rw [hrE]
    field_simp
    linear_combination (-1 : K) * hs
  have hr' : r' * r' = -1 + τ * r' := by
    rw [hr'E]
    field_simp
    linear_combination (-1 : K) * hs
  have hsum : r + r' = τ := by
    rw [hrE, hr'E]
    field_simp
    ring
  have hsum' : r' + r = τ := by rw [add_comm]; exact hsum
  have hprod : r * r' = 1 := by
    rw [hrE, hr'E]
    field_simp
    linear_combination hs
  have hne : r ≠ r' := by
    intro e
    apply hs0
    have e2 : r - r' = s := by
      rw [hrE, hr'E]
      field_simp
      ring
    rw [← e2, e, sub_self]
  have hint : ∀ v : K, (∃ w : O, algebraMap O K w = v) → IsIntegral O v := by
    rintro v ⟨w, rfl⟩
    exact isIntegral_algebraMap
  have huv : ∀ (u : Oˣ) (v : K), v = algebraMap O K (u : O) → IsIntegral O v ∧ IsIntegral O v⁻¹ := by
    intro u v hv
    refine ⟨hint v ⟨u, hv.symm⟩, hint v⁻¹ ⟨(u⁻¹ : Oˣ), ?_⟩⟩
    rw [hv, map_units_inv]
  have hcint : ∀ (c : (Etau K τ)ˣ) (u : Oˣ),
      phiK τ r hr (c : Etau K τ) * (phiK τ r' hr' (c : Etau K τ))⁻¹ = algebraMap O K (u : O) →
      c ∈ Cint O τ := by
    intro c u hu
    obtain ⟨i1, i2⟩ := huv u _ hu
    have e2 : phiK τ r' hr' (c : Etau K τ) * (phiK τ r hr (c : Etau K τ))⁻¹
        = (phiK τ r hr (c : Etau K τ) * (phiK τ r' hr' (c : Etau K τ))⁻¹)⁻¹ := by
      rw [mul_inv, inv_inv, mul_comm]
    refine ⟨?_, ?_⟩
    · rw [phiK_int O hr hr' hne, phiK_quo hr hr' hsum, phiK_quo hr' hr hsum', e2]
      exact ⟨i1, i2⟩
    · rw [phiK_int O hr hr' hne, phiK_quo hr hr' hsum, phiK_quo hr' hr hsum', phiK_inv, phiK_inv,
        inv_inv, inv_inv]
      refine ⟨?_, ?_⟩
      · rw [mul_comm, e2]
        exact i2
      · rw [mul_comm]
        exact i1
  refine ⟨?_, ?_⟩
  · intro c hc
    obtain ⟨hc1, -⟩ := hc
    rw [phiK_int O hr hr' hne, phiK_quo hr hr' hsum, phiK_quo hr' hr hsum'] at hc1
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 hc1.1
    obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.1 hc1.2
    have hA := phiK_ne hr c
    have hB := phiK_ne hr' c
    have hab : a * b = 1 := by
      apply IsFractionRing.injective O K
      rw [map_mul, ha, hb, map_one]
      field_simp
    refine ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, phiK τ r' hr' (c : Etau K τ), hB, ?_⟩
    rw [phiK_norm hr hr' hsum hprod, Units.val_mk, ha]
    field_simp
  · rintro y ⟨u, t, ht, hy⟩
    have hA := phiK_ne hr y
    have hB := phiK_ne hr' y
    obtain ⟨z, hz1, hz2⟩ := phiK_surjU hr hr' hne 1 (phiK τ r' hr' (y : Etau K τ) / t) one_ne_zero
      (div_ne_zero hB ht)
    refine ⟨z, y * (z ^ 2)⁻¹, ?_, (inv_mul_cancel_right y (z ^ 2)).symm⟩
    apply hcint _ u
    rw [Units.val_mul, map_mul, map_mul, phiK_inv, phiK_inv, Units.val_pow_eq_pow_val, map_pow,
      map_pow, hz1, hz2]
    have hn := phiK_norm hr hr' hsum hprod (y : Etau K τ)
    rw [hy] at hn
    field_simp
    linear_combination (-1 : K) * hn
