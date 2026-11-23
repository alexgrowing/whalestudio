import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.FibreStC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.EqZeroOfSecTraceMulEqZero

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module

variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}

theorem coord_ne_zero {ι : Type*} (y : ι → Ω) (h : coordIdeal ℤ y = ⊥) (k : ι) : y k ≠ 0 := by
  intro hk
  have hmem : (MvPolynomial.X k : MvPolynomial ι ℤ) ∈ coordIdeal ℤ y := by
    rw [coordIdeal, RingHom.mem_ker, coneMap]
    simp [hk]
  rw [h, Ideal.mem_bot] at hmem
  exact MvPolynomial.X_ne_zero k hmem

theorem div_mem_fnField (x : κ → Ω) (i j : κ) : x i / x j ∈ fnField x := by
  exact IntermediateField.subset_adjoin ℚ {t | ∃ i j, t = x i / x j} ⟨i, j, rfl⟩

theorem deh_mem_fnField {ι : Type*} (y : ι → Ω) (i₀ : ι) (m : MvPolynomial ι ℤ) :
    deh y i₀ m ∈ fnField y := by
  rw [deh_apply]
  induction m using MvPolynomial.induction_on
  · rw [MvPolynomial.eval₂_C]
    simpa using intCast_mem (fnField y) _
  · rw [MvPolynomial.eval₂_add]
    exact add_mem ‹_› ‹_›
  · rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    exact mul_mem ‹_› (div_mem_fnField y _ i₀)

def dehK (y : Fin (D + 1) → Ω) : MvPolynomial (Fin (D + 1)) ℤ →+* fnField y :=
  (deh y 0).codRestrict (fnField y).toSubfield.toSubring fun m => deh_mem_fnField y 0 m

@[simp] theorem coe_dehK (y : Fin (D + 1) → Ω) (m : MvPolynomial (Fin (D + 1)) ℤ) :
    ((dehK y m : fnField y) : Ω) = deh y 0 m := rfl

def chartGen (y : Fin (D + 1) → Ω) (k : {k : Fin (D + 1) // k ≠ 0}) : fnField y :=
  ⟨y k / y 0, div_mem_fnField y k 0⟩

def chartRing (y : Fin (D + 1) → Ω) : Subalgebra ℤ (fnField y) :=
  Algebra.adjoin ℤ (Set.range (chartGen y))

theorem aeval_chartGen (y : Fin (D + 1) → Ω) (g : MvPolynomial {k : Fin (D + 1) // k ≠ 0} ℤ) :
    ((MvPolynomial.aeval (chartGen y) g : fnField y) : Ω) =
      deh y 0 (MvPolynomial.rename Subtype.val g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [deh_apply]
  | add p q hp hq => simp only [map_add, AddMemClass.coe_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.rename_X, MulMemClass.coe_mul, hp]
    congr 1
    simp [deh_apply, chartGen]

theorem chartGen_indep (y : Fin (D + 1) → Ω) (hfree : coordIdeal ℤ y = ⊥) :
    AlgebraicIndependent ℤ (chartGen y) := by
  classical
  rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
  intro g hg
  have hy0 := coord_ne_zero y hfree 0
  set G := MvPolynomial.rename Subtype.val g
  have h1 : deh y 0 G = 0 := by
    rw [← aeval_chartGen]
    change (((MvPolynomial.aeval (chartGen y) g : fnField y)) : Ω) = 0
    rw [hg]; rfl
  have hH := homog_isHomogeneous (0 : Fin (D + 1)) G le_rfl
  have h2 : MvPolynomial.aeval y (homog 0 G.totalDegree G) = 0 := by
    rw [MvPolynomial.aeval_def, algebraMap_int_eq, eval₂_homog y 0 hy0 G le_rfl, h1, mul_zero]
  have h3 := mem_coordIdeal_of_isHomogeneous ℤ y hH h2
  rw [hfree, Ideal.mem_bot] at h3
  apply MvPolynomial.funext
  intro u
  let v : Fin (D + 1) → ℚ := fun k => if h : k = 0 then 1 else (u ⟨k, h⟩ : ℚ)
  have h4 := eval₂_homog v 0 (by simp [v]) G le_rfl
  rw [h3, MvPolynomial.eval₂_zero] at h4
  have h5 : deh v 0 G = ((MvPolynomial.eval u g : ℤ) : ℚ) := by
    rw [deh_apply, MvPolynomial.eval₂_rename, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom,
      ← eq_intCast (Int.castRingHom ℚ), MvPolynomial.eval₂_comp_left]
    congr 1
    funext k
    simp [v, k.2]
  rw [h5] at h4
  have h6 : ((MvPolynomial.eval u g : ℤ) : ℚ) = 0 := by
    have := h4.symm
    rwa [mul_eq_zero, or_iff_right (pow_ne_zero _ (by simp [v]))] at this
  simpa using h6

theorem chartRing_closed (y : Fin (D + 1) → Ω) (hfree : coordIdeal ℤ y = ⊥) :
    IsIntegrallyClosed (chartRing y) := by
  have hind := chartGen_indep y hfree
  haveI : UniqueFactorizationMonoid (chartRing y) :=
    MulEquiv.uniqueFactorizationMonoid hind.aevalEquiv.toRingEquiv.toMulEquiv inferInstance
  haveI : IsDomain (chartRing y) := Subalgebra.isDomain _
  exact UniqueFactorizationMonoid.instIsIntegrallyClosed

theorem chartRing_frac (y : Fin (D + 1) → Ω) (hfree : coordIdeal ℤ y = ⊥) :
    IsFractionRing (chartRing y) (fnField y) := by
  have hl : y 0 ≠ 0 := coord_ne_zero y hfree 0
  refine IsFractionRing.of_field _ _ fun z => ?_
  have hinj : Function.Injective (algebraMap (chartRing y) Ω) := by
    intro a b hab
    exact Subtype.val_injective (Subtype.val_injective hab)
  let F : Subfield Ω := (IsFractionRing.lift (K := FractionRing (chartRing y)) hinj).fieldRange
  have hgen : ∀ i, y i / y 0 ∈ F := by
    intro i
    by_cases hi : i = 0
    · subst hi; rw [div_self hl]; exact F.one_mem
    · refine ⟨algebraMap (chartRing y) (FractionRing (chartRing y))
        ⟨chartGen y ⟨i, hi⟩, Algebra.subset_adjoin ⟨_, rfl⟩⟩, ?_⟩
      rw [IsFractionRing.lift_algebraMap hinj]
      rfl
  have hle : (fnField y).toSubfield ≤ F := by
    unfold fnField
    refine IntermediateField.adjoin_le_subfield ℚ _ ?_ ?_
    · rintro _ ⟨q, rfl⟩
      rw [eq_ratCast]
      exact SubfieldClass.ratCast_mem F q
    · rintro _ ⟨i, j, rfl⟩
      have : y i / y j = (y i / y 0) / (y j / y 0) := by
        rw [div_div_div_cancel_right₀ hl]
      change y i / y j ∈ F
      rw [this]
      exact F.div_mem (hgen i) (hgen j)
  obtain ⟨w, hw⟩ := hle z.2
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := chartRing y) w
  refine ⟨a, b, Subtype.val_injective ?_⟩
  rw [map_div₀, IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap] at hw
  rw [← hw]
  exact (map_div₀ (fnField y).val _ _).symm

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module IntermediateField

variable {Ω : Type*} [Field Ω] [CharZero Ω] {ι : Type} [Fintype ι] {D : ℕ}

theorem coord_div_isIntegral (x : ι → Ω) (e : Fin (D + 1) → ι) (h : IsProjFrame x e) (i : ι) :
    IsIntegral (chartRing (x ∘ e)) (x i / x (e 0)) := by
  set y := x ∘ e with hy
  change IsIntegral _ (x i / y 0)
  have hl : y 0 ≠ 0 := coord_ne_zero y h.free 0
  have hinj : Function.Injective (coneMap ℤ y) := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    have : f ∈ coordIdeal ℤ y := by rw [coordIdeal, RingHom.mem_ker]; exact hf
    rwa [h.free, Ideal.mem_bot] at this
  let eqv : MvPolynomial (Fin (D + 1)) ℤ ≃ₐ[ℤ] coneRing ℤ y := AlgEquiv.ofInjective (coneMap ℤ y) hinj
  let w : Fin (D + 1) → chartRing y := fun k =>
    if hk : k = 0 then 1 else ⟨chartGen y ⟨k, hk⟩, Algebra.subset_adjoin ⟨_, rfl⟩⟩
  have hw : ∀ k, algebraMap (chartRing y) Ω (w k) = y k * (y 0)⁻¹ := by
    intro k
    by_cases hk : k = 0
    · subst hk; simp [w, mul_inv_cancel₀ hl]
    · simp only [w, dif_neg hk]
      change y k / y 0 = _
      exact div_eq_mul_inv _ _
  let ψ : Polynomial Ω →+* Ω := Polynomial.evalRingHom (y 0)⁻¹
  have hev : ∀ f : MvPolynomial (Fin (D + 1)) ℤ,
      ψ (coneMap ℤ y f) = MvPolynomial.aeval (fun k => y k * (y 0)⁻¹) f := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [coneMap, ψ]
    | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
    | mul_X p k hp => rw [map_mul, map_mul, map_mul, hp]; simp [coneMap, ψ]
  let φ : coneRing ℤ y →+* chartRing y :=
    (MvPolynomial.aeval w).toRingHom.comp eqv.symm.toAlgHom.toRingHom
  have hrel : (algebraMap (chartRing y) Ω).comp φ = ψ.comp (algebraMap (coneRing ℤ y) _) := by
    ext r
    obtain ⟨f, rfl⟩ := eqv.surjective r
    have h1 : ((eqv f : coneRing ℤ y) : Polynomial Ω) = coneMap ℤ y f := rfl
    change algebraMap _ Ω (MvPolynomial.aeval w (eqv.symm (eqv f))) =
      ψ ((eqv f : coneRing ℤ y) : Polynomial Ω)
    rw [eqv.symm_apply_apply, h1, hev, ← MvPolynomial.aeval_algebraMap_apply,
      show (⇑(algebraMap (chartRing y) Ω) ∘ w) = fun k => y k * (y 0)⁻¹ from funext hw]
  have := IsIntegral.map_of_comp_eq φ ψ hrel (h.integral i)
  simpa [ψ, div_eq_mul_inv] using this

abbrev Lx (x : ι → Ω) (e : Fin (D + 1) → ι) : IntermediateField (fnField (x ∘ e)) Ω :=
  extendScalars (fnField_comp_le x e)

theorem Lx_eq (x : ι → Ω) (e : Fin (D + 1) → ι) (hx0 : x (e 0) ≠ 0) :
    Lx x e = adjoin (fnField (x ∘ e)) (Set.range fun i => x i / x (e 0)) := by
  apply le_antisymm
  · intro t ht
    have key : fnField x ≤
        (adjoin (fnField (x ∘ e)) (Set.range fun i => x i / x (e 0))).restrictScalars ℚ := by
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro s ⟨i, j, rfl⟩
      have hi : x i / x (e 0) ∈ adjoin (fnField (x ∘ e)) (Set.range fun i => x i / x (e 0)) :=
        subset_adjoin _ _ ⟨i, rfl⟩
      have hj : x j / x (e 0) ∈ adjoin (fnField (x ∘ e)) (Set.range fun i => x i / x (e 0)) :=
        subset_adjoin _ _ ⟨j, rfl⟩
      have hq := div_mem hi hj
      have e2 : x i / x (e 0) / (x j / x (e 0)) = x i / x j := by
        by_cases hj0 : x j = 0
        · simp [hj0]
        · field_simp
      rw [e2] at hq
      exact hq
    exact key ht
  · rw [IntermediateField.adjoin_le_iff]
    rintro t ⟨i, rfl⟩
    exact div_mem_fnField x i (e 0)

theorem Lx_finite (x : ι → Ω) (e : Fin (D + 1) → ι) (h : IsProjFrame x e) :
    FiniteDimensional (fnField (x ∘ e)) (Lx x e) := by
  have hx0 : x (e 0) ≠ 0 := coord_ne_zero (x ∘ e) h.free 0
  have hint : ∀ t ∈ Set.range (fun i => x i / x (e 0)), IsIntegral (fnField (x ∘ e)) t := by
    rintro t ⟨i, rfl⟩
    exact (coord_div_isIntegral x e h i).tower_top
  rw [Lx_eq x e hx0]
  exact IntermediateField.finiteDimensional_adjoin hint

def gL (x : ι → Ω) (e : Fin (D + 1) → ι) (i : ι) : Lx x e :=
  ⟨x i / x (e 0), div_mem_fnField x i (e 0)⟩

theorem adjoin_gL (x : ι → Ω) (e : Fin (D + 1) → ι) (hx0 : x (e 0) ≠ 0) :
    adjoin (fnField (x ∘ e)) (Set.range (gL x e)) = ⊤ := by
  apply IntermediateField.map_injective (Lx x e).val
  have htop : (⊤ : IntermediateField (fnField (x ∘ e)) (Lx x e)).map (Lx x e).val = Lx x e := by
    ext z
    rw [IntermediateField.mem_map]
    constructor
    · rintro ⟨w, -, rfl⟩
      exact w.2
    · intro hz
      exact ⟨⟨z, hz⟩, IntermediateField.mem_top, rfl⟩
  rw [IntermediateField.adjoin_map, ← Set.range_comp, htop]
  exact (Lx_eq x e hx0).symm

theorem exists_primitive (x : ι → Ω) (e : Fin (D + 1) → ι) (h : IsProjFrame x e) :
    ∃ c : ι → ℤ, (fnField (x ∘ e))⟮∑ i, (c i : Lx x e) * gL x e i⟯ = ⊤ := by
  have hx0 : x (e 0) ≠ 0 := coord_ne_zero (x ∘ e) h.free 0
  have := Lx_finite x e h
  exact exists_int_primitive (gL x e) (adjoin_gL x e hx0)

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
