import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsFirstOrderDeformationOfRZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PtCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoRes
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

private theorem hx_finite {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O]
    {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B]
    [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B]
    (x : R →ₐ[O] B) : Module.Finite O x.range := by
  haveI : IsArtinianRing B := IsArtinianRing.of_finite ℚ_[l] B
  haveI : IsNoetherianRing x.range := isNoetherianRing_of_surjective R _ x.rangeRestrict.toRingHom
    x.rangeRestrict_surjective
  have hfin : ∀ m : MaximalSpectrum B, Module.Finite ℤ_[l] (integralClosure ℤ_[l] (B ⧸ m.asIdeal)) := fun m => by
    haveI := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    exact IsIntegralClosure.finite ℤ_[l] ℚ_[l] (B ⧸ m.asIdeal) _
  let v : x.range →ₐ[ℤ_[l]] B := x.range.val.restrictScalars ℤ_[l]
  have hint : ∀ (m : MaximalSpectrum B) (z : x.range),
      ((Ideal.Quotient.mkₐ ℤ_[l] m.asIdeal).comp v) z ∈ integralClosure ℤ_[l] (B ⧸ m.asIdeal) := by
    rintro m ⟨_, a, rfl⟩
    haveI := m.isMaximal
    exact ((ptCont (l := l) R (B ⧸ m.asIdeal) ((Ideal.Quotient.mkₐ O m.asIdeal).comp x)).2
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 m.isMaximal)).1 a
  let g : x.range →ₐ[ℤ_[l]] ∀ m : MaximalSpectrum B, integralClosure ℤ_[l] (B ⧸ m.asIdeal) :=
    Pi.algHom _ _ fun m => AlgHom.codRestrict _ _ (hint m)
  haveI : Module.Finite ℤ_[l] g.range :=
    Module.Finite.of_injective g.range.val.toLinearMap Subtype.val_injective
  haveI : Module.Finite ℤ_[l] x.range := by
    refine Module.finite_of_surjective_of_ker_le_nilradical g.rangeRestrict g.rangeRestrict_surjective ?_
      (IsNoetherian.noetherian _)
    intro z hz
    have hz' : g z = 0 := congrArg Subtype.val hz
    have hj : (z : B) ∈ Ideal.jacobson (⊥ : Ideal B) := by
      rw [Ideal.jacobson, Ideal.mem_sInf]
      rintro I ⟨-, hI⟩
      have := congrArg Subtype.val (congrFun hz' ⟨I, hI⟩)
      exact Ideal.Quotient.eq_zero_iff_mem.1 this
    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := B)
    refine ⟨n, Subtype.ext ?_⟩
    have := Ideal.pow_mem_pow hj n
    rw [hn] at this
    simpa using this
  exact Module.Finite.of_restrictScalars_finite ℤ_[l] O x.range

private theorem hx_pow {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    {A : Type} [CommRing A] [Algebra O A] [Module.Finite O A] (y : R →ₐ[O] A) :
    ∃ N : ℕ, ∀ a ∈ maximalIdeal R ^ N, y a ∈ (maximalIdeal O).map (algebraMap O A) := by
  have h1 : (maximalIdeal R).map y ≤ ((maximalIdeal O).map (algebraMap O A)).radical := by
    rw [Ideal.radical_eq_sInf, le_sInf_iff]
    rintro P ⟨hP, hPp⟩
    have hc : (P.comap (algebraMap O A)).IsMaximal := by
      rw [← (maximalIdeal.isMaximal _).eq_of_le (Ideal.IsPrime.ne_top inferInstance)
        (Ideal.map_le_iff_le_comap.1 hP)]
      infer_instance
    haveI : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P hc
    have hi : (y : R →+* A).IsIntegral := by
      refine RingHom.IsIntegral.tower_top (algebraMap O R) _ ?_
      rw [AlgHom.comp_algebraMap]
      exact fun a => Algebra.IsIntegral.isIntegral (R := O) a
    have := eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' (y : R →+* A) hi P)
    rw [Ideal.map_le_iff_le_comap, ← this]
    exact le_rfl
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg h1 (Ideal.FG.map (IsNoetherian.noetherian _) _)
  refine ⟨N, fun a ha => hN ?_⟩
  rw [← Ideal.map_pow]
  exact Ideal.mem_map_of_mem y ha

theorem UpperTheory.V.Loc.homExt :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] {Γ ι : Type} [Group Γ] [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField O)) (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ρ : Lift O rbar R), ρ.Generates → ∀ (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (f f' : R →ₐ[O] B), (∀ g a b, f (ρ.hom g a b) = f' (ρ.hom g a b)) → f = f' := by
  intro l _ O _ _ _ _ _ _ _ Γ ι _ _ _ _ rbar R _ _ _ ρ hρ B _ _ _ _ _ _ _ f f' h
  choose c hc using IsCO.res_surj (O := O) (R := R)
  let S : Set R := Set.range fun s : Γ × ι × ι => ρ.hom s.1 s.2.1 s.2.2 - algebraMap O R (c (ρ.hom s.1 s.2.1 s.2.2))
  have hS : S ⊆ maximalIdeal R := by
    rintro _ ⟨s, rfl⟩
    exact hc _
  have hspan := co_span O R O (Algebra.ofId O R) S hS fun u u' _ hu => by
    haveI := (co_res O).2
    refine hρ _ u u' (Lift.ext (MonoidHom.ext fun g => Matrix.ext fun a b => ?_))
    have := hu _ ⟨(g, a, b), rfl⟩
    simp only [map_sub, AlgHom.commutes, sub_left_inj] at this
    exact this
  haveI := hx_finite (l := l) f
  haveI := hx_finite (l := l) f'
  let A : Subalgebra O B := f.range ⊔ f'.range
  haveI : Module.Finite O A := Subalgebra.finite_sup _ _
  let u : R →ₐ[O] A := f.codRestrict A fun a => (le_sup_left : f.range ≤ A) ⟨a, rfl⟩
  let u' : R →ₐ[O] A := f'.codRestrict A fun a => (le_sup_right : f'.range ≤ A) ⟨a, rfl⟩
  haveI : IsHausdorff (maximalIdeal O) A := inferInstance
  haveI : IsHausdorff ((maximalIdeal O).map (algebraMap O A)) A := IsHausdorff.map_algebraMap_iff.2 this
  obtain ⟨N, hN⟩ := hx_pow u
  obtain ⟨N', hN'⟩ := hx_pow u'
  have key : u = u' := by
    refine co_ext O R O A ((maximalIdeal O).map (algebraMap O A)) (Algebra.ofId O R) S hS hspan u u'
      ⟨N + N', fun x hx => ⟨hN x (Ideal.pow_le_pow_right (Nat.le_add_right _ _) hx),
        hN' x (Ideal.pow_le_pow_right (Nat.le_add_left _ _) hx)⟩⟩ (Subsingleton.elim _ _) ?_
    rintro _ ⟨s, rfl⟩
    rw [map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, sub_left_inj]
    exact Subtype.ext (h _ _ _)
  ext a
  exact congrArg Subtype.val (DFunLike.congr_fun key a)
