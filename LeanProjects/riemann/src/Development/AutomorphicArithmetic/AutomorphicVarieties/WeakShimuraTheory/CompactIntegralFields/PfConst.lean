import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.CharpolyPowInt

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

section Abstract

variable {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R] [IsCO O R]

private theorem pf_const [IsDomain R] (h0 : ∀ a ∈ maximalIdeal O, algebraMap O R a = 0) {y : R} (hy : IsIntegral O y) :
    ∃ a, y = algebraMap O R a := by
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) y
  refine ⟨a, ?_⟩
  by_contra hne
  letI : Algebra (ResidueField O) R := (Ideal.Quotient.lift (maximalIdeal O) (algebraMap O R) h0).toAlgebra
  haveI : IsScalarTower O (ResidueField O) R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h1 : IsIntegral (ResidueField O) (y - algebraMap O R a) := (hy.sub isIntegral_algebraMap).tower_top
  exact ha (h1.isUnit (sub_ne_zero.2 hne))

private theorem pf_sect (h0 : ∀ a ∈ maximalIdeal O, algebraMap O R a = 0) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] :
    ∃ s : B →ₐ[O] R, (∀ b ∈ maximalIdeal B, s b = 0) ∧ ∀ (f : B →ₐ[O] R) (b : B), (∃ a, f b = algebraMap O R a) → f b = s b := by
  let j : ResidueField O →ₐ[O] R := Ideal.Quotient.liftₐ (maximalIdeal O) (Algebra.ofId O R) h0
  refine ⟨j.comp (res O B), fun b hb => ?_, ?_⟩
  · rw [AlgHom.comp_apply, (res_eq_zero_iff O B b).2 hb, map_zero]
  · rintro f b ⟨a, ha⟩
    rw [AlgHom.comp_apply, ← res_map f, ha, AlgHom.commutes, AlgHom.commutes]

private theorem pf_cont {Γ B : Type} [TopologicalSpace Γ] [CommRing B] [Algebra O B] [IsCO O B] (f : B →ₐ[O] R) {u : Γ → B}
    (hu : AdicCont (maximalIdeal B) u) : AdicCont (maximalIdeal R) fun g => f (u g) := fun N => by
  have hle : maximalIdeal B ^ N ≤ (maximalIdeal R ^ N).comap (f : B →+* R) := by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    show f y ∈ maximalIdeal R
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hy
  exact (hu N).comp (Ideal.quotientMap _ (f : B →+* R) hle)

private theorem pf_lam {l : ℕ} [Fact l.Prime] {F : W.GFrame l} [Algebra ℤ_[l] O] {n : ℕ} {r : W.Resid F O n} (Λ : W.LamObj r)
    (h0 : ∀ a ∈ maximalIdeal O, algebraMap O R a = 0) (f : Λ.Λ →ₐ[O] R)
    (hf : ∀ v i g, ∃ a, f (Λ.κ v i g) = algebraMap O R a) (x : Λ.Λ) : ∃ a, f x = algebraMap O R a := by
  obtain ⟨s, hs, hsf⟩ := pf_sect h0 Λ.Λ
  have hi : W.IsInert r fun v i => W.pushCh (f : Λ.Λ →+* R) (Λ.κ v i) := fun v i => by
    obtain ⟨ψ, hψ, he⟩ := Λ.inert v i
    refine ⟨W.pushCh (f : Λ.Λ →+* R) ψ, ⟨pf_cont f hψ.cont, fun g => (res_map f _).trans (hψ.red g), fun g => ?_⟩, ?_⟩
    · show f (ψ g) = _
      rw [hψ.mu g, f.commutes]
    · exact congrArg (W.pushCh (f : Λ.Λ →+* R)) he
  have he : f = s := (Λ.univ R _ hi).unique (fun _ _ => rfl) fun v i =>
    MonoidHom.ext fun g => Units.ext (hsf f _ (hf v i g)).symm
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
  have h1 := hs _ ha
  rw [map_sub, AlgHom.commutes, sub_eq_zero] at h1
  exact ⟨a, he ▸ h1⟩

private theorem pf_int {Λ B : Type} [CommRing Λ] [CommRing B] [Algebra O Λ] [Algebra O B] (t : Λ →ₐ[O] B) (J : Ideal B)
    (hfin : ((Ideal.Quotient.mk J).comp (t : Λ →+* B)).Finite) (f : B →ₐ[O] R) (hJ : ∀ b ∈ J, f b = 0)
    (hc : ∀ x, ∃ a, f (t x) = algebraMap O R a) (b : B) : IsIntegral O (f b) := by
  obtain ⟨p, hp, hb⟩ := hfin.to_isIntegral (Ideal.Quotient.mk J b)
  have h1 := congrArg (Ideal.Quotient.lift J (f : B →+* R) hJ) hb
  rw [hom_eval₂, map_zero] at h1
  have hl : p.map ((f.comp t : Λ →ₐ[O] R) : Λ →+* R) ∈ lifts (algebraMap O R) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    obtain ⟨a, ha⟩ := hc (p.coeff n)
    exact ⟨a, by rw [coeff_map]; exact ha.symm⟩
  obtain ⟨q, hq, -, hm⟩ := lifts_and_natDegree_eq_and_monic hl (hp.map _)
  refine ⟨q, hm, ?_⟩
  rw [← eval_map, hq, eval_map]
  exact h1

variable {O₀ Γ : Type} [CommRing O₀] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O₀ Γ} {a : O₀ →+* O} (X : Space Φ a)

private theorem pf_sq (f : X.B →ₐ[O] R) (g : Γ) (hg : ∀ n, IsIntegral O (f ((X.cp (g ^ 2)).coeff n))) (n : ℕ) :
    IsIntegral O (f ((X.cp g).coeff n)) := by
  let S₀ : Subring X.B := (integralClosure O R).toSubring.comap (f : X.B →+* R)
  let S : Subring X.A := S₀.map (algebraMap X.B X.A)
  have h1 := AlgebraTools.charpolyPowInt X.A (Fin 4) S (X.P.r g) 2 two_pos (fun i => by
    rw [← map_pow, ← X.cp_map, coeff_map]
    exact ⟨_, hg i, rfl⟩) n
  rw [← X.cp_map, coeff_map] at h1
  obtain ⟨p, hp, hb⟩ := h1
  have hl : p.map S.subtype ∈ lifts ((algebraMap X.B X.A).comp S₀.subtype) := by
    rw [lifts_iff_coeff_lifts]
    intro m
    obtain ⟨y, hy, he⟩ := (p.coeff m).2
    exact ⟨⟨y, hy⟩, by rw [coeff_map]; exact he⟩
  obtain ⟨q, hq, -, hm⟩ := lifts_and_natDegree_eq_and_monic hl (hp.map _)
  have h2 : q.eval₂ S₀.subtype ((X.cp g).coeff n) = 0 := by
    apply X.inj
    rw [hom_eval₂, map_zero, ← eval_map, hq, eval_map]
    exact hb
  let j : S₀ →+* integralClosure O R := ((f : X.B →+* R).comp S₀.subtype).codRestrict _ fun y => y.2
  have h3 : IsIntegral (integralClosure O R) (f ((X.cp g).coeff n)) := by
    refine ⟨q.map j, hm.map j, ?_⟩
    have h4 := congrArg (f : X.B →+* R) h2
    rw [hom_eval₂, map_zero] at h4
    rw [eval₂_map]
    exact h4
  exact isIntegral_trans _ h3

private theorem pf_gen [IsDomain R] (h0 : ∀ a ∈ maximalIdeal O, algebraMap O R a = 0) (f : X.B →ₐ[O] R)
    (h1 : ∀ g n, IsIntegral O (f ((X.cp g).coeff n))) (h2 : ∀ v i, ∀ s ∈ Φ.Gv v, IsIntegral O (f (X.ψ v i s))) :
    ∀ b ∈ maximalIdeal X.B, f b = 0 := by
  obtain ⟨s, hs, hsf⟩ := pf_sect h0 X.B
  rw [X.genB R f s (fun g n => hsf f _ (pf_const h0 (h1 g n))) fun v i g hg => hsf f _ (pf_const h0 (h2 v i g hg))]
  exact hs

private theorem pf_unit {u : Oˣ} {y : R} (h : IsIntegral O (algebraMap O R u * y)) : IsIntegral O y := by
  have h1 := (isIntegral_algebraMap (R := O) (A := R) (x := (u⁻¹ : Oˣ))).mul h
  rwa [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul] at h1

end Abstract

section Galois

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} (T : Tower D)

private theorem pf_lift {g : G T.F Ω} (hg : resQ T.F g ∈ T.K.fixingSubgroup) : ∃ g' : G T.L Ω, resLe T.F_le g' = g := by
  have h1 : resQ T.F g ∈ T.F.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    exact fun x hx => g.commutes ⟨x, hx⟩
  have h2 : resQ T.F g ∈ T.L.fixingSubgroup := by
    rw [T.hL, IntermediateField.fixingSubgroup_sup]
    exact ⟨h1, hg⟩
  rw [IntermediateField.mem_fixingSubgroup_iff] at h2
  exact ⟨{ g.toRingEquiv with commutes' := fun x => h2 x.1 x.2 }, AlgEquiv.ext fun _ => rfl⟩

private theorem pf_sqK (g : G ℚ Ω) : g ^ 2 ∈ T.K.fixingSubgroup := by
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : IsGalois ℚ Ω := inferInstance
  have hi : T.K.fixingSubgroup.index = 2 := by
    rw [← T.degK]
    exact (IntermediateField.finrank_eq_fixingSubgroup_index Ω T.K).symm
  exact Subgroup.sq_mem_of_index_two hi g

end Galois
