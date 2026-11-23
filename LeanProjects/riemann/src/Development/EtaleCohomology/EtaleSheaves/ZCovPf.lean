import Development.EtaleCohomology.EtaleSheaves.LineHighPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.LineHighPf

namespace LateralTheory.E.ZCovPf
set_option linter.style.haveILetI false

theorem aic_of_equiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) (h : AIC R) : AIC S := by
  intro p hp hd
  obtain ⟨a, ha⟩ := h (p.map e.symm.toRingHom) (hp.map _)
    (by rwa [Polynomial.natDegree_map_eq_of_injective e.symm.injective])
  refine ⟨e a, ?_⟩
  have hc : (e : R →+* S).comp e.symm.toRingHom = RingHom.id S := by ext x; simp
  have hq : p = (p.map e.symm.toRingHom).map (e : R →+* S) := by
    rw [Polynomial.map_map, hc, Polynomial.map_id]
  rw [hq, show e a = (e : R →+* S) a from rfl, Polynomial.eval_map_apply, ha, map_zero]

theorem good_of_affine {A : Type} [CommRing A] {Z W : Scheme.{0}} (hZ : AICSch Z) (j : W ⟶ Z) [IsOpenImmersion j]
    [IsAffine W] (p : Z ⟶ Spec (CommRingCat.of A)) : Good (j ≫ p) := by
  by_cases hW : IsEmpty W
  · exact Or.inl hW
  right
  obtain ⟨x⟩ : Nonempty W := not_isEmpty_iff.mp hW
  have hO : IsAffineOpen (j ''ᵁ ⊤) := (isAffineOpen_top W).image_of_isOpenImmersion j
  have hne : ((j ''ᵁ ⊤ : Z.Opens) : Set Z).Nonempty := ⟨j x, x, trivial, rfl⟩
  have hA : AIC Γ(W, ⊤) := aic_of_equiv (j.appIso ⊤).commRingCatIsoToRingEquiv (hZ.2 _ hO hne)
  haveI : IsIntegral Z := hZ.1
  haveI : Nonempty W := ⟨x⟩
  haveI : IsIntegral W := isIntegral_of_isOpenImmersion j
  haveI : Nonempty (⊤ : W.Opens) := ⟨⟨x, trivial⟩⟩
  let φ : A →+* Γ(W, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (j ≫ p).appTop).hom
  letI : Algebra A Γ(W, ⊤) := φ.toAlgebra
  refine ⟨Γ(W, ⊤), inferInstance, inferInstance, inferInstance, hA, W.isoSpec, ?_⟩
  have hφ : CommRingCat.ofHom (algebraMap A Γ(W, ⊤)) = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (j ≫ p).appTop := rfl
  rw [hφ, Spec.map_comp, Scheme.isoSpec_hom, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]

attribute [local instance] MvPolynomial.gradedAlgebra

def D (i : Fin 2) : P1.Opens := Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) (MvPolynomial.X i)

theorem D_affine (i : Fin 2) : IsAffineOpen (D i) :=
  Proj.isAffineOpen_basicOpen _ _ (f_deg := (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
    (MvPolynomial.isHomogeneous_X ℤ i)) (hm := Nat.one_pos)

theorem D_inf : IsAffineOpen (D 0 ⊓ D 1) := by
  have h := Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
    (MvPolynomial.X 0 * MvPolynomial.X 1) (f_deg := (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
    ((MvPolynomial.isHomogeneous_X ℤ 0).mul (MvPolynomial.isHomogeneous_X ℤ 1))) (hm := Nat.two_pos)
  rw [Proj.basicOpen_mul] at h
  exact h

theorem D_cover : D 0 ⊔ D 1 = ⊤ := by
  have h := Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
    (fun i : Fin 2 => (MvPolynomial.X i : MvPolynomial (Fin 2) ℤ)) ?_
  · refine eq_top_iff.mpr (le_trans (le_of_eq h.symm) (iSup_le fun i => ?_))
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  · intro x hx
    have h0 := (HomogeneousIdeal.mem_irrelevant_iff _ _).mp hx
    have hc : MvPolynomial.coeff 0 x = 0 := by
      rw [GradedRing.proj_apply] at h0
      have e : ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) x) 0 : MvPolynomial (Fin 2) ℤ) =
          MvPolynomial.homogeneousComponent 0 x := MvPolynomial.decomposition.decompose'_apply x 0
      rw [e] at h0
      have := congrArg (MvPolynomial.coeff 0) h0
      rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_zero] at this
      simpa using this
    rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra hne
    push Not at hne
    have hm0 : m = 0 := Finsupp.ext fun i => hne i trivial
    subst hm0
    exact (MvPolynomial.mem_support_iff.mp hm) hc

theorem projectiveLine_integers_affine_cover_absolutely_integrally_closed : ZCov := by
  intro A _ Z p hp hZ
  obtain ⟨L, u, l, hu, ⟨-, f0, hpb⟩, rfl⟩ := hp
  have hf0 : IsAffineHom f0 :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom) hpb.flip inferInstance
  let φ : Z ⟶ P1 := u ≫ f0
  let U : Z.Opens := φ ⁻¹ᵁ D 0
  let V : Z.Opens := φ ⁻¹ᵁ D 1
  have hU : IsAffineOpen U := (D_affine 0).preimage φ
  have hV : IsAffineOpen V := (D_affine 1).preimage φ
  have hUV : IsAffineOpen (U ⊓ V) := D_inf.preimage φ
  haveI : IsAffine U := hU
  haveI : IsAffine V := hV
  haveI : IsAffine (U ⊓ V : Z.Opens) := hUV
  haveI : IsAffine (pullback U.ι V.ι) := IsAffine.of_isIso (isPullback_opens_inf U V).isoPullback.inv
  refine ⟨U, V, U.ι, V.ι, inferInstance, inferInstance, ?_, good_of_affine hZ U.ι _, good_of_affine hZ V.ι _, ?_⟩
  · rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    have h := congrArg (fun O : P1.Opens => ((φ ⁻¹ᵁ O : Z.Opens) : Set Z)) D_cover
    simpa [U, V] using h
  · rw [← Category.assoc]
    exact good_of_affine hZ (pullback.fst U.ι V.ι ≫ U.ι) _

end LateralTheory.E.ZCovPf
