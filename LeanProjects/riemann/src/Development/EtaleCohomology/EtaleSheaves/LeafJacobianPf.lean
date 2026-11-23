import Development.EtaleCohomology.EtaleSheaves.LeafChartRingPf

noncomputable section
open MvPolynomial TensorProduct
namespace LateralTheory.E.LeafJacobianPf

theorem mapBaseChange_bij (A ι S : Type) [CommRing A] [CommRing S] [Algebra A S]
    [Algebra (MvPolynomial ι A) S] [IsScalarTower A (MvPolynomial ι A) S]
    (hli : LinearIndependent S fun i => KaehlerDifferential.D A S (algebraMap (MvPolynomial ι A) S (X i)))
    (hsp : Submodule.span S (Set.range fun i => KaehlerDifferential.D A S (algebraMap (MvPolynomial ι A) S (X i))) = ⊤) :
    Function.Bijective (KaehlerDifferential.mapBaseChange A (MvPolynomial ι A) S) := by
  let bT := Algebra.TensorProduct.basis S (KaehlerDifferential.mvPolynomialBasis A ι)
  let bS := Module.Basis.mk hli hsp.ge
  have h : KaehlerDifferential.mapBaseChange A (MvPolynomial ι A) S = (bT.equiv bS (Equiv.refl ι)).toLinearMap := by
    refine bT.ext fun i => ?_
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply, Module.Basis.mk_apply]
    simp [bT, Algebra.TensorProduct.basis_apply, KaehlerDifferential.mvPolynomialBasis_apply,
      KaehlerDifferential.mapBaseChange_tmul]
  rw [h]
  exact (bT.equiv bS (Equiv.refl ι)).bijective

theorem formallyEtale_of_bij (A R S : Type) [CommRing A] [CommRing R] [CommRing S] [Algebra A R] [Algebra A S]
    [Algebra R S] [IsScalarTower A R S] [Algebra.FormallySmooth A S]
    (h : Function.Bijective (KaehlerDifferential.mapBaseChange A R S)) : Algebra.FormallyEtale R S := by
  have hD : ∀ s : S, KaehlerDifferential.D R S s = 0 := by
    intro s
    obtain ⟨y, hy⟩ := h.2 (KaehlerDifferential.D A S s)
    have h2 := (KaehlerDifferential.exact_mapBaseChange_map A R S).apply_apply_eq_zero y
    rw [hy, KaehlerDifferential.map_D] at h2
    simpa using h2
  have hK : Subsingleton (KaehlerDifferential R S) := by
    refine ⟨fun a b => ?_⟩
    have key : ∀ x : KaehlerDifferential R S, x = 0 := by
      intro x
      have hx : x ∈ Submodule.span S (Set.range (KaehlerDifferential.D R S)) := by
        rw [KaehlerDifferential.span_range_derivation]; exact Submodule.mem_top
      induction hx using Submodule.span_induction with
      | mem y hy => obtain ⟨s, rfl⟩ := hy; exact hD s
      | zero => rfl
      | add a b _ _ ha hb => rw [ha, hb, add_zero]
      | smul c a _ ha => rw [ha, smul_zero]
    rw [key a, key b]
  have hH : Subsingleton (Algebra.H1Cotangent R S) := by
    refine ⟨fun a b => ?_⟩
    have key : ∀ z : Algebra.H1Cotangent R S, z = 0 := by
      intro z
      have hz : Algebra.H1Cotangent.δ A R S z = 0 := by
        apply h.1
        rw [(Algebra.H1Cotangent.exact_δ_mapBaseChange A R S).apply_apply_eq_zero z, map_zero]
      obtain ⟨w, hw⟩ := (Algebra.H1Cotangent.exact_map_δ A R S z).mp hz
      rw [← hw, Subsingleton.elim w 0, map_zero]
    rw [key a, key b]
  exact ⟨hK, hH⟩

theorem LeafJacobian_of : LateralTheory.E.LeafChartRingPf.LeafJacobian := by
  intro d e A B _ _ _ n hB g t y hli hsp
  let ψ := (sumAlgEquiv A (Fin d) (Fin e)).toRingEquiv
  let φ : MvPolynomial (Fin d ⊕ Fin e) A →+* Localization.Away g :=
    (LateralTheory.E.LeafChartRingPf.coordMap (A := A) g y t).comp ψ.toRingHom
  have hφX : ∀ i, φ (X i) = Sum.elim (fun j => algebraMap B (Localization.Away g) (t j))
      (fun k => algebraMap B (Localization.Away g) (y k)) i := by
    intro i; cases i <;> simp [φ, ψ, LateralTheory.E.LeafChartRingPf.coordMap]
  have hφ : φ.Etale := by
    letI : Algebra (MvPolynomial (Fin d ⊕ Fin e) A) (Localization.Away g) := φ.toAlgebra
    haveI : IsScalarTower A (MvPolynomial (Fin d ⊕ Fin e) A) (Localization.Away g) :=
      IsScalarTower.of_algebraMap_eq fun a => by
        simp [RingHom.algebraMap_toAlgebra, φ, ψ, LateralTheory.E.LeafChartRingPf.coordMap,
          MvPolynomial.algebraMap_eq]
    haveI := hB.isStandardSmooth
    haveI : Algebra.FormallySmooth A B := inferInstance
    haveI : Algebra.FormallySmooth B (Localization.Away g) :=
      Algebra.FormallySmooth.of_isLocalization (Submonoid.powers g)
    haveI : Algebra.FormallySmooth A (Localization.Away g) := Algebra.FormallySmooth.comp A B _
    have hfam : (fun i => KaehlerDifferential.D A (Localization.Away g)
        (algebraMap (MvPolynomial (Fin d ⊕ Fin e) A) (Localization.Away g) (X i))) =
        (Sum.elim
          (fun k => KaehlerDifferential.D A (Localization.Away g) (algebraMap B _ (y k)))
          (fun j => KaehlerDifferential.D A (Localization.Away g) (algebraMap B _ (t j)))) ∘
          Equiv.sumComm (Fin d) (Fin e) := by
      funext i
      rw [RingHom.algebraMap_toAlgebra, hφX]
      cases i <;> rfl
    have hbij := mapBaseChange_bij A (Fin d ⊕ Fin e) (Localization.Away g)
      (by rw [hfam]; exact hli.comp _ (Equiv.injective _))
      (by rw [hfam, (Equiv.surjective _).range_comp]; exact hsp)
    haveI := formallyEtale_of_bij A (MvPolynomial (Fin d ⊕ Fin e) A) (Localization.Away g) hbij
    haveI : Algebra.FinitePresentation B (Localization.Away g) := IsLocalization.Away.finitePresentation g
    haveI : Algebra.FinitePresentation A (Localization.Away g) := Algebra.FinitePresentation.trans A B _
    haveI : Algebra.FinitePresentation (MvPolynomial (Fin d ⊕ Fin e) A) (Localization.Away g) :=
      Algebra.FinitePresentation.of_restrict_scalars_finitePresentation A _ _
    exact RingHom.etale_algebraMap.mpr ⟨inferInstance, inferInstance⟩
  have hc : LateralTheory.E.LeafChartRingPf.coordMap (A := A) g y t = φ.comp ψ.symm.toRingHom := by
    refine RingHom.ext fun x => ?_
    simp only [φ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  rw [hc]
  exact RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective ψ.symm.bijective) hφ

end LateralTheory.E.LeafJacobianPf
