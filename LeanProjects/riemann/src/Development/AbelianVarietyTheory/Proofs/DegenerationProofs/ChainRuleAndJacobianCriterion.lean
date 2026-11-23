import Mathlib

open KaehlerDifferential TensorProduct

namespace GlobalTheory.EtaleCoordJacobian

section tower
variable (R B : Type) [CommRing R] [CommRing B] (I : Type) [Algebra R B]
  [Algebra (MvPolynomial I R) B] [IsScalarTower R (MvPolynomial I R) B]

open KaehlerDifferential TensorProduct in
variable (R B : Type) [CommRing R] [CommRing B] (I : Type) [Algebra R B]
  [Algebra (MvPolynomial I R) B] [IsScalarTower R (MvPolynomial I R) B] in
theorem _root_.GlobalTheory.EtaleCoordJacobian.mapBaseChange_basis (i : I) :
    mapBaseChange R (MvPolynomial I R) B (((mvPolynomialBasis R I).baseChange B) i) =
      D R B (algebraMap (MvPolynomial I R) B (MvPolynomial.X i)) := by
  rw [Module.Basis.baseChange_apply, mvPolynomialBasis_apply, mapBaseChange_tmul, one_smul,
    map_D]

open KaehlerDifferential TensorProduct in
variable (R B : Type) [CommRing R] [CommRing B] (I : Type) [Algebra R B]
  [Algebra (MvPolynomial I R) B] [IsScalarTower R (MvPolynomial I R) B] in
theorem _root_.GlobalTheory.EtaleCoordJacobian.exists_basis_of_etale [Finite I] [Algebra.Etale (MvPolynomial I R) B] :
    (∃ b : Module.Basis I B Ω[B⁄R],
      ∀ i, b i = D R B (algebraMap (MvPolynomial I R) B (MvPolynomial.X i))) ∧
      Algebra.Smooth R B := by
  haveI : Algebra.Smooth R (MvPolynomial I R) := Algebra.Smooth.mk
  refine ⟨⟨((mvPolynomialBasis R I).baseChange B).map
    (tensorKaehlerEquivOfFormallyEtale R (MvPolynomial I R) B), fun i => ?_⟩,
    Algebra.Smooth.comp R (MvPolynomial I R) B⟩
  rw [Module.Basis.map_apply, ← _root_.GlobalTheory.EtaleCoordJacobian.mapBaseChange_basis]
  rfl

open KaehlerDifferential TensorProduct in
variable (R B : Type) [CommRing R] [CommRing B] (I : Type) [Algebra R B]
  [Algebra (MvPolynomial I R) B] [IsScalarTower R (MvPolynomial I R) B] in
theorem _root_.GlobalTheory.EtaleCoordJacobian.etale_of_basis [Finite I] [Algebra.Smooth R B]
    (b : Module.Basis I B Ω[B⁄R])
    (hb : ∀ i, b i = D R B (algebraMap (MvPolynomial I R) B (MvPolynomial.X i))) :
    Algebra.Etale (MvPolynomial I R) B := by
  set bc := (mvPolynomialBasis R I).baseChange B
  have hmap : mapBaseChange R (MvPolynomial I R) B = (bc.equiv b (Equiv.refl I)).toLinearMap :=
    bc.ext fun i => by
      rw [_root_.GlobalTheory.EtaleCoordJacobian.mapBaseChange_basis, LinearEquiv.coe_coe, Module.Basis.equiv_apply,
        Equiv.refl_apply, hb]
  have hinj : Function.Injective (mapBaseChange R (MvPolynomial I R) B) := by
    rw [hmap]; exact (bc.equiv b (Equiv.refl I)).injective
  have hsurj : Function.Surjective (mapBaseChange R (MvPolynomial I R) B) := by
    rw [hmap]; exact (bc.equiv b (Equiv.refl I)).surjective
  have hΩ : Subsingleton Ω[B⁄MvPolynomial I R] := by
    refine ⟨fun x y => ?_⟩
    have hx : ∀ z : Ω[B⁄MvPolynomial I R], z = 0 := fun z => by
      obtain ⟨w, rfl⟩ := map_surjective R (MvPolynomial I R) B z
      obtain ⟨v, rfl⟩ := hsurj w
      exact (exact_mapBaseChange_map R (MvPolynomial I R) B).apply_apply_eq_zero v
    rw [hx x, hx y]
  have hH : Subsingleton (Algebra.H1Cotangent (MvPolynomial I R) B) := by
    haveI : Subsingleton (Algebra.H1Cotangent R B) :=
      Algebra.FormallySmooth.subsingleton_h1Cotangent
    refine ⟨fun x y => ?_⟩
    have hx : ∀ z : Algebra.H1Cotangent (MvPolynomial I R) B, z = 0 := fun z => by
      have h1 : Algebra.H1Cotangent.δ R (MvPolynomial I R) B z = 0 :=
        hinj (((Algebra.H1Cotangent.exact_δ_mapBaseChange R _ B).apply_apply_eq_zero z).trans
          (map_zero _).symm)
      obtain ⟨w, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ R (MvPolynomial I R) B z).mp h1
      rw [Subsingleton.elim w 0, map_zero]
    rw [hx x, hx y]
  haveI : Algebra.FormallyEtale (MvPolynomial I R) B := Algebra.FormallyEtale.mk hΩ hH
  haveI : Algebra.FinitePresentation (MvPolynomial I R) B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R _ B
  exact Algebra.Etale.mk

end tower

open KaehlerDifferential TensorProduct in
private theorem exists_basis_D_and_smooth_of_etale_eval2Hom (R B I : Type) [CommRing R] [CommRing B]
    [Finite I] [Algebra R B] (t : I → B)
    (h : (MvPolynomial.eval₂Hom (algebraMap R B) t).Etale) :
    (∃ b : Module.Basis I B Ω[B⁄R], ∀ i, b i = D R B (t i)) ∧ Algebra.Smooth R B := by
  letI : Algebra (MvPolynomial I R) B := (MvPolynomial.eval₂Hom (algebraMap R B) t).toAlgebra
  haveI : IsScalarTower R (MvPolynomial I R) B := IsScalarTower.of_algebraMap_eq fun r => by
    simp [RingHom.algebraMap_toAlgebra, MvPolynomial.algebraMap_eq]
  haveI : Algebra.Etale (MvPolynomial I R) B := h
  obtain ⟨⟨b, hb⟩, hs⟩ := _root_.GlobalTheory.EtaleCoordJacobian.exists_basis_of_etale R B I
  exact ⟨⟨b, fun i => by rw [hb]; simp [RingHom.algebraMap_toAlgebra]⟩, hs⟩

open KaehlerDifferential TensorProduct in
private theorem det_derivation_eq_mul_det_repr {R B I : Type} [CommRing R] [CommRing B] [Fintype I]
    [DecidableEq I] [Algebra R B] (t t' : I → B) (b : Module.Basis I B Ω[B⁄R])
    (hb : ∀ i, b i = D R B (t i)) (C : Type) [CommRing C] (φ : B →+* C) (d : I → B →+ C)
    (hd : ∀ i x y, d i (x * y) = φ x * d i y + φ y * d i x)
    (hc : ∀ i r, d i (algebraMap R B r) = 0) :
    (Matrix.of fun i j => d i (t' j)).det =
      φ (Matrix.of fun k j => b.repr (D R B (t' j)) k).det *
        (Matrix.of fun i j => d i (t j)).det := by
  letI : Algebra B C := φ.toAlgebra
  letI : Algebra R C := (φ.comp (algebraMap R B)).toAlgebra
  haveI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have key : ∀ i j, d i (t' j) = ∑ k, d i (t k) * φ (b.repr (D R B (t' j)) k) := by
    intro i j
    let δ : Derivation R B C := Derivation.mk'
      { toFun := d i
        map_add' := map_add (d i)
        map_smul' := fun r x => by
          rw [RingHom.id_apply, Algebra.smul_def r (d i x), Algebra.smul_def, hd, hc, mul_zero,
            add_zero]
          rfl }
      (fun x y => by
        simp only [LinearMap.coe_mk, AddHom.coe_mk, Algebra.smul_def]
        exact hd i x y)
    have h1 : ∀ x, d i x = δ.liftKaehlerDifferential (D R B x) := fun x => by
      rw [Derivation.liftKaehlerDifferential_comp_D]; rfl
    rw [h1]
    conv_lhs => rw [← b.sum_repr (D R B (t' j))]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hb, ← h1, Algebra.smul_def, mul_comm]
    rfl
  have hmat : (Matrix.of fun i j => d i (t' j)) = (Matrix.of fun i j => d i (t j)) *
      (Matrix.of fun k j => b.repr (D R B (t' j)) k).map φ := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply, key]
  rw [hmat, Matrix.det_mul, mul_comm]
  congr 1
  exact (RingHom.map_det φ _).symm

open KaehlerDifferential TensorProduct in
private theorem exists_basis_D_of_isUnit_det_repr {R B I : Type} [CommRing R] [CommRing B]
    [Fintype I] [DecidableEq I] [Algebra R B] (t' : I → B) (b : Module.Basis I B Ω[B⁄R])
    (ha : IsUnit (Matrix.of fun k j => b.repr (D R B (t' j)) k).det) :
    ∃ b' : Module.Basis I B Ω[B⁄R], ∀ j, b' j = D R B (t' j) := by
  refine ⟨b.map (Matrix.toLinearEquiv b _ ha), fun j => ?_⟩
  rw [Module.Basis.map_apply, Matrix.toLinearEquiv_apply, Matrix.toLin_self]
  conv_rhs => rw [← b.sum_repr (D R B (t' j))]
  simp only [Matrix.of_apply]

open KaehlerDifferential TensorProduct in
private theorem etale_eval2Hom_of_basis_D (R B I : Type) [CommRing R] [CommRing B]
    [Finite I] [Algebra R B] [Algebra.Smooth R B] (t : I → B) (b : Module.Basis I B Ω[B⁄R])
    (hb : ∀ i, b i = D R B (t i)) : (MvPolynomial.eval₂Hom (algebraMap R B) t).Etale := by
  letI : Algebra (MvPolynomial I R) B := (MvPolynomial.eval₂Hom (algebraMap R B) t).toAlgebra
  haveI : IsScalarTower R (MvPolynomial I R) B := IsScalarTower.of_algebraMap_eq fun r => by
    simp [RingHom.algebraMap_toAlgebra, MvPolynomial.algebraMap_eq]
  exact _root_.GlobalTheory.EtaleCoordJacobian.etale_of_basis R B I b fun i => by
    rw [hb]; simp [RingHom.algebraMap_toAlgebra]

open KaehlerDifferential TensorProduct in

theorem _root_.GlobalTheory.EtaleCoordJacobian.chain_rule_and_jacobian_criterion : ∀ (R B : Type) [CommRing R] [CommRing B] (c : R →+* B) (I : Type) [Fintype I] [DecidableEq I] (t t' : I → B), (MvPolynomial.eval₂Hom c t).Etale → ∃ a : B, (∀ (C : Type) [CommRing C] (φ : B →+* C) (d : I → B →+ C), (∀ i x y, d i (x * y) = φ x * d i y + φ y * d i x) → (∀ i r, d i (c r) = 0) → (Matrix.of fun i j => d i (t' j)).det = φ a * (Matrix.of fun i j => d i (t j)).det) ∧ (IsUnit a → (MvPolynomial.eval₂Hom c t').Etale) := by
  intro R B _ _ c I _ _ t t' het
  letI : Algebra R B := c.toAlgebra
  obtain ⟨⟨b, hb⟩, hs⟩ := exists_basis_D_and_smooth_of_etale_eval2Hom R B I t het
  refine ⟨(Matrix.of fun k j => b.repr (D R B (t' j)) k).det,
    fun C _ φ d hd hc => det_derivation_eq_mul_det_repr t t' b hb C φ d hd hc, fun ha => ?_⟩
  obtain ⟨b', hb'⟩ := exists_basis_D_of_isUnit_det_repr t' b ha
  exact etale_eval2Hom_of_basis_D R B I t' b' hb'

end GlobalTheory.EtaleCoordJacobian
