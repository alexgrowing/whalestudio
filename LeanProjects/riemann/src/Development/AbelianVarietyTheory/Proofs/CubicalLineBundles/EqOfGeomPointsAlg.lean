import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

open TensorProduct in

theorem eq_of_geomPoints_alg (R K A : Type) [CommRing R] [IsDomain R] [Field K] [CharZero K]
    [Algebra R K] [IsFractionRing R K] [CommRing A] [Algebra R A] [Module.Flat R A]
    (het : (Algebra.TensorProduct.includeLeftRingHom : K →+* K ⊗[R] A).Etale) (a b : A)
    (h : ∀ (k' : Type) [Field k'] [IsAlgClosed k'] [CharZero k'] (ψ : A →+* k'), ψ a = ψ b) :
    a = b := by
  have het' : Algebra.Etale K (K ⊗[R] A) := by
    have : (algebraMap K (K ⊗[R] A)).Etale := het
    exact RingHom.etale_algebraMap.mp this
  have hred : _root_.IsReduced (K ⊗[R] A) :=
    Algebra.FormallyUnramified.isReduced_of_field K (K ⊗[R] A)
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A) :=
    Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective R K)
  apply hinj
  rw [← sub_eq_zero]
  apply IsNilpotent.eq_zero
  rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]
  intro p hp
  have hp' : p.IsPrime := hp
  let k' := AlgebraicClosure p.ResidueField
  let χ : (K ⊗[R] A) →+* k' :=
    (algebraMap p.ResidueField k').comp (algebraMap (K ⊗[R] A) p.ResidueField)
  have : CharZero k' := by
    let : Algebra K k' := (χ.comp (algebraMap K (K ⊗[R] A))).toAlgebra
    exact charZero_of_injective_algebraMap (algebraMap K k').injective
  have h1 := h k' (χ.comp (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A).toRingHom)
  rw [← Ideal.algebraMap_residueField_eq_zero]
  apply (algebraMap p.ResidueField k').injective
  rw [map_zero, map_sub, map_sub, sub_eq_zero]
  exact h1

theorem eq_of_geomPoints : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (T : Over (Sp R)), IsFinite T.hom → Flat T.hom → Etale (pullback.snd T.hom (spMap (algebraMap R K))) → ∀ a b : Γ(T.left, ⊤), (∀ (k' : Type) [Field k'] [IsAlgClosed k'] [CharZero k'] (β : R →+* k') (t : Over.mk (spMap β) ⟶ T), t.left.appTop.hom a = t.left.appTop.hom b) → a = b := by
  intro R K _ _ _ _ _ _ T hfin hflat het a b h
  have haff : IsAffine T.left := isAffine_of_isAffineHom T.hom
  let A : CommRingCat := Γ(T.left, ⊤)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (R := CommRingCat.of R) (S := A)
    (T.left.isoSpec.inv ≫ T.hom)
  let : Algebra R A := φ.hom.toAlgebra
  have hφ' : spMap (algebraMap R A) = T.left.isoSpec.inv ≫ T.hom := hφ
  have hfl : Module.Flat R A := by
    have : Flat (Spec.map φ) := by rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).mp this
  have het2 : (Algebra.TensorProduct.includeLeftRingHom : K →+* TensorProduct R K A).Etale := by
    have h1 : Etale (pullback.fst (spMap (algebraMap R K)) (spMap (algebraMap R A))) := by
      have e : pullback.fst (spMap (algebraMap R K)) (spMap (algebraMap R A)) =
          (pullbackSymmetry _ _).hom ≫
          pullback.map _ _ T.hom (spMap (algebraMap R K)) T.left.isoSpec.inv (𝟙 _) (𝟙 _)
            (by simp [hφ']) (by simp) ≫ pullback.snd T.hom (spMap (algebraMap R K)) := by
        rw [pullback.map, pullback.lift_snd, Category.comp_id, pullbackSymmetry_hom_comp_snd]
      rw [e]
      infer_instance
    have h2 : Etale (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : K →+* TensorProduct R K A))) := by
      rw [← pullbackSpecIso_inv_fst]
      infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp h2
  refine eq_of_geomPoints_alg R K A het2 a b ?_
  intro k' _ _ _ ψ
  let t : Over.mk (spMap (ψ.comp (algebraMap R A))) ⟶ T :=
    Over.homMk (spMap ψ ≫ T.left.isoSpec.inv) (by
      simp only [Over.mk_hom, Category.assoc]
      erw [← hφ', ← Spec.map_comp]
      rfl)
  have h3 := h k' _ t
  have key : ∀ x : Γ(T.left, ⊤), t.left.appTop.hom x =
      (Scheme.ΓSpecIso (CommRingCat.of k')).inv.hom (ψ x) := by
    intro x
    have e : (spMap ψ ≫ T.left.isoSpec.inv).appTop =
        CommRingCat.ofHom ψ ≫ (Scheme.ΓSpecIso (CommRingCat.of k')).inv := by
      rw [Scheme.Hom.comp_appTop, Scheme.ΓSpecIso_inv_naturality]
      congr 1
      have e2 : T.left.isoSpec.inv.appTop ≫ T.left.isoSpec.hom.appTop = 𝟙 _ := by
        rw [← Scheme.Hom.comp_appTop]; simp
      have e3 : T.left.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(T.left, ⊤)).hom :=
        Scheme.toSpecΓ_appTop _
      rw [e3] at e2
      exact (Iso.comp_hom_eq_id _).mp e2
    exact congrArg (fun f => f.hom x) e
  rw [key, key] at h3
  exact (Scheme.ΓSpecIso (CommRingCat.of k')).symm.commRingCatIsoToRingEquiv.injective h3

end GlobalTheory.LamF
