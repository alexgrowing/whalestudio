import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerFibreEquivPushoutFormallyEtale
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

open KaehlerDifferential TensorProduct in

theorem mapBaseChange_residueField_bijective_of_etale_fibre :
    ∀ (A C B Ω : Type) [CommRing A] [CommRing C] [CommRing B] [Algebra A C] [Algebra A B] [Algebra C B] [IsScalarTower A C B] [Field Ω] [Algebra A Ω] (Q : Ideal B) [Q.IsPrime] (Q' : Ideal (TensorProduct A Ω B)) [Q'.IsPrime] (f : TensorProduct A Ω B), Q'.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] TensorProduct A Ω B) = Q → f ∉ Q' → ((algebraMap (TensorProduct A Ω B) (Localization.Away f)).comp (Algebra.TensorProduct.map (AlgHom.id A Ω) (IsScalarTower.toAlgHom A C B)).toRingHom).Etale → Function.Bijective ((KaehlerDifferential.mapBaseChange A C B).lTensor Q.ResidueField) := by
  intro A C B Ω _ _ _ _ _ _ _ _ _ Q _ Q' _ f hQ hf het
  classical
  letI : Algebra C (TensorProduct A Ω C) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra B (TensorProduct A Ω B) := Algebra.TensorProduct.rightAlgebra
  set ψ := ((algebraMap (TensorProduct A Ω B) (Localization.Away f)).comp
    (Algebra.TensorProduct.map (AlgHom.id A Ω) (IsScalarTower.toAlgHom A C B)).toRingHom) with hψ
  letI : Algebra (TensorProduct A Ω C) (Localization.Away f) := ψ.toAlgebra
  haveI : Algebra.Etale (TensorProduct A Ω C) (Localization.Away f) := het
  haveI : IsScalarTower Ω (TensorProduct A Ω C) (Localization.Away f) :=
    IsScalarTower.of_algebraMap_eq fun w => by
      change _ = ψ _
      simp [hψ, Algebra.TensorProduct.algebraMap_apply, IsScalarTower.algebraMap_apply Ω (TensorProduct A Ω B) (Localization.Away f)]

  have hunit : IsUnit (algebraMap (TensorProduct A Ω B) Q'.ResidueField f) := by
    rw [isUnit_iff_ne_zero, Ne, Ideal.algebraMap_residueField_eq_zero]; exact hf
  letI : Algebra (Localization.Away f) Q'.ResidueField :=
    (Localization.awayLift (algebraMap (TensorProduct A Ω B) Q'.ResidueField) f hunit).toAlgebra
  have hlift : ∀ s, algebraMap (Localization.Away f) Q'.ResidueField
      (algebraMap (TensorProduct A Ω B) (Localization.Away f) s) =
      algebraMap (TensorProduct A Ω B) Q'.ResidueField s := fun s =>
    IsLocalization.Away.lift_eq f hunit s
  have hBK : ∀ b : B, algebraMap B Q'.ResidueField b =
      algebraMap (TensorProduct A Ω B) Q'.ResidueField (algebraMap B (TensorProduct A Ω B) b) := by
    intro b
    rw [IsScalarTower.algebraMap_apply B (Localization.AtPrime Q') Q'.ResidueField,
      IsScalarTower.algebraMap_apply B (TensorProduct A Ω B) (Localization.AtPrime Q'),
      ← IsScalarTower.algebraMap_apply]
  letI : Algebra C Q'.ResidueField := ((algebraMap B Q'.ResidueField).comp (algebraMap C B)).toAlgebra
  haveI : IsScalarTower C B Q'.ResidueField := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨eB, heB⟩ := GlobalTheory.kaehler_fibre_equiv_pushout_formallyEtale A Ω B (TensorProduct A Ω B)
    (Localization.Away f) Q'.ResidueField (fun x => by rw [hlift, hBK])
  obtain ⟨eC, heC⟩ := GlobalTheory.kaehler_fibre_equiv_pushout_formallyEtale A Ω C (TensorProduct A Ω C)
    (Localization.Away f) Q'.ResidueField (fun x => by
      change algebraMap B Q'.ResidueField (algebraMap C B x) =
        algebraMap (Localization.Away f) Q'.ResidueField (ψ ((1 : Ω) ⊗ₜ[A] x))
      rw [hBK, hψ, RingHom.comp_apply, hlift]
      congr 1)
  set K := Q'.ResidueField
  let E := eC.trans eB.symm
  have hE : ∀ c : C, E ((1 : K) ⊗ₜ[C] KaehlerDifferential.D A C c) =
      (1 : K) ⊗ₜ[B] KaehlerDifferential.D A B (algebraMap C B c) := by
    intro c
    simp only [E, LinearEquiv.trans_apply, heC, LinearEquiv.symm_apply_eq, heB]
    rfl
  have hE' : ∀ ω : Ω[C⁄A], E ((1 : K) ⊗ₜ[C] ω) =
      (1 : K) ⊗ₜ[B] KaehlerDifferential.map A A C B ω := by
    intro ω
    have hω : ω ∈ Submodule.span C (Set.range (KaehlerDifferential.D A C)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hω using Submodule.span_induction with
    | mem x hx => obtain ⟨c, rfl⟩ := hx; rw [hE, KaehlerDifferential.map_D]
    | zero => simp
    | add x y _ _ hx hy => rw [TensorProduct.tmul_add, map_add, hx, hy, map_add, TensorProduct.tmul_add]
    | smul c x _ hx =>
      have h1 : (1 : K) ⊗ₜ[C] (c • x) = algebraMap C K c • ((1 : K) ⊗ₜ[C] x) := by
        rw [TensorProduct.tmul_smul]; exact (algebraMap_smul K c _).symm
      rw [h1, map_smul, hx, LinearMap.map_smul_of_tower, ← algebraMap_smul B c,
        TensorProduct.tmul_smul, ← algebraMap_smul K (algebraMap C B c)]
      rfl
  have hE'' : ∀ (k : K) (ω : Ω[C⁄A]), E (k ⊗ₜ[C] ω) = k ⊗ₜ[B] KaehlerDifferential.map A A C B ω := by
    intro k ω
    have h1 : k ⊗ₜ[C] ω = k • ((1 : K) ⊗ₜ[C] ω) := by rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [h1, map_smul, hE', TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  letI : Algebra Q.ResidueField K :=
    (Ideal.ResidueField.map Q Q' (algebraMap B (TensorProduct A Ω B)) (by rw [← hQ]; rfl)).toAlgebra
  haveI : IsScalarTower B Q.ResidueField K := IsScalarTower.of_algebraMap_eq fun b => by
    rw [RingHom.algebraMap_toAlgebra, Ideal.ResidueField.map_algebraMap, hBK]
  rw [← LinearMap.baseChange_eq_ltensor,
    ← Module.FaithfullyFlat.lTensor_bijective_iff_bijective Q.ResidueField K]
  let cM := TensorProduct.AlgebraTensorModule.cancelBaseChange B Q.ResidueField K K
    (TensorProduct C B Ω[C⁄A])
  let cN := TensorProduct.AlgebraTensorModule.cancelBaseChange B Q.ResidueField K K Ω[B⁄A]
  let cC := TensorProduct.AlgebraTensorModule.cancelBaseChange C B K K Ω[C⁄A]
  have key : ∀ z, ((KaehlerDifferential.mapBaseChange A C B).baseChange Q.ResidueField).lTensor K z =
      cN.symm (E (cC (cM z))) := by
    intro z
    rw [LinearEquiv.eq_symm_apply]
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul k y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y₁ y₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, h₁, h₂]
      | tmul l m =>
        induction m using TensorProduct.induction_on with
        | zero => simp
        | add m₁ m₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, h₁, h₂]
        | tmul b ω =>
          simp only [cM, cN, cC, LinearMap.lTensor_tmul, LinearMap.baseChange_tmul,
            TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
            KaehlerDifferential.mapBaseChange_tmul, hE'', TensorProduct.smul_tmul]
  have hfun : ⇑(((KaehlerDifferential.mapBaseChange A C B).baseChange Q.ResidueField).lTensor K) =
      ⇑cN.symm ∘ ⇑E ∘ ⇑cC ∘ ⇑cM := funext key
  rw [hfun]
  exact cN.symm.bijective.comp (E.bijective.comp (cC.bijective.comp cM.bijective))

end GlobalTheory.Mum
