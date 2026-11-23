import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfDerHomEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTangentEqOfCrystallineValuesEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineFormTangentValueMulAbelianScheme
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentValuePullbackCrystallineFormDualNumbersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueFormsFunctionalAbelianBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateDualNumberPointInverseConstantTangentStatement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
open MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ParPt

theorem t4 : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (A : Over (Sp R)) (A' : Over (Sp R')) (φ : A'.left ⟶ A.left) (m : IsMor (dp0 R) (A.hom ≫ 𝟙 (Sp R)) (dp0 R') (A'.hom ≫ 𝟙 (Sp R')) (algebraMap R R') φ) (v : epsR R' ⟶ A') (hy : (v.left ≫ φ) ≫ A.hom ≫ 𝟙 (Sp R) = spMap (algebraMap R (DualNumber R'))) (f : Form (A.hom ≫ 𝟙 (Sp R))), tanVal v (m.pullForm f) = TrivSqZeroExt.snd ((SqExt.ofModule R R' R').val (v.left ≫ φ) hy f.1) := GlobalTheory.T.tangent_value_pullback_crystalline_form_dual_numbers

theorem t5 : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (R' : Type) [CommRing R'] [Algebra R R'] (A' : Over (Sp R')) (φ : A'.left ⟶ A.left), IsPullback φ A'.hom A.hom (spMap (algebraMap R R')) → ∀ (m : IsMor (dp0 R) (A.hom ≫ 𝟙 (Sp R)) (dp0 R') (A'.hom ≫ 𝟙 (Sp R')) (algebraMap R R') φ) (l : GlobForm (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] R'), ∃! ψ : Form (A'.hom ≫ 𝟙 (Sp R')) →ₗ[R'] R', (∀ f, cmpForm (A'.hom ≫ 𝟙 (Sp R')) f = 0 → ψ f = 0) ∧ ∀ f, ψ (m.pullForm f) = l (GlobalTheory.LieDual.glob (A.hom ≫ 𝟙 (Sp R)) f) := GlobalTheory.T.existsUnique_forms_functional_abelian_base_change

theorem t6 : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (S : Type) [CommRing S] (A : Over (Sp S)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (c : epsR S ⟶ A) (p : Sp S ⟶ A.left), c.left = spMap (algebraMap S (DualNumber S)) ≫ p → ∀ y : epsR S ⟶ A, (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ y.left = spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ c.left ↔ IsTangent (y * c⁻¹)) ∧ ∀ f, tanVal y f = tanVal (y * c⁻¹) f := GlobalTheory.T.translate_dual_number_point_inverse_constant_tangent

section Main

variable {R : Type} [CommRing R] (A : Over (Sp R)) (V : A.left.affineOpens)

local notation "𝔰" => A.hom ≫ 𝟙 (Sp R)
local notation "𝔅" => Sec (A.hom ≫ 𝟙 (Sp R)) (Subtype.val V)
set_option quotPrecheck false in
local notation "𝔄" => (Over.pullback (spMap (algebraMap R (Sec (A.hom ≫ 𝟙 (Sp R)) (Subtype.val V))))).obj A
local notation "𝔣" => pullback.fst A.hom (spMap (algebraMap R (Sec (A.hom ≫ 𝟙 (Sp R)) (Subtype.val V))))

theorem affPt_hom : affPt (𝔰) V ≫ A.hom = spMap (algebraMap R 𝔅) :=
  (congrArg (affPt (𝔰) V ≫ ·) (Category.comp_id A.hom).symm).trans (affPt_w _ V)

theorem derHom_hom (δ : Ω[𝔅⁄R] →ₗ[𝔅] 𝔅) :
    (spMap (derHom δ : 𝔅 →+* DualNumber 𝔅) ≫ affPt (𝔰) V) ≫ A.hom =
      spMap (algebraMap 𝔅 (DualNumber 𝔅)) ≫ spMap (algebraMap R 𝔅) := by
  rw [Category.assoc, affPt_hom, ← Cris.spMap_comp, ← Cris.spMap_comp, AlgHom.comp_algebraMap,
    ← IsScalarTower.algebraMap_eq]

def ptOf (δ : Ω[𝔅⁄R] →ₗ[𝔅] 𝔅) : epsR 𝔅 ⟶ 𝔄 :=
  Over.homMk (pullback.lift (spMap (derHom δ : 𝔅 →+* DualNumber 𝔅) ≫ affPt (𝔰) V)
    (spMap (algebraMap 𝔅 (DualNumber 𝔅))) (derHom_hom A V δ)) (pullback.lift_snd _ _ _)

theorem ptOf_fst (δ : Ω[𝔅⁄R] →ₗ[𝔅] 𝔅) :
    (ptOf A V δ).left ≫ 𝔣 = spMap (derHom δ : 𝔅 →+* DualNumber 𝔅) ≫ affPt (𝔰) V :=
  pullback.lift_fst _ _ _

theorem ptOf_snd (δ : Ω[𝔅⁄R] →ₗ[𝔅] 𝔅) :
    (ptOf A V δ).left ≫ pullback.snd A.hom (spMap (algebraMap R 𝔅)) = spMap (algebraMap 𝔅 (DualNumber 𝔅)) :=
  pullback.lift_snd _ _ _

def basePt : Sp 𝔅 ⟶ (𝔄).left :=
  pullback.lift (affPt (𝔰) V) (𝟙 _) (by rw [affPt_hom, Category.id_comp])

theorem ptOf_zero : (ptOf A V 0).left = spMap (algebraMap 𝔅 (DualNumber 𝔅)) ≫ basePt A V := by
  refine pullback.hom_ext ?_ ?_
  · rw [ptOf_fst, basePt, Category.assoc, pullback.lift_fst]
    congr 2
    ext b <;> simp [derHom, TrivSqZeroExt.algebraMap_eq_inl']
  · rw [ptOf_snd, basePt, Category.assoc, pullback.lift_snd]
    exact (Category.comp_id _).symm

theorem fst_derHom_spMap (δ : Ω[𝔅⁄R] →ₗ[𝔅] 𝔅) : spMap (TrivSqZeroExt.fstHom 𝔅 𝔅 𝔅).toRingHom ≫
    spMap (derHom δ : 𝔅 →+* DualNumber 𝔅) = 𝟙 _ := by
  refine (Cris.spMap_comp _ _).symm.trans ((congrArg spMap ?_).trans (Cris.spMap_id _))
  ext b
  exact fst_derHom δ b

theorem ptOf_red (δ : Ω[𝔅⁄R] →ₗ[𝔅] 𝔅) : spMap (TrivSqZeroExt.fstHom 𝔅 𝔅 𝔅).toRingHom ≫ (ptOf A V δ).left =
    spMap (TrivSqZeroExt.fstHom 𝔅 𝔅 𝔅).toRingHom ≫ (ptOf A V 0).left := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, ptOf_fst, ptOf_fst, ← Category.assoc, ← Category.assoc,
      fst_derHom_spMap, fst_derHom_spMap]
  · rw [Category.assoc, Category.assoc, ptOf_snd, ptOf_snd]

theorem over_fst (y : epsR 𝔅 ⟶ 𝔄) : (y.left ≫ 𝔣) ≫ 𝔰 = spMap (algebraMap R (DualNumber 𝔅)) := by
  rw [← Category.assoc]
  refine (Category.comp_id _).trans ?_
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  erw [Over.w y]
  change spMap _ ≫ spMap _ = _
  rw [← Cris.spMap_comp, ← IsScalarTower.algebraMap_eq]

theorem isMor_fst : IsMor (dp0 R) (𝔰) (dp0 𝔅) ((𝔄).hom ≫ 𝟙 (Sp 𝔅)) (algebraMap R 𝔅) 𝔣 :=
  IsMor.of_dividedPowersZeroIdeal _ (by rw [Category.comp_id, Category.comp_id]; exact pullback.condition)

theorem tanVal_ptOf (δ : Ω[𝔅⁄R] →ₗ[𝔅] 𝔅) (f : Form (𝔰)) :
    tanVal (ptOf A V δ) ((isMor_fst A V).pullForm f) = δ ((GlobalTheory.LieDual.glob (𝔰) f).1 (Opposite.op V)) :=
  (t4 R 𝔅 A 𝔄 𝔣 (isMor_fst A V) (ptOf A V δ) (over_fst A V _) f).trans
    (snd_val_derHom (𝔰) V δ _ (over_fst A V _) (ptOf_fst A V δ).symm f)

variable (hC : CrystallineSmoothLift) (hH : AbelianHodgeDeRham) [GrpObj A] (g : ℕ) (hab : IsAbelianScheme A)
  (hdim : SmoothOfRelativeDimension g A.hom)

include hC hH hab hdim in
theorem key (l : GlobForm 𝔰 →ₗ[R] 𝔅) :
    ∃! δ : Ω[𝔅⁄R] →ₗ[𝔅] 𝔅, ∀ w : GlobForm 𝔰, δ (w.1 (Opposite.op V)) = l w := by
  have hφ : IsGrpPullback (𝔄) A (spMap (algebraMap R 𝔅)) (𝔣) := isGrpPullback_pullback A _
  have habB := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hab hφ
  have hdimB : SmoothOfRelativeDimension g (𝔄).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback hφ.1 hdim
  have hglob := GlobalTheory.LieDual.glob_surjective hC hH A g hab hdim
  have uniq : ∀ δ₁ δ₂ : Ω[𝔅⁄R] →ₗ[𝔅] 𝔅, (∀ w : GlobForm 𝔰, δ₁ (w.1 (Opposite.op V)) = l w) →
      (∀ w : GlobForm 𝔰, δ₂ (w.1 (Opposite.op V)) = l w) → δ₁ = δ₂ := by
    intro δ₁ δ₂ h₁ h₂
    have T₁ := t6 hC hH 𝔅 𝔄 g habB hdimB (ptOf A V 0) (basePt A V) (ptOf_zero A V) (ptOf A V δ₁)
    have T₂ := t6 hC hH 𝔅 𝔄 g habB hdimB (ptOf A V 0) (basePt A V) (ptOf_zero A V) (ptOf A V δ₂)
    have ht₁ := T₁.1.1 (ptOf_red A V δ₁)
    have ht₂ := T₂.1.1 (ptOf_red A V δ₂)
    have k₁ : ∀ f, tanVal (ptOf A V δ₁ * (ptOf A V 0)⁻¹) ((isMor_fst A V).pullForm f) = l (GlobalTheory.LieDual.glob (𝔰) f) :=
      fun f ↦ (T₁.2 _).symm.trans ((tanVal_ptOf A V δ₁ f).trans (h₁ _))
    have k₂ : ∀ f, tanVal (ptOf A V δ₂ * (ptOf A V 0)⁻¹) ((isMor_fst A V).pullForm f) = l (GlobalTheory.LieDual.glob (𝔰) f) :=
      fun f ↦ (T₂.2 _).symm.trans ((tanVal_ptOf A V δ₂ f).trans (h₂ _))
    have hψ := (t5 hC hH R A g hab hdim 𝔅 𝔄 𝔣 hφ.1 (isMor_fst A V) l).unique
      ⟨fun f hf ↦ GlobalTheory.TanVanish.tanVal_eq_zero_of_cmpForm_eq_zero 𝔅 𝔄 _ f hf, k₁⟩
      ⟨fun f hf ↦ GlobalTheory.TanVanish.tanVal_eq_zero_of_cmpForm_eq_zero 𝔅 𝔄 _ f hf, k₂⟩
    have hv := GlobalTheory.LieInj.tangent_eq_of_tanVal_eq hC hH 𝔅 𝔄 g habB hdimB _ _ ht₁ ht₂
      fun f ↦ LinearMap.congr_fun hψ f
    have hy : ptOf A V δ₁ = ptOf A V δ₂ := mul_right_cancel hv
    apply eq_of_affPt_eq (𝔰) V
    rw [← ptOf_fst, ← ptOf_fst, hy]
  obtain ⟨ψ, ⟨hψ0, hψ⟩, -⟩ := t5 hC hH R A g hab hdim 𝔅 𝔄 𝔣 hφ.1 (isMor_fst A V) l
  obtain ⟨v, hv, hvψ⟩ := GlobalTheory.LieDual.exists_tangent_of_functional hC hH 𝔅 𝔄 g habB hdimB ψ hψ0
  have T := t6 hC hH 𝔅 𝔄 g habB hdimB (ptOf A V 0) (basePt A V) (ptOf_zero A V) (v * ptOf A V 0)
  have hvc : v * ptOf A V 0 * (ptOf A V 0)⁻¹ = v := mul_inv_cancel_right v _
  have hr := T.1.2 (hvc.symm ▸ hv)
  have hred' : spMap (TrivSqZeroExt.fstHom 𝔅 𝔅 𝔅).toRingHom ≫ ((v * ptOf A V 0).left ≫ 𝔣) = affPt (𝔰) V := by
    rw [← Category.assoc, hr, Category.assoc, ptOf_fst, ← Category.assoc, fst_derHom_spMap, Category.id_comp]
  obtain ⟨δ, hδ⟩ := exists_derHom (𝔰) V _ (over_fst A V _) hred'
  have hmain : ∀ w : GlobForm 𝔰, δ (w.1 (Opposite.op V)) = l w := by
    intro w
    obtain ⟨f, rfl⟩ := hglob w
    have e1 := snd_val_derHom (𝔰) V δ _ (over_fst A V (v * ptOf A V 0)) hδ f
    have e2 := t4 R 𝔅 A 𝔄 𝔣 (isMor_fst A V) (v * ptOf A V 0) (over_fst A V _) f
    have e3 : tanVal (v * ptOf A V 0) ((isMor_fst A V).pullForm f) = l (GlobalTheory.LieDual.glob (𝔰) f) :=
      (T.2 _).trans ((congrArg (fun z ↦ tanVal z ((isMor_fst A V).pullForm f)) hvc).trans ((hvψ _).trans (hψ f)))
    exact e1.symm.trans (e2.symm.trans e3)
  exact ⟨δ, hmain, fun δ' h' ↦ uniq δ' δ h' hmain⟩

end Main

theorem exists_unique_of_globForm : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (U : AffOp A.left) (l : GlobForm A.hom →ₗ[R] Sec A.hom U.unop.1), ∃! δ : Ω[Sec A.hom U.unop.1⁄R] →ₗ[Sec A.hom U.unop.1] Sec A.hom U.unop.1, ∀ w : GlobForm A.hom, δ (w.1 U) = l w := by
  intro hC hH R _ A _ g hab hdim U l
  have k := fun l ↦ key A U.unop hC hH g hab hdim l
  rw [Category.comp_id] at k
  exact k l

end GlobalTheory.ParPt
