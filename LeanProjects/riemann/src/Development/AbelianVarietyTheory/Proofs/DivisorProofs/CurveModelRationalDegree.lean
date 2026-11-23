import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LineBundleIntersectionNumberGroundFieldChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RatFibreClosure

theorem isPullback_spec_ringOfIntegers (F : Type) [Field F] [NumberField F] :
    IsPullback (spMap (algebraMap (𝓞 F) F)) (spMap (algebraMap ℚ F))
      (spMap (Int.castRingHom (𝓞 F))) (spMap (Int.castRingHom ℚ)) := by
  have h : Algebra.IsPushout ℤ (𝓞 F) ℚ F :=
    (Algebra.isLocalization_iff_isPushout (nonZeroDivisors ℤ) ℚ).1 inferInstance
  have h' := (CommRingCat.isPushout_iff_isPushout (R := ℤ) (R' := 𝓞 F) (S := ℚ) (S' := F)).2 h
  exact isPullback_SpecMap_of_isPushout _ _ _ _ h'

theorem ratDeg_eq_finrank_mul_interNumRed : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (P : TrueGeo.Model Y) (Z : Closeds Y.X), IsCompleteCurve F Z → ∀ (W : Scheme.{0}) (w : W ⟶ P.X) (z : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ⟶ W), IsArithVar (w ≫ P.p) 1 → z ≫ w = redι Z ≫ P.j → IsPullback z (redι Z ≫ Y.str) (w ≫ P.p) (spMap (algebraMap (𝓞 F) F)) → ∀ M : LB P.X, M.IsLB → ratDeg (w ≫ P.p) (M.pull w) = (Module.finrank ℚ F : ℤ) * interNumRed F Z ![M.pull P.j] := by
  intro F _ _ Y P Z hZ W w z hW hzw H M hM
  letI iF : Algebra F Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) := algebraΓOfHom (redι Z ≫ Y.str)
  letI iQ : Algebra ℚ Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) := ((algebraMap F Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤)).comp (algebraMap ℚ F)).toAlgebra
  haveI : IsScalarTower ℚ F Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) := .of_algebraMap_eq fun _ ↦ rfl
  have hi : ∀ r : F, (redι Z).appTop (algebraMap F Γ(Y.X, ⊤) r) = algebraMap F Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) r :=
    fun _ ↦ rfl
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := isIntegral_red hZ.isIrreducible
  have hC : VB.IsProjCurve F (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
    refine ⟨inferInstance, (topologicalKrullDim_red Z).trans hZ.dim_eq, ?_⟩
    rw [strHom_eq (f := redι Z ≫ Y.str) fun _ ↦ rfl]
    obtain ⟨n, f, hf, hs⟩ := Y.isProjOver
    exact ⟨n, redι Z ≫ f, inferInstance, by rw [Category.assoc, hs]⟩

  have H' := H.paste_vert (isPullback_spec_ringOfIntegers F)
  set R := ratFibre (w ≫ P.p)
  set e : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≅ R := H'.isoIsPullback _ _ (ratFibre.isPullback (w ≫ P.p)) with he
  have efst : e.hom ≫ ratFibre.fst (w ≫ P.p) = z := IsPullback.isoIsPullback_hom_fst _ _ H' (ratFibre.isPullback _)
  have hf : ∀ r : ℚ, e.hom.appTop (algebraMap ℚ Γ(R, ⊤) r) = algebraMap ℚ Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) r := fun r ↦
    RingHom.congr_fun (RingHom.ext_rat (e.hom.appTop.hom.comp (algebraMap ℚ _)) (algebraMap ℚ _)) r

  set L := (M.pull w).pull (ratFibre.fst (w ≫ P.p)) with hLdef
  set N := (M.pull P.j).pull (redι Z) with hNdef
  have hL : L.IsLB := Semi.LB.isLB_pull (Semi.LB.isLB_pull hM _) _
  have hN : N.IsLB := Semi.LB.isLB_pull (Semi.LB.isLB_pull hM _) _
  have hLe : (L.pull e.hom).IsLB := Semi.LB.isLB_pull hL _
  have hcls : cls (L.pull e.hom) hLe = cls N hN := by
    rw [cls_pull hL, cls_pull (Semi.LB.isLB_pull hM _), cls_pull hM, cls_pull (Semi.LB.isLB_pull hM _),
      cls_pull hM]
    simp only [← pull_comp, ← Category.assoc, efst, hzw]

  have h₁ : chi ℚ (structureModule R) = chi ℚ (structureModule (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) :=
    (chi_congr ℚ (asIso (unitToPush e.hom))).trans (chi_pushforward_of_isClosedImmersion hf _)
  have h₂ : chi ℚ (toMod L) = chi ℚ (twist (structureModule (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) N) := by
    refine (chi_congr ℚ (Twist.unitTwistIso L)).symm.trans ?_
    refine (chi_congr ℚ ((twistFunctor L).mapIso (asIso (unitToPush e.hom)))).trans ?_
    refine (chi_twist_pushforward_of_isClosedImmersion hf _ L).trans ?_
    exact (nonempty_twist_iso_of_cls_eq _ hLe hN hcls).elim (chi_congr ℚ)

  have h₃ : interNumRed F Z ![M.pull P.j] = chi F (twist (structureModule (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) N) - chi F (structureModule (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) := by
    have e₁ := interNumOn_eq_interNum_pull (k := F) (L := ![M.pull P.j]) hi
      (fun i ↦ by fin_cases i; exact Semi.LB.isLB_pull hM _)
    have e₂ := hC.degLB_eq_interNum hN
    rw [VB.degLB_eq hN, ← chi_congr F (Twist.unitTwistIso N)] at e₂
    rw [interNumRed_def, interNumSub_def]
    refine e₁.trans (Eq.trans ?_ e₂.symm)
    congr 1
    funext i
    fin_cases i
    rfl
  rw [ratDeg, degOfRank, h₁, h₂, h₃, GroundFieldChange.chi_fieldChange ℚ F (Scheme.IdealSheafData.vanishingIdeal Z).subscheme,
    GroundFieldChange.chi_fieldChange ℚ F (Scheme.IdealSheafData.vanishingIdeal Z).subscheme]
  push_cast
  ring

end GlobalTheory.RatFibreClosure
