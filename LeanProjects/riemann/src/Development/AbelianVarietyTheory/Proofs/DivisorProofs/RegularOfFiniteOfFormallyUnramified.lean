import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsEtaleCompletionCompOpenImmersion
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSharpGen
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnramifiedExtensionGroupLiftStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkSpecializesCompatRingMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRegularLocalRingAdicCompletion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Integral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompleteLocalEtaleNeighbourhood
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeConditionsCoverModels
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

namespace GlobalTheory.InteriorChart

theorem bijective_stalkSpecializes {X : Scheme.{0}} {x y : X} (e : x = y) (h : x ⤳ y) :
    Function.Bijective (X.presheaf.stalkSpecializes h).hom := by
  subst e
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  exact Function.bijective_id

theorem isEtaleCompletion_comp {A B C : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [CommRing C]
    [IsLocalRing C] (φ : A →+* B) (ρ : B →+* C) [IsLocalHom ρ] (hφ : IsEtaleCompletion φ) (hf : ρ.Flat)
    (hm : (maximalIdeal B).map ρ = maximalIdeal C) (hfin : ρ.Finite) : IsEtaleCompletion (ρ.comp φ) := by
  obtain ⟨h1, h2, h3⟩ := hφ
  refine ⟨RingHom.Flat.comp h1 hf, ?_, ?_⟩
  · rw [← Ideal.map_map, h2, hm]
  · have e : (residue C).comp (ρ.comp φ) = (ResidueField.map ρ).comp ((residue B).comp φ) := by
      rw [← RingHom.comp_assoc, ← ResidueField.map_comp_residue, RingHom.comp_assoc]
    rw [e]
    have hm' : (ResidueField.map ρ).Finite := by
      have h := RingHom.Finite.comp (RingHom.Finite.of_surjective (residue C) residue_surjective) hfin
      rw [← ResidueField.map_comp_residue] at h
      exact RingHom.Finite.of_comp_finite h
    exact RingHom.Finite.comp hm' h3

theorem regular_of_finite_of_formallyUnramified {A B : Type} [CommRing A] [CommRing B] [IsRegularLocalRing A]
    [IsLocalRing B] (ρ : A →+* B) [IsLocalHom ρ] (hi : Function.Injective ρ) (hfin : ρ.Finite)
    (hu : ρ.FormallyUnramified) :
    (maximalIdeal A).map ρ = maximalIdeal B ∧ IsRegularLocalRing B ∧ ρ.Flat := by
  algebraize [ρ]
  haveI : IsLocalHom (algebraMap A B) := ‹IsLocalHom ρ›
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B := Algebra.FormallyUnramified.map_maximalIdeal
  have hd : ringKrullDim B = ringKrullDim A := ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective hi
  haveI hreg : IsRegularLocalRing B := by
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    have h1 := Ideal.spanFinrank_map_le_of_fg (algebraMap A B) (maximalIdeal A).fg_of_isNoetherianRing
    rw [hm] at h1
    rw [hd, ← IsRegularLocalRing.spanFinrank_maximalIdeal]
    exact_mod_cast h1
  refine ⟨hm, hreg, ?_⟩
  haveI : Module.Free A B := GlobalTheory.free_of_isRegularLocalRing_of_finite hd.symm
  exact (inferInstance : Module.Flat A B)

theorem completedStalk_chart (X : Scheme.{0}) (x : X) [IsNoetherianRing (X.presheaf.stalk x)] :
    IsEtaleCompletion (Scheme.stalkClosedPointTo (GlobalTheory.fromSpecCompletedStalk X x)).hom ∧
      Function.Surjective ((residue (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))).comp
        (Scheme.stalkClosedPointTo (GlobalTheory.fromSpecCompletedStalk X x)).hom) := by
  have fg : (maximalIdeal (X.presheaf.stalk x)).FG := IsNoetherian.noetherian _
  have hm := AdicCompletion.maximalIdeal_eq_map_of_fg fg
  let φ := algebraMap (X.presheaf.stalk x) (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
  haveI : IsLocalHom φ := ((IsLocalRing.local_hom_TFAE φ).out 0 2).mpr hm.symm.le
  have hres : Function.Surjective ((residue _).comp φ) := by
    intro r
    obtain ⟨a, ha⟩ := (AdicCompletion.residueField_map_bijective (X.presheaf.stalk x)).2 r
    obtain ⟨b, rfl⟩ := residue_surjective a
    refine ⟨b, ?_⟩
    rw [← ha, RingHom.comp_apply, ResidueField.map_residue]
  have hx : GlobalTheory.fromSpecCompletedStalk X x (closedPoint _) = x := by
    rw [GlobalTheory.fromSpecCompletedStalk]
    erw [Scheme.Hom.comp_apply]
    have hc : Spec.map (CommRingCat.ofHom φ) (closedPoint _) = closedPoint (X.presheaf.stalk x) :=
      IsLocalRing.comap_closedPoint φ
    erw [hc]
    exact Scheme.fromSpecStalk_closedPoint
  obtain ⟨e, he, hψ⟩ := GlobalTheory.GenFan.stalk_factor_eq hx (CommRingCat.ofHom φ)
    (Scheme.stalkClosedPointTo (GlobalTheory.fromSpecCompletedStalk X x))
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk _)
  refine ⟨?_, ?_⟩
  · rw [hψ]
    exact isEtaleCompletion_comp_bij e he φ ⟨RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian _),
      hm.symm, RingHom.Finite.of_surjective _ hres⟩
  · rw [hψ, ← RingHom.comp_assoc]
    exact hres.comp he.2

end GlobalTheory.InteriorChart

namespace GlobalTheory.InteriorChart

theorem chart : ∀ (g n : ℕ), 3 ≤ n → ∀ (F : SFam g n (zetaAway n)) (x₀ : F.X), ∃ (R : Type) (_ : CommRing R) (_ : IsRegularLocalRing R) (_ : IsDomain R) (ξ₀ : Sp R ⟶ F.X), IsAdicComplete (maximalIdeal R) R ∧ CharZero R ∧ ξ₀ (closedPoint R) = x₀ ∧ IsEtaleCompletion (Scheme.stalkClosedPointTo ξ₀).hom ∧ ((residue R).comp (Scheme.stalkClosedPointTo ξ₀).hom).FormallyUnramified ∧ ∃ (B : Over (Sp R)) (_ : GrpObj B) (_ : IsCommMonObj B) (β : B.left ⟶ F.univ.A.left) (β₂ : (G2 B).left ⟶ (G2 F.univ.A).left) (M : RigLB B) (_ : CubicalStr B M), IsGrpPullback B F.univ.A ξ₀ β ∧ IsSquare β β₂ ∧ RelAmple B M.L ∧ KTriv B M.L ∧ LBIso (abelian₂ B M.L) (F.univ.P.pull β₂) := by
  intro g n _ F x₀

  haveI : IsRegularLocalRing (GlobalTheory.LowChart.W F (r := 0) x₀) := GlobalTheory.LowChart.isRegularLocalRing_W_of_isRegularRing F (r := 0) x₀
  haveI hc₀ : IsAdicComplete (maximalIdeal (GlobalTheory.LowChart.W F (r := 0) x₀)) (GlobalTheory.LowChart.W F (r := 0) x₀) :=
    GlobalTheory.LowChart.isAdicComplete_completedStalkSiegelFibrePower F (r := 0) x₀
  haveI : CharZero (GlobalTheory.LowChart.W F (r := 0) x₀) := GlobalTheory.LowChart.charZero_W_of_charZero F (r := 0) x₀
  haveI : IsRegularLocalRing (F.X.presheaf.stalk x₀) := GlobalTheory.LowChart.isRegularLocalRing_stalk F (r := 0) x₀
  let y₀ : Sp (GlobalTheory.LowChart.W F (r := 0) x₀) ⟶ F.X := GlobalTheory.LowChart.toPow F (r := 0) x₀
  have hx : y₀ (closedPoint (GlobalTheory.LowChart.W F (r := 0) x₀)) = x₀ := GlobalTheory.LowChart.toPow_closedPoint F (r := 0) x₀
  obtain ⟨hEt₀, hres₀⟩ := completedStalk_chart F.X x₀
  change IsEtaleCompletion (Scheme.stalkClosedPointTo y₀).hom at hEt₀
  change Function.Surjective ((residue (GlobalTheory.LowChart.W F (r := 0) x₀)).comp (Scheme.stalkClosedPointTo y₀).hom) at hres₀

  obtain ⟨R', _, _, ρ, hc', hloc, hinj, hfin, hfu, B, _, _, β, β₂, M, hcub, hpb, hsq, hamp, hk, hiso⟩ :=
    GlobalTheory.T.finite_unramified_extension_group_lift F (GlobalTheory.LowChart.W F (r := 0) x₀) hc₀ y₀
  obtain ⟨hm', hreg', hflat⟩ := regular_of_finite_of_formallyUnramified ρ hinj hfin hfu
  have hdom : IsDomain R' := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R').1
  have hcz : CharZero R' := charZero_of_injective_ringHom hinj
  let ξ₀ : Sp R' ⟶ F.X := spMap ρ ≫ y₀
  have hcp : ξ₀ (closedPoint R') = y₀ (closedPoint (GlobalTheory.LowChart.W F (r := 0) x₀)) := by
    show y₀ (spMap ρ (closedPoint R')) = _
    rw [show spMap ρ (closedPoint R') = closedPoint (GlobalTheory.LowChart.W F (r := 0) x₀) from IsLocalRing.comap_closedPoint ρ]
  have hs : ξ₀ (closedPoint R') ⤳ y₀ (closedPoint (GlobalTheory.LowChart.W F (r := 0) x₀)) := specializes_of_eq hcp
  have key := GlobalTheory.TorRef.stalkClosedPointTo_comp_spMap_specializes F.X y₀ ρ hs
  let E := RingEquiv.ofBijective (F.X.presheaf.stalkSpecializes hs).hom (bijective_stalkSpecializes hcp hs)
  have hξ : (Scheme.stalkClosedPointTo ξ₀).hom =
      (ρ.comp (Scheme.stalkClosedPointTo y₀).hom).comp E.symm.toRingHom := by
    ext b
    obtain ⟨a, rfl⟩ := E.surjective b
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.symm_apply_apply]
    exact key a
  refine ⟨R', inferInstance, hreg', hdom, ξ₀, hc', hcz, hcp.trans hx, ?_, ?_, B, inferInstance, inferInstance, β, β₂, M,
    hcub, hpb, hsq, hamp, hk, hiso⟩
  · rw [hξ]
    exact isEtaleCompletion_comp_bij _ E.symm.bijective _ (isEtaleCompletion_comp _ ρ hEt₀ hflat hm' hfin)
  · have hmap : (ResidueField.map ρ).FormallyUnramified := by
      apply RingHom.FormallyUnramified.of_comp (f := residue (GlobalTheory.LowChart.W F (r := 0) x₀))
      rw [ResidueField.map_comp_residue]
      exact RingHom.FormallyUnramified.comp hfu (RingHom.FormallyUnramified.of_surjective residue_surjective)
    have e2 : (residue R').comp (Scheme.stalkClosedPointTo ξ₀).hom = (ResidueField.map ρ).comp
        (((residue (GlobalTheory.LowChart.W F (r := 0) x₀)).comp (Scheme.stalkClosedPointTo y₀).hom).comp E.symm.toRingHom) := by
      rw [hξ, ← RingHom.comp_assoc, ← RingHom.comp_assoc, ← ResidueField.map_comp_residue]
      rfl
    rw [e2]
    exact RingHom.FormallyUnramified.comp
      (RingHom.FormallyUnramified.of_surjective (hres₀.comp E.symm.surjective)) hmap

end GlobalTheory.InteriorChart
