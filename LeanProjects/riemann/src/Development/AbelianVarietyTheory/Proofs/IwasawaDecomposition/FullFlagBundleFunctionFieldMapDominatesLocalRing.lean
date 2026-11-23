import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoBear
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsChartFiniteType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPointCarriesFrameFlagsOwnFrameStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagCommonClosedPointOfGenericStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointsCarryCommonFlagSpectrumMapFieldExtStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfBearCommonFullFlagStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

namespace GlobalTheory.FlagBundle.Dom

theorem mem_O_of_forall_dvr {F : Type} [Field F] (Y : Var F) (y : (ratOf Y).Z) (x : Y.Fn)
    (hx : ∀ V : ValuationSubring Y.Fn, IsDiscreteValuationRing V →
      LocalSubring.range (algebraMap ((ratOf Y).O y) Y.Fn) ≤ V.toLocalSubring → x ∈ V) :
    x ∈ (ratOf Y).O y := by
  haveI := (ratOf Y).lft
  haveI : IsLocallyNoetherian (ratOf Y).Z := LocallyOfFiniteType.isLocallyNoetherian (ratOf Y).s
  haveI : IsNoetherianRing ((ratOf Y).O y) :=
    isNoetherianRing_of_ringEquiv _ ((ratOf Y).stalkEquiv y)
  haveI : Algebra.EssFiniteType ((ratOf Y).O y) Y.Fn :=
    Algebra.EssFiniteType.of_isLocalization Y.Fn (nonZeroDivisors ((ratOf Y).O y))
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (ratOf Y).Z := fun z =>
    ⟨(Y.isNormalScheme).isDomain_stalk z, (Y.isNormalScheme).isIntegrallyClosed_stalk z⟩
  haveI := RatModel.isIntegrallyClosed_O hN y
  by_contra hn
  have hi : ¬ IsIntegral ((ratOf Y).O y) x := fun h => by
    obtain ⟨a, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    exact hn a.2
  obtain ⟨V, h1, h2, h3⟩ := GlobalTheory.exists_discreteValuationSubring_dominating_notMem hi
  exact h3 (hx V h1 h2)

end GlobalTheory.FlagBundle.Dom

namespace GlobalTheory.FlagBundle.Dom

theorem exists_pt_of_le {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (z : M.Z)
    (V : ValuationSubring Ω) (hV : LocalSubring.range (algebraMap (M.O z) Ω) ≤ V.toLocalSubring) :
    ∃ v : Sp V ⟶ M.Z, v (IsLocalRing.closedPoint V) = z ∧ spMap (algebraMap V Ω) ≫ v = M.pt ∧
      ∃ σ : IsLocalRing.ResidueField (M.Z.presheaf.stalk z) →+* IsLocalRing.ResidueField V,
        spMap (IsLocalRing.residue V) ≫ v = spMap σ ≫ spMap (IsLocalRing.residue _) ≫ M.Z.fromSpecStalk z := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.localSubring_range_le_valuationSubring_iff _ V).1 hV
  let ι : M.O z →+* V := (algebraMap (M.O z) Ω).codRestrict V h1
  haveI hι : IsLocalHom ι := ⟨fun r hr => by
    by_contra hn
    obtain ⟨_, hm⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal).1 (h2 r hn)
    exact hm hr⟩
  let g : M.Z.presheaf.stalk z →+* V := ι.comp (M.stalkEquiv z).toRingHom
  haveI : IsLocalHom g := ⟨fun a ha =>
    (isUnit_map_iff (M.stalkEquiv z) a).1 (IsLocalHom.map_nonunit (f := ι) _ ha)⟩
  refine ⟨spMap g ≫ M.Z.fromSpecStalk z, ?_, ?_, IsLocalRing.ResidueField.map g, ?_⟩
  · show M.Z.fromSpecStalk z (spMap g (IsLocalRing.closedPoint V)) = z
    rw [show spMap g (IsLocalRing.closedPoint V) = IsLocalRing.closedPoint _ from IsLocalRing.comap_closedPoint g]
    exact Scheme.fromSpecStalk_closedPoint
  · have e : (algebraMap V Ω).comp g = M.stalkHom z := rfl
    have e2 : spMap (M.stalkHom z) = spMap (Scheme.stalkClosedPointTo (R := .of Ω) M.pt).hom ≫
        Spec.map (M.Z.presheaf.stalkSpecializes (M.pt_specializes (IsLocalRing.closedPoint Ω) z)) := by
      rw [RatModel.stalkHom]
      show Spec.map _ = _
      rw [CommRingCat.ofHom_hom, Spec.map_comp]
      rfl
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
    change spMap (M.stalkHom z) ≫ _ = _
    rw [e2, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact spMap_stalkClosedPointTo M.pt
  · rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, IsLocalRing.ResidueField.map_comp_residue]

end GlobalTheory.FlagBundle.Dom

namespace GlobalTheory.FlagBundle.Dom

variable {F : Type} [Field F] {ι : Type} {m : ι → ℕ} {X Y₁ Y₂ : Var F} {Eb : Fr (ratOf X) m 0}
  {S₁ : Fr (ratOf Y₁) m m} {φ₁ : X.Fn →ₐ[F] Y₁.Fn} {S₂ : Fr (ratOf Y₂) m m} {φ₂ : X.Fn →ₐ[F] Y₂.Fn}

theorem coBear_swap {K : Type} [Field K] {x x' : Sp K ⟶ X.X} {p₁ p₁' : Sp K ⟶ Y₁.X}
    {p₂ p₂' : Sp K ⟶ Y₂.X} (hx : x = x') (hp₁ : p₁ = p₁') (hp₂ : p₂ = p₂')
    (h : CoBear Eb S₁ φ₁ S₂ φ₂ x p₁ p₂) : CoBear Eb S₂ φ₂ S₁ φ₁ x' p₂' p₁' := by
  subst hx hp₁ hp₂
  obtain ⟨A, hA, g, hg, b₁, b₂⟩ := h
  exact ⟨A, hA, g, hg, b₂, b₁⟩

end GlobalTheory.FlagBundle.Dom

namespace GlobalTheory.FlagBundle

open GlobalTheory.FlagBundle.Dom in

theorem dominates_O (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F)
    (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X)
    (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X) (h₁ : Reps Eb S₁ φ₁ f₁)
    (h₂ : Reps Eb S₂ φ₂ f₂) (ψ : Y₂.Fn →ₐ[F] Y₁.Fn) (hψ : ψ.comp φ₂ = φ₁)
    (hg : CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt (spMap ψ.toRingHom ≫ (ratOf Y₂).pt))
    (y : Y₁.X) : ∃ y' : Y₂.X, ∀ a ∈ (ratOf Y₂).O y', ψ a ∈ (ratOf Y₁).O y := by
  let κ := IsLocalRing.ResidueField (Y₁.X.presheaf.stalk y)
  let py : Sp κ ⟶ Y₁.X := spMap (IsLocalRing.residue _) ≫ Y₁.X.fromSpecStalk y
  obtain ⟨A, hA, h, hh, hb⟩ := GlobalTheory.T.exists_pointCarriesFrameFlags_own_frame F ι m X Y₁ Eb S₁ φ₁ f₁ h₁ κ py
  obtain ⟨s, ⟨hs, hsb⟩, -⟩ := h₂.2.2 κ (py ≫ f₁) A hA h hh
  refine ⟨s (IsLocalRing.closedPoint κ), fun a ha => ?_⟩
  refine mem_O_of_forall_dvr Y₁ y (ψ a) fun V _ hV => ?_
  obtain ⟨v, -, hv1, σ, hv2⟩ := exists_pt_of_le (ratOf Y₁) y V hV
  haveI : IsProper (f₂ ≫ X.str) := by
    rw [show f₂ ≫ X.str = Y₂.str from h₂.1.inducedModelMorphism_comp_structureMap]
    infer_instance
  haveI : IsProper f₂ := IsProper.of_comp f₂ X.str
  have hψ' : spMap ψ.toRingHom ≫ spMap φ₂.toRingHom = spMap φ₁.toRingHom := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hψ]
    rfl
  have hq : (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) ≫ f₂ = spMap (algebraMap V Y₁.Fn) ≫ (v ≫ f₁) := by
    have e1 : (ratOf Y₂).pt ≫ f₂ = spMap φ₂.toRingHom ≫ (ratOf X).pt := h₂.1
    have e2 : (ratOf Y₁).pt ≫ f₁ = spMap φ₁.toRingHom ≫ (ratOf X).pt := h₁.1
    erw [Category.assoc, e1, ← Category.assoc, hψ', ← e2, ← Category.assoc, hv1]
  obtain ⟨ℓ, ⟨hℓ1, hℓ2⟩, -⟩ :=
    GlobalTheory.ModelPoints.existsUnique_extension f₂ (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) (v ≫ f₁) hq
  have hinc := GlobalTheory.T.fullFlag_common_closedPoint_of_generic F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ V Y₁.Fn v ℓ hℓ1.symm
    (by erw [hℓ2, ← Category.assoc, hv1]; exact hg)
  have hbc := GlobalTheory.T.pointsCarryCommonFlag_spectrumMap_field_ext F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ h₁ h₂ κ (IsLocalRing.ResidueField V) σ
    (py ≫ f₁) py s ⟨A, hA, h, hh, hb, hsb⟩
  have hpv : spMap (IsLocalRing.residue V) ≫ v = spMap σ ≫ py := hv2
  have E1 : (spMap (IsLocalRing.residue V) ≫ ℓ) ≫ f₂ = (spMap σ ≫ py) ≫ f₁ :=
    (Category.assoc _ _ _).trans ((congrArg (spMap (IsLocalRing.residue V) ≫ ·) hℓ1).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ f₁) hpv)))
  have E2 : (spMap σ ≫ s) ≫ f₂ = (spMap σ ≫ py) ≫ f₁ :=
    (Category.assoc _ _ _).trans ((congrArg (spMap σ ≫ ·) hs).trans (Category.assoc _ _ _).symm)
  have E3 : spMap (IsLocalRing.residue V) ≫ v ≫ f₁ = (spMap (IsLocalRing.residue V) ≫ ℓ) ≫ f₂ :=
    (congrArg (spMap (IsLocalRing.residue V) ≫ ·) hℓ1.symm).trans (Category.assoc _ _ _).symm
  have E4 : spMap σ ≫ py ≫ f₁ = (spMap σ ≫ s) ≫ f₂ :=
    (congrArg (spMap σ ≫ ·) hs.symm).trans (Category.assoc _ _ _).symm
  have e : spMap (IsLocalRing.residue V) ≫ ℓ = spMap σ ≫ s :=
    GlobalTheory.T.eq_of_bear_common_fullFlag F ι m X Y₂ Y₁ Eb S₂ φ₂ f₂ S₁ φ₁ f₁ h₂ h₁ _ (spMap (IsLocalRing.residue V) ≫ ℓ)
      (spMap σ ≫ s) (spMap σ ≫ py) E1 E2 (coBear_swap E3 hpv rfl hinc) (coBear_swap E4 rfl rfl hbc)
  have hℓc : ℓ (IsLocalRing.closedPoint V) = s (IsLocalRing.closedPoint κ) := by
    have h3 : ℓ (spMap (IsLocalRing.residue V) (IsLocalRing.closedPoint (IsLocalRing.ResidueField V))) =
        s (spMap σ (IsLocalRing.closedPoint (IsLocalRing.ResidueField V))) :=
      congrArg (fun t : Sp (IsLocalRing.ResidueField V) ⟶ Y₂.X =>
        t (IsLocalRing.closedPoint (IsLocalRing.ResidueField V))) e
    have h4 : spMap (IsLocalRing.residue V) (IsLocalRing.closedPoint (IsLocalRing.ResidueField V)) =
        IsLocalRing.closedPoint V := IsLocalRing.comap_closedPoint (IsLocalRing.residue V)
    have h5 : spMap σ (IsLocalRing.closedPoint (IsLocalRing.ResidueField V)) = IsLocalRing.closedPoint κ :=
      Subsingleton.elim (α := PrimeSpectrum κ) _ _
    rw [h4, h5] at h3
    exact h3
  have hsp : ℓ (IsLocalRing.closedPoint V) ⤳ s (IsLocalRing.closedPoint κ) := hℓc ▸ specializes_rfl
  have k1 := RatModel.val_spMap_comp (M := ratOf Y₂) (algebraMap V Y₁.Fn) ℓ hsp ⟨a, ha⟩
  have k2 := RatModel.val_spMap_comp (M := ratOf Y₂) ψ.toRingHom (ratOf Y₂).pt
    ((ratOf Y₂).pt_specializes (IsLocalRing.closedPoint _) _) ⟨a, ha⟩
  have k4 := (RatModel.valLoc_eq_val (M := ratOf Y₂) (ratOf Y₂).pt
    ((ratOf Y₂).pt_specializes (IsLocalRing.closedPoint _) (s (IsLocalRing.closedPoint κ))) ⟨a, ha⟩).trans
    (RatModel.val_pt (M := ratOf Y₂) a)
  have k3 : ψ a = algebraMap V Y₁.Fn (RatModel.valLoc ℓ _ hsp ⟨a, ha⟩) := by
    calc ψ a = ψ.toRingHom (RatModel.valLoc (ratOf Y₂).pt _
          ((ratOf Y₂).pt_specializes (IsLocalRing.closedPoint _) (s (IsLocalRing.closedPoint κ))) ⟨a, ha⟩) :=
          (congrArg ψ.toRingHom k4).symm
      _ = (ratOf Y₂).val (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) a := k2.symm
      _ = (ratOf Y₂).val (spMap (algebraMap V Y₁.Fn) ≫ ℓ) a :=
          congrArg (fun t : Sp Y₁.Fn ⟶ Y₂.X => (ratOf Y₂).val t a) hℓ2.symm
      _ = _ := k1
  rw [k3]
  exact (RatModel.valLoc ℓ _ hsp ⟨a, ha⟩).2

end GlobalTheory.FlagBundle
