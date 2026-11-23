import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvrPointBoundaryCompatible
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

noncomputable section

namespace GlobalTheory.ChartCentre

open GlobalTheory.TraitChartForm in

theorem exists_equiv_formAt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Z.X)
    (tR : SAB H (Sp R)) (mR : SABMap tR Z.t ξ) (PR : PELUnif (maximalIdeal R) tR) (hCN : IsCN R) (hTor : PR.TorsionIso)
    (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (hW : CDvr W) (ϖ : W) (hϖ : Irreducible ϖ) (χ : Sp W ⟶ Z.X)
    (t : SAB H (Sp W)) (mt : SABMap t Z.t χ) (P : PELUnif (maximalIdeal W) t)
    (hr : Set.range (jK W ≫ χ) ⊆ Set.range Z.j) (be : LinearMap.BilinForm ℤ P.D.toPre.X)
    (hmon : IsMonomial P.D.toPre ![ϖ] ![be]) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (hV : CDvr V)
    (f : W →+* V) (ψ : R →+* V) (hfi : Function.Injective f) (hfl : IsLocalHom f) (hψl : IsLocalHom ψ)
    (hc : spMap f ≫ χ = spMap ψ ≫ ξ) :
    ∃ ε : PR.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X, ∀ y, ∃ (r : R) (n : ℕ), PsiCoord PR.D.toPre y r ∧
      be (ε y) (ε y) = 2 * n ∧ Associated (ψ r) (f ϖ ^ n) := by
  obtain ⟨hWd, hWc, hW0⟩ := hW
  obtain ⟨hVd, hVc, hV0⟩ := hV
  obtain ⟨hRN, hRI, hRA, hR0⟩ := hCN
  obtain ⟨L₁, L₂, L₃, L₄, L₅⟩ := GlobalTheory.firstFiveLaws

  obtain ⟨tV, ⟨mV⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap f) t
  obtain ⟨tRV, ⟨mRV⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap ψ) tR
  obtain ⟨n₀⟩ := GlobalTheory.TraitOrder.comp rfl mt mV
  obtain ⟨n₂⟩ := GlobalTheory.TraitOrder.comp rfl mR mRV
  have j : Function.Injective ((algebraMap V (FractionRing V)).comp f) := (IsFractionRing.injective V _).comp hfi
  let g : FractionRing W →+* FractionRing V := IsFractionRing.lift j
  have eg : jK V ≫ spMap f = spMap g ≫ jK W :=
    (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).symm
  obtain ⟨k₁⟩ := GlobalTheory.TraitOrder.cancel (show 𝟙 _ ≫ (spMap f ≫ χ) = spMap ψ ≫ ξ by rw [Category.id_comp, hc]) n₀ n₂

  have hpV : PolAt tV (jK V) := GlobalTheory.DatUniq.polAt_pull mV (GlobalTheory.DatUniq.polAt_of_unif P) (jK V) (spMap g) eg.symm
  have hpRV : PolAt tRV (jK V) :=
    GlobalTheory.DatUniq.polAt_pull k₁ hpV (jK V) (𝟙 _) (by rw [Category.id_comp, Category.comp_id])
  obtain ⟨B, -, gen, hg, hw, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt L₁ L₂ E H V tV hpV
  obtain ⟨BR, -, genR, hgR, hwR, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt L₁ L₂ E H V tRV hpRV

  have hχgen : χ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum W) ∈ abLocus Z.t.G := by
    let p : Sp (FractionRing W) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing W))
    obtain ⟨w, hw⟩ := hr ⟨p, rfl⟩
    rw [← jK_apply_eq_bot W p, ← Scheme.Hom.comp_apply, ← hw]
    exact j_mem_abLocus Z w
  have hfbot : spMap f (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V) = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum W) := by
    rw [← ker_eq_spMap_bot]
    exact PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot f).1 hfi)

  have hlocW : ∀ a ∈ maximalIdeal W, f a ∈ maximalIdeal V := fun a ha =>
    (mem_maximalIdeal _).2 fun h => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit f a h)
  let Ww : Set (Sp W) := abLocus t.G ∩ {p | ϖ ∉ p.asIdeal}
  have hWo : IsOpen Ww :=
    (GlobalTheory.AbLocusOpen.isOpen_abLocus_local t.G t.semi).inter (PrimeSpectrum.isOpen_basicOpen (a := ϖ))
  have hkerW : (⟨RingHom.ker f, RingHom.ker_isPrime f⟩ : PrimeSpectrum W) ∈ Ww := by
    rw [ker_eq_spMap_bot, hfbot]
    refine ⟨(abLocus_pullback abLocusOne Z.t.semi mt.cart.1 _).1 hχgen, fun h => hϖ.ne_zero ((Submodule.mem_bot W).1 h)⟩
  have hψW : ∀ y, PsiUnitOn P.D.toPre y Ww := fun y => hmon.psiUnitOn y fun p hp => by simpa using hp.2
  obtain ⟨PV, e₁, he₁⟩ := GlobalTheory.PelCoordPull.exists_pelUnif_psiCoord E H W V f t tV mV P Ww inferInstance inferInstance
    hWc inferInstance inferInstance hVc hlocW hWo Set.inter_subset_left hψW hkerW ⟨B, gen, hg, hw⟩

  have hlocR : ∀ a ∈ maximalIdeal R, ψ a ∈ maximalIdeal V := fun a ha =>
    (mem_maximalIdeal _).2 fun h => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit ψ a h)
  have hRo : IsOpen (abLocus tR.G) := GlobalTheory.AbLocusOpen.isOpen_abLocus_local tR.G tR.semi
  have hAdm : admitted R (maximalIdeal R) := ⟨⟨hRN, inferInstance, hRI, hRA⟩, hRA, hR0, inferInstance,
    by letI := Ideal.Quotient.field (maximalIdeal R); infer_instance⟩
  have hψR : ∀ y, PsiUnitOn PR.D.toPre y (abLocus tR.G) :=
    GlobalTheory.psiUnitOn_abLocus_pel L₁ L₂ L₃ L₄ L₅ E H R (maximalIdeal R) hAdm tR PR hTor hRo
  have hrV : Set.range (jK V ≫ spMap ψ ≫ ξ) ⊆ Set.range Z.j := by
    rw [← hc, ← Category.assoc, eg, Category.assoc]
    rintro _ ⟨p, rfl⟩
    exact hr ⟨spMap g p, by rw [Scheme.Hom.comp_apply (spMap g)]⟩
  have hkerR : (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum R) ∈ abLocus tR.G := by
    rw [ker_eq_spMap_bot]
    refine (abLocus_pullback abLocusOne Z.t.semi mR.cart.1 _).1 ?_
    let p : Sp (FractionRing V) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))
    obtain ⟨w, hw⟩ := hrV ⟨p, rfl⟩
    have key : ξ (spMap ψ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V)) = (jK V ≫ spMap ψ ≫ ξ) p := by
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, jK_apply_eq_bot V p]
    rw [key, ← hw]
    exact j_mem_abLocus Z w
  obtain ⟨PRV, e₂, he₂⟩ := GlobalTheory.PelCoordPull.exists_pelUnif_psiCoord E H R V ψ tR tRV mRV PR (abLocus tR.G) hRN hRI
    hRA inferInstance inferInstance hVc hlocR hRo subset_rfl hψR hkerR ⟨BR, genR, hgR, hwR⟩

  obtain ⟨e₃, he₃⟩ := GlobalTheory.SameCoord.exists_equiv_psiCoord E H V tV tRV k₁ PV PRV inferInstance inferInstance hVc
  refine ⟨(e₂.trans e₃.symm).trans e₁.symm, fun y => ?_⟩
  obtain ⟨r, hr⟩ := (GlobalTheory.PeriodFormCompare.exists_psiCoord_iff PR.D.toPre y).2
    (GlobalTheory.PeriodFormCompare.psiIn_top PR.D y)
  set x := ((e₂.trans e₃.symm).trans e₁.symm) y with hx
  have hx2 : e₃ (e₁ x) = e₂ y := by simp [hx]
  obtain ⟨u₀, nW, hnW, hcW⟩ := hmon x
  obtain ⟨u₁, h₁⟩ := he₁ x _ hcW
  obtain ⟨u₃, h₃⟩ := he₃ _ _ h₁
  obtain ⟨u₂, h₂⟩ := he₂ y r hr
  rw [hx2] at h₃
  obtain ⟨w, hw⟩ := GlobalTheory.PsiCoordLocal.exists_unit_of_coord h₃ h₂
  have key : ψ r = ((u₂⁻¹ * w * u₃ * u₁ * Units.map f.toMonoidHom u₀ : Vˣ) : V) * f ϖ ^ nW 0 := by
    have e := congrArg (fun z => ((u₂⁻¹ : Vˣ) : V) * z) hw
    simp only [Fin.prod_univ_one, Matrix.cons_val_zero, map_mul, map_pow] at e
    rw [← mul_assoc, Units.inv_mul, one_mul] at e
    rw [e]
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
    ring
  refine ⟨r, nW 0, hr, by simpa using hnW 0, ?_⟩
  exact Associated.symm (⟨_, by rw [key, mul_comm]⟩ : Associated (f ϖ ^ nW 0) (ψ r))

theorem isLocalHom_stalkSpecializes {X : Scheme.{0}} {x y : X} (h : x ⤳ y) (e : x = y) :
    IsLocalHom (X.presheaf.stalkSpecializes h).hom := by
  subst e
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  exact ⟨fun _ h => h⟩

theorem spMap_comp_eq {X : Scheme.{0}} {R W V : Type} [CommRing R] [IsLocalRing R] [CommRing W] [IsLocalRing W]
    [CommRing V] (ξ : Sp R ⟶ X) (χ : Sp W ⟶ X) (hs : χ (closedPoint W) ⤳ ξ (closedPoint R)) (ι : W →+* V) (g : R →+* V)
    (h : ∀ a, g ((Scheme.stalkClosedPointTo ξ).hom a) =
      ι ((Scheme.stalkClosedPointTo χ).hom ((X.presheaf.stalkSpecializes hs).hom a))) :
    spMap ι ≫ χ = spMap g ≫ ξ := by
  have e : X.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo χ ≫ CommRingCat.ofHom ι =
      Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom g := by
    ext a
    exact (h a).symm
  have e₁ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk χ
  have e₂ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have e₃ := Scheme.SpecMap_stalkSpecializes_fromSpecStalk hs
  calc spMap ι ≫ χ = Spec.map (CommRingCat.ofHom ι) ≫ Spec.map (Scheme.stalkClosedPointTo χ) ≫
        Spec.map (X.presheaf.stalkSpecializes hs) ≫ X.fromSpecStalk _ := by rw [e₃, e₁]
    _ = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (Scheme.stalkClosedPointTo ξ) ≫ X.fromSpecStalk _ := by
        rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, e]
    _ = spMap g ≫ ξ := by rw [e₂]

theorem exists_surjective_formAt : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Z.X) (t : SAB H (Sp R)) (_ : SABMap t Z.t ξ) (P : PELUnif (maximalIdeal R) t), IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → P.TorsionIso → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ → ∀ (χ : Sp W ⟶ Z.X) (tW : SAB H (Sp W)) (_ : SABMap tW Z.t χ) (PW : PELUnif (maximalIdeal W) tW), Set.range (jK W ≫ χ) ⊆ Set.range Z.j → ∀ be ∈ levelForms H 1 PW.D.toPre.X, IsMonomial PW.D.toPre ![ϖ] ![be] → ∀ hs : χ (closedPoint W) ⤳ ξ (closedPoint R), χ (closedPoint W) = ξ (closedPoint R) → ∀ (W' : Type) [CommRing W'] [IsDomain W'] [IsLocalRing W'] (ι : W →+* W') (g : R →+* W'), CDvr W' → Irreducible (ι ϖ) → (∀ a, g ((Scheme.stalkClosedPointTo ξ).hom a) = ι ((Scheme.stalkClosedPointTo χ).hom ((Z.X.presheaf.stalkSpecializes hs).hom a))) → ∃ (e : P.D.toPre.X →ₗ[𝓞 E] PW.D.toPre.X), Function.Surjective e ∧ FormAt P.D.toPre g (ι ϖ) (be.compl₁₂ e.toAddMonoidHom.toIntLinearMap e.toAddMonoidHom.toIntLinearMap) := by
  intro E _ _ _ H D l Xo c Z R _ _ _ ξ t m P hR hE _ hT W _ _ _ hW ϖ hϖ χ tW mW PW hχ be _ hmon hs hx W' _ _ _ ι g hW'
    hι hg
  have hd : IsDiscreteValuationRing W := hW.1
  have hloc : IsLocalHom ι := ⟨fun a ha => by
    by_contra hn
    have hm : a ∈ maximalIdeal W := hn
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
    exact hι.not_isUnit (isUnit_of_dvd_unit (map_dvd ι hm) ha)⟩
  have hinj : Function.Injective ι := by
    refine (injective_iff_map_eq_zero ι).2 fun a ha => by_contra fun hn => ?_
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hn hϖ
    rw [map_mul, map_pow] at ha
    exact mul_ne_zero (u.isUnit.map ι).ne_zero (pow_ne_zero n hι.ne_zero) ha
  have hsl := isLocalHom_stalkSpecializes hs hx
  have hgl : IsLocalHom g := by
    have hle : maximalIdeal R ≤ (maximalIdeal W').comap g := by
      rw [← hE.2.1, Ideal.map_le_iff_le_comap]
      intro a ha hu
      rw [hg] at hu
      exact ha (isUnit_of_map_unit _ _ (isUnit_of_map_unit _ _ (isUnit_of_map_unit ι _ hu)))
    exact ⟨fun a ha => by_contra fun hn => hle hn ha⟩
  obtain ⟨e, he⟩ := exists_equiv_formAt Z ξ t m P hR hT W hW ϖ hϖ χ tW mW PW hχ be hmon W' hW' ι g hinj hloc hgl
    (spMap_comp_eq ξ χ hs ι g hg)
  exact ⟨e.toLinearMap, e.surjective, he⟩

end GlobalTheory.ChartCentre
