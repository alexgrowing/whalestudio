import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAbelianLocus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelFamilyProperExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelPullbackDvrExtensionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompleteUnramifiedResidueLiftStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteLocalDomainCoverStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SemiabelianTorusAfterSeparableStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnAbelianLocusUniformisation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmplePointsLocalizedModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeConditionsCoverModels
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalNormalPrime
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfProperGenericTorusExtensionSpecialFiber
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNZOfPolAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelObjectDescendsFgSubfield
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EgaHolds
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationLinearAndTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTotalClosed

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegChart

theorem dvd_of_map_dvd {A A₁ : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing A₁] [IsDomain A₁]
    (ι : A →+* A₁) (hi : Function.Injective ι) (hf : ι.Finite) {a b : A} (h : ι a ∣ ι b) : a ∣ b := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [map_zero, zero_dvd_iff, ← map_zero ι] at h
    rw [hi h]
  obtain ⟨u, hu⟩ := h
  letI := ι.toAlgebra
  have : Module.Finite A A₁ := hf
  have hu' : IsIntegral A u := Algebra.IsIntegral.isIntegral u
  have j : Function.Injective ((algebraMap A₁ (FractionRing A₁)).comp ι) := (IsFractionRing.injective A₁ _).comp hi
  let g : FractionRing A →ₐ[A] FractionRing A₁ :=
    { IsFractionRing.lift j with commutes' := fun x => IsFractionRing.lift_algebraMap j x }
  have ha' : algebraMap A (FractionRing A) a ≠ 0 := by simpa using ha
  have e : g (algebraMap A _ b / algebraMap A _ a) = algebraMap A₁ (FractionRing A₁) u := by
    have h0 : algebraMap A₁ (FractionRing A₁) (ι a) ≠ 0 := fun h => ha (j (h.trans (map_zero _).symm))
    rw [map_div₀, g.commutes, g.commutes, div_eq_iff (show algebraMap A (FractionRing A₁) a ≠ 0 from h0)]
    show algebraMap A₁ _ (ι b) = _ * algebraMap A₁ _ (ι a)
    rw [hu, map_mul, mul_comm]
  have hint : IsIntegral A (algebraMap A (FractionRing A) b / algebraMap A _ a) := by
    rw [← isIntegral_algHom_iff g g.toRingHom.injective, e]
    exact hu'.algebraMap
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  refine ⟨w, IsFractionRing.injective A (FractionRing A) ?_⟩
  rw [map_mul, hw, mul_div_cancel₀ _ ha']

theorem injective_of_flat_local {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] (f : A →+* B)
    (hf : f.Flat) (hl : IsLocalHom f) : Function.Injective f := by
  algebraize [f]
  have : IsLocalHom (algebraMap A B) := hl
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := A) (B := B)
  exact FaithfulSMul.algebraMap_injective A B

theorem isAdmissibleBase_of_completeNormalLocalCharZero {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] (hA : IsCN A) : LN.admitted A (maximalIdeal A) :=
  ⟨admissibleBase_of_completeNormalLocalCharZero hA, hA.2.2.1, hA.2.2.2, inferInstance, inferInstanceAs (IsIntegrallyClosed (ResidueField A))⟩

theorem exists_open {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {F : SFam g n ζ} {S : Scheme.{0}} {j : F.X ⟶ S}
    {G : Over S} [GrpObj G] {e : F.univ.A.left ⟶ G.left} (hG : IsSemiAbelian G) (hab : abLocus G = Set.range j)
    {R V : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] (hR : IsCN R) (ψ : R →+* V)
    {ξ : Sp R ⟶ S} {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {π : G'.left ⟶ G.left}
    {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))} {U : Unif (maximalIdeal R) D A G'}
    (hU : IsUnifOf F j e ξ π U) (hr : Set.range (jK V ≫ spMap ψ ≫ ξ) ⊆ Set.range j) :
    ∃ W : Set (Sp R), IsOpen W ∧ (∀ y, PsiUnitOn D.toPre y W) ∧
      (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum R) ∈ W := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := GlobalTheory.allSixLaws
  have hG' := TraitOrd.isSemiAbelian_of_isGrpPullback hU.1 hG
  have := hR.1
  have ho := GlobalTheory.AbLocusOpenGlobal.isOpen_abLocus_of_locallyNoetherian G' hG'
  refine ⟨abLocus G', ho, GlobalTheory.PsiAbelian.psiUnitOn_abLocus h1 h2 h3 h4 h5 R _ (isAdmissibleBase_of_completeNormalLocalCharZero hR) D A G' hG' U ho,
    (abLocus_pullback abLocusOne hG hU.1.1 _).1 (hab ▸ hr ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V)), ?_⟩)⟩
  exact congrArg (spMap ψ ≫ ξ) (GlobalTheory.TraitChartForm.jK_apply_eq_bot V _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l}

theorem charZero_essFiniteType_stalk {R : Type} [CommRing R] (a : 𝓞 c.F) (b : 𝓞 c.F →+* R) {ω : R →+* c.F}
    (hω : IsDedFrac ω) (hloc : @IsLocalization.Away (𝓞 c.F) _ a R _ b.toAlgebra) (C : Model Xo c ω) (z : C.X) :
    CharZero (C.X.presheaf.stalk z) ∧ Algebra.EssFiniteType ℤ (C.X.presheaf.stalk z) := by
  haveI := c.fin
  haveI : NumberField c.F := {}
  obtain ⟨⟨_, -⟩, _, -⟩ := hω
  haveI := GlobalTheory.ThetaDescent.isProper_of_isProjOver C.proj
  haveI : Flat C.s := C.flat
  let y : PrimeSpectrum R := C.s z
  letI : Algebra R ((Sp R).presheaf.stalk (C.s z)) := StructureSheaf.stalkAlgebra _ y
  haveI : IsLocalization.AtPrime ((Sp R).presheaf.stalk (C.s z)) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk _ y
  let φ := algebraMap R ((Sp R).presheaf.stalk (C.s z))
  have h₁ : (C.s.stalkMap z).hom.EssFiniteType := LocallyOfFiniteType.stalkMap C.s z
  have h₂ : φ.EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ y.asIdeal.primeCompl)
  have hφ : Function.Injective φ :=
    IsLocalization.injective ((Sp R).presheaf.stalk (C.s z)) y.asIdeal.primeCompl_le_nonZeroDivisors
  have hσ : Function.Injective (C.s.stalkMap z).hom :=
    injective_of_flat_local _ (Flat.stalkMap C.s z) (C.s.toLRSHom.prop z)
  refine ⟨charZero_of_injective_ringHom (f := (C.s.stalkMap z).hom.comp φ) (hσ.comp hφ), ?_⟩
  have hO : Algebra.EssFiniteType ℤ (𝓞 c.F) := inferInstance
  have hb : b.EssFiniteType := by
    letI := b.toAlgebra
    exact RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ (Submonoid.powers a))
  refine RingHom.essFiniteType_algebraMap.1 ?_
  convert (RingHom.essFiniteType_algebraMap.2 hO).comp (hb.comp (h₂.comp h₁)) using 1
  exact Subsingleton.elim _ _

theorem specMap_stalkCongr_fromSpecStalk {X : Scheme.{0}} {x y : X} (h : x = y) :
    Spec.map (X.presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫ X.fromSpecStalk x = X.fromSpecStalk y := by
  subst h
  simp

theorem exists_split_chart {R : Type} [CommRing R] (a : 𝓞 c.F) (b : 𝓞 c.F →+* R) {ω : R →+* c.F}
    (hω : IsDedFrac ω) (hloc : @IsLocalization.Away (𝓞 c.F) _ a R _ b.toAlgebra) (C : Model Xo c ω) {S : Scheme.{0}}
    (π : C.X ⟶ S) (z : C.X) {R₀ : Type} [CommRing R₀] [IsLocalRing R₀] (ξ₀ : Sp R₀ ⟶ S)
    (hc : IsAdicComplete (maximalIdeal R₀) R₀) (hpt : ξ₀ (closedPoint R₀) = π z)
    (het : IsEtaleCompletion (Scheme.stalkClosedPointTo ξ₀).hom)
    (hfu : ((residue R₀).comp (Scheme.stalkClosedPointTo ξ₀).hom).FormallyUnramified) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsLocalRing A) (ξ : Sp A ⟶ C.X) (φ : R₀ →+* A)
      (t : SAB H (Sp A)) (_ : SABMap t C.t ξ), IsCN A ∧ ξ (closedPoint A) = z ∧
      IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧
      ((residue A).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified ∧ IsLocalHom φ ∧
      ξ ≫ π = spMap φ ≫ ξ₀ ∧ LN.SplitOver t.G (maximalIdeal A) := by
  haveI := (C.normal z).1
  haveI := (C.normal z).2
  obtain ⟨hcz, hez⟩ := charZero_essFiniteType_stalk a b hω hloc C z
  let e := S.presheaf.stalkCongr (Inseparable.of_eq hpt)
  let f : S.presheaf.stalk (ξ₀ (closedPoint R₀)) →+* C.X.presheaf.stalk z := (π.stalkMap z).hom.comp e.hom.hom
  have hfl : IsLocalHom f := inferInstance
  let x₀ : Sp (ResidueField (C.X.presheaf.stalk z)) ⟶ C.X := spMap (residue _) ≫ C.X.fromSpecStalk z
  obtain ⟨k', _, _, hk, hsep, hT⟩ := GlobalTheory.T.semiabelian_torus_after_separable _ ((Over.pullback x₀).obj C.t.G) (IsSemiAbelian.pullback _ _ C.t.semi)
  obtain ⟨A, _, _, _, ψ, φ, τ, hA, hψl, het', hfu', hφl, hcomm, hτ⟩ :=
    GlobalTheory.T.complete_unramified_residue_lift _ _ R₀ k' f (Scheme.stalkClosedPointTo ξ₀).hom (algebraMap _ k') hc hfl inferInstance het hfu
      (RingHom.finite_algebraMap.2 hk)
      (RingHom.formallyUnramified_algebraMap.2 (Algebra.FormallyUnramified.of_isSeparable _ _))
  haveI := hψl
  let ψc : C.X.presheaf.stalk z ⟶ CommRingCat.of A := CommRingCat.ofHom ψ
  haveI : IsLocalHom ψc.hom := hψl
  let ξ : Sp A ⟶ C.X := (SpecToEquivOfLocalRing C.X (CommRingCat.of A)).symm ⟨z, ⟨ψc, inferInstance⟩⟩
  have hsym := (SpecToEquivOfLocalRing C.X (CommRingCat.of A)).apply_symm_apply ⟨z, ⟨ψc, inferInstance⟩⟩
  rw [SpecToEquivOfLocalRing_eq_iff] at hsym
  obtain ⟨h1, h2⟩ := hsym
  have h2' : (Scheme.stalkClosedPointTo ξ).hom = ψ.comp (C.X.presheaf.stalkCongr (Inseparable.of_eq h1)).hom.hom :=
    congrArg (fun q => q.hom) h2
  obtain ⟨t, ⟨m⟩⟩ : ∃ t : SAB H (Sp A), Nonempty (SABMap t C.t ξ) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull ξ C.t
    exact ⟨_, ⟨m⟩⟩
  refine ⟨A, inferInstance, inferInstance, inferInstance, ξ, φ, t, m, hA, h1, ?_, ?_, hφl, ?_, ?_⟩
  · rw [h2']
    exact isEtaleCompletion_comp_bij _ (ConcreteCategory.bijective_of_isIso _) ψ het'
  · rw [h2']
    have hsurj : Function.Surjective (C.X.presheaf.stalkCongr (Inseparable.of_eq h1)).hom.hom :=
      (ConcreteCategory.bijective_of_isIso _).2
    have h3 := RingHom.FormallyUnramified.comp (RingHom.FormallyUnramified.of_surjective hsurj) hfu'
    exact h3
  · have hcomm' : Scheme.stalkClosedPointTo ξ₀ ≫ CommRingCat.ofHom φ = e.hom ≫ π.stalkMap z ≫ ψc := by
      ext a
      exact (congrArg (fun q : _ →+* A => q a) hcomm).symm
    calc ξ ≫ π = Spec.map ψc ≫ C.X.fromSpecStalk z ≫ π := by
          simp only [ξ, SpecToEquivOfLocalRing_symm_apply, Category.assoc]
      _ = Spec.map ψc ≫ Spec.map (π.stalkMap z) ≫ S.fromSpecStalk (π z) := by
          rw [Scheme.SpecMap_stalkMap_fromSpecStalk]
      _ = Spec.map ψc ≫ Spec.map (π.stalkMap z) ≫ Spec.map e.hom ≫ S.fromSpecStalk (ξ₀ (closedPoint R₀)) := by
          rw [specMap_stalkCongr_fromSpecStalk hpt]
      _ = Spec.map (e.hom ≫ π.stalkMap z ≫ ψc) ≫ S.fromSpecStalk (ξ₀ (closedPoint R₀)) := by
          simp only [Spec.map_comp, Category.assoc]
      _ = Spec.map (Scheme.stalkClosedPointTo ξ₀ ≫ CommRingCat.ofHom φ) ≫ S.fromSpecStalk (ξ₀ (closedPoint R₀)) := by
          rw [hcomm']
      _ = spMap φ ≫ ξ₀ := by
          rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  · obtain ⟨T'⟩ := GlobalTheory.SS.nonempty_torusExtension_pullback (spMap τ) _ hT
    have hx : spMap τ ≫ spMap (algebraMap _ k') ≫ x₀ = spMap (residue A) ≫ ξ := by
      have e₁ : ξ = spMap ψ ≫ C.X.fromSpecStalk z := rfl
      rw [e₁, ← Category.assoc, ← Category.assoc, ← Category.assoc, DomFine.spMap_comp', DomFine.spMap_comp',
        DomFine.spMap_comp', ← hτ, RingHom.comp_assoc]
    obtain ⟨i, hi, -⟩ := grpPullback_iso
      (((isGrpPullback_pullback _ (spMap τ)).comp ((isGrpPullback_pullback _ (spMap (algebraMap _ k'))).comp
        (isGrpPullback_pullback C.t.G x₀))).congr hx rfl)
      ((isGrpPullback_pullback t.G (spMap (residue A))).comp m.cart)
    exact exists_splitExt_isGt_of_torusExtension _ _ ⟨torusExtOfIso i T'⟩

theorem exists_local_cone : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (n : ℕ) (R : Type) [CommRing R] (b : 𝓞 c.F →+* R) (ω : R →+* c.F) (φ : InvFun ℤ) (F : SFam (Module.finrank ℚ E / 2 * (D.p + D.q)) n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) (j : F.X ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left) (BD : EffCartierData S) (d N : ℕ) (κ : cycAway n →+* R) (C : Model Xo c ω) (π : C.X ⟶ S), 1 ≤ D.p + D.q → 3 ≤ n → Odd n → n ∣ l.M → IsPolFan id (Module.finrank ℚ E / 2 * (D.p + D.q)) φ → IsDedFrac ω → ω.comp b = algebraMap (𝓞 c.F) c.F → @IsLocalization.Away (𝓞 c.F) _ (n : 𝓞 c.F) R _ b.toAlgebra → SiegData (Module.finrank ℚ E / 2 * (D.p + D.q)) φ n F S s j G e BD d N → (∀ x, ((ω (κ x) : c.F) : ℂ) = (x : ℂ)) → IsSiegPull s j G e κ C π → ∀ z : C.X,
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsLocalRing A) (ξ : Sp A ⟶ C.X) (t : SAB H (Sp A))
      (_ : SABMap t C.t ξ) (P : PELUnif (maximalIdeal A) t) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X)
      (τ : Fin m → A) (k : ℕ),
      IsCN A ∧ ξ (closedPoint A) = z ∧ IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧
      ((residue A).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified ∧ P.TorsionIso ∧
      Module.Free ℤ P.D.toPre.X ∧ Module.finrank ℤ P.D.toPre.X ≤ (Module.finrank ℚ E / 2 * (D.p + D.q)) ∧ IsCone id φ γ ∧
      ∀ y, ∃ (r : A) (u : Aˣ), PsiCoord P.D.toPre y r ∧ r ^ 2 = u * ∏ i, τ i ^ (k * (γ i y y).toNat) := by
  intro E _ _ _ H D l Xo c n R _ b ω φ F S s j _ G _ e BD d N κ C π _ _ _ _ _ hω _ hloc hS _ hpull z
  obtain ⟨-, -, -, -, hG, hGs, hGe, hab, -, hch, -⟩ := hS
  obtain ⟨R₀, _, _, b₀, ξ₀, m, t₀, R', _, _, _, ρ, r, G', _, _, π', D', A', U', γ, a, ⟨hc, -, hpt, het, hfu⟩, -,
    ⟨hR', hz', hρi, hρf, -, hr⟩, ⟨hU', hX, hγ, hmon⟩, -⟩ := hch (π z)
  obtain ⟨A, _, _, _, ξ, ψ, t, mt, hA, hξ, hetA, hfuA, hψ, hcomm, hsplit⟩ :=
    exists_split_chart (n : 𝓞 c.F) b hω hloc C π z ξ₀ hc hpt het hfu
  obtain ⟨y, hy⟩ : ∃ y : Sp (FractionRing A) ⟶ Xo.XF c, y ≫ C.j = jK A ≫ ξ := by
    obtain ⟨⟨_, _⟩, -, hfr⟩ := hω
    letI := ω.toAlgebra
    exact DomFine.exists_generic_point R c.F C.X (Xo.XF c) C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense ξ hetA.1
  have hadm := isAdmissibleBase_of_completeNormalLocalCharZero hA
  have hpol := GlobalTheory.Ex.UnifModel.polAt_of_point C (jK A) ξ y hy.symm t mt
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := GlobalTheory.allSixLaws
  obtain ⟨P, hP⟩ := GlobalTheory.LN.UnifPrime.exists_pelUnif h1 h2 h3 h4 h5 GlobalTheory.LN.ega_holds GlobalTheory.uniformisation_total_closed
    GlobalTheory.uniformisation_linear_and_torsion E H A _ hadm (inferInstanceAs (IsPrincipalIdealRing (ResidueField A))) t hpol
    hsplit (GlobalTheory.ThetaNormal.thetaNZ_of_polAt E H A hadm t hpol hsplit)
  obtain ⟨A₁, _, _, _, ι, σ, hA₁, hιi, hιf, hιl, hσl, hσ⟩ := GlobalTheory.T.exists_finite_local_domain_cover R₀ A R' ψ ρ hA hψ hρi hρf
  have hR'' : IsCN R' := ⟨hR'.1, hR'.2.2.1, hR'.2.2.2, hz'⟩
  obtain ⟨μ, hμ⟩ := GlobalTheory.T.siegel_pullback_dvr_extension E H D l Xo c _ n R ω F S s j G e κ C π hω hpull A _ ξ t mt P
    (by rw [← hy]; rintro _ ⟨p, rfl⟩; exact ⟨y p, rfl⟩)
  have hξ₁ : spMap ι ≫ ξ ≫ π = spMap σ ≫ spMap ρ ≫ ξ₀ := by
    rw [hcomm, ← Category.assoc, ← Category.assoc, DomFine.spMap_comp', DomFine.spMap_comp', hσ]
  have ji : Function.Injective ((algebraMap A₁ (FractionRing A₁)).comp ι) := (IsFractionRing.injective A₁ _).comp hιi
  have hr₁ : Set.range (jK A₁ ≫ spMap ι ≫ ξ ≫ π) ⊆ Set.range j := by
    obtain ⟨-, y₁, -, -, hy₁, -⟩ := hμ
    have e₁ : jK A₁ ≫ spMap ι = spMap (IsFractionRing.lift ji : FractionRing A →+* FractionRing A₁) ≫ jK A :=
      (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).trans
        (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap ji)).symm
    rw [← Category.assoc, e₁, Category.assoc, ← hy₁, ← Category.assoc]
    rintro _ ⟨p, rfl⟩
    exact ⟨_, (Scheme.Hom.comp_apply _ _ p).symm⟩
  obtain ⟨W₁, o₁, u₁, k₁⟩ := exists_open hG hab hA ι hμ hr₁
  obtain ⟨W₂, o₂, u₂, k₂⟩ := exists_open hG hab hR'' σ hU' (hξ₁ ▸ hr₁)
  obtain ⟨ε₀, hε⟩ := TraitOrd.exists_compare hG hGe hA hR'' hA₁ ι hιl σ hσl hμ W₁ o₁ u₁ k₁ hU' W₂ o₂ u₂ k₂ hξ₁ hr₁
  let ε : P.D.toPre.X ≃ₗ[ℤ] D'.toPre.X := ε₀.toIntLinearEquiv
  refine ⟨A, inferInstance, inferInstance, inferInstance, ξ, t, mt, P, m, fun i => pull ε.toLinearMap (γ i),
    fun i => ψ (t₀ i), n, hA, hξ, hetA, hfuA, hP, inferInstance, ε.finrank_eq.trans_le hX, hγ.pull_equiv ε, fun x => ?_⟩
  have := hA.2.2.2
  have := hA.2.1
  obtain ⟨q, hq, -⟩ := (PsiCoordLocal.main A P.D hA.2.1 x).1
  obtain ⟨v, k, hk, hv⟩ := hmon (ε x)
  have h₀ := hε x _ _ hq hv
  have hk' : ∀ i, k i = n * (γ i (ε x) (ε x)).toNat := fun i => by
    have h₁ := hk i
    have h₂ := Int.toNat_of_nonneg (hγ.nonneg i (ε x))
    simp only [LinearMap.smul_apply, smul_eq_mul] at h₁
    have : (k i : ℤ) = n * ((γ i (ε x) (ε x)).toNat : ℤ) := by rw [h₂]; linarith
    exact_mod_cast this
  have hs : σ (∏ i, r i ^ k i) ^ 2 = ι (∏ i, ψ (t₀ i) ^ (n * (γ i (ε x) (ε x)).toNat)) := by
    rw [map_prod, map_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, map_pow, ← pow_mul, mul_comm, pow_mul, ← map_pow, hr, hk']
    exact congrArg (· ^ _) (RingHom.congr_fun hσ (t₀ i))
  have h₃ : Associated (ι (q ^ 2)) (ι (∏ i, ψ (t₀ i) ^ (n * (γ i (ε x) (ε x)).toNat))) := by
    rw [← hs, map_pow]
    refine h₀.trans (Associated.pow_pow ?_)
    rw [map_mul]
    exact associated_unit_mul_left _ _ (v.isUnit.map σ)
  obtain ⟨u, hu⟩ := associated_of_dvd_dvd (dvd_of_map_dvd ι hιi hιf h₃.symm.dvd) (dvd_of_map_dvd ι hιi hιf h₃.dvd)
  exact ⟨q, u, hq, by rw [mul_comm]; exact hu.symm⟩

end GlobalTheory.SiegChart
