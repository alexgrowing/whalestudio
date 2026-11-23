import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkCharZeroEssFiniteType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericFiberNormalReduced
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section
namespace GlobalTheory.FibreChart

open scoped TensorProduct

theorem chart : ∀ (X G : Scheme.{0}) (U : X.Opens) (hU : IsAffineOpen U) (W : G.Opens) (hW : IsAffineOpen W)
    (R : Type) [CommRing R] [Algebra Γ(X, U) R] [Algebra Γ(X, U) Γ(G, W)] (g : G ⟶ X),
    hW.fromSpec ≫ g = Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) Γ(G, W))) ≫ hU.fromSpec →
    ∀ (ξ : Sp R ⟶ X), ξ = Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) R)) ≫ hU.fromSpec →
    ∀ v : ↥(pullback ξ g), pullback.snd ξ g v ∈ W →
    ∃ ι : Sp (R ⊗[Γ(X, U)] Γ(G, W)) ⟶ pullback ξ g, IsOpenImmersion ι ∧ v ∈ Set.range ι := by
  intro X G U hU W hW R _ _ _ g hWg ξ hξ v hv
  subst hξ
  let aR := Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) R))
  let aW := Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) Γ(G, W)))
  let m := pullback.map aR aW (aR ≫ hU.fromSpec) g (𝟙 _) hW.fromSpec hU.fromSpec (by simp) hWg.symm
  haveI : IsOpenImmersion m := inferInstance
  refine ⟨(pullbackSpecIso Γ(X, U) R Γ(G, W)).inv ≫ m, inferInstance, ?_⟩
  have hv' : v ∈ Set.range (pullback.fst (pullback.snd (aR ≫ hU.fromSpec) g) hW.fromSpec) := by
    rw [IsOpenImmersion.range_pullbackFst]
    change (pullback.snd (aR ≫ hU.fromSpec) g) v ∈ hW.fromSpec.opensRange
    rw [hW.opensRange_fromSpec]
    exact hv
  obtain ⟨q, hq⟩ := hv'
  have e1 := pullback.condition (f := aR ≫ hU.fromSpec) (g := g)
  have e2 := pullback.condition (f := pullback.snd (aR ≫ hU.fromSpec) g) (g := hW.fromSpec)
  have hc : (pullback.fst (pullback.snd (aR ≫ hU.fromSpec) g) hW.fromSpec ≫ pullback.fst _ _) ≫ aR =
      pullback.snd (pullback.snd (aR ≫ hU.fromSpec) g) hW.fromSpec ≫ aW := by
    rw [← cancel_mono hU.fromSpec]
    calc _ = pullback.fst _ _ ≫ (pullback.fst _ _ ≫ aR ≫ hU.fromSpec) := by simp
      _ = pullback.fst _ _ ≫ pullback.snd _ _ ≫ g := by rw [e1]
      _ = (pullback.fst _ _ ≫ pullback.snd _ _) ≫ g := by simp
      _ = (pullback.snd _ _ ≫ hW.fromSpec) ≫ g := by rw [e2]
      _ = _ := by rw [Category.assoc, hWg]; rfl
  let ℓ := pullback.lift _ _ hc
  have hℓ : ℓ ≫ m = pullback.fst _ _ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, ℓ, m, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id]
    · simp only [Category.assoc, ℓ, m, pullback.map, pullback.lift_snd, pullback.lift_snd_assoc]
      exact e2.symm
  refine ⟨(pullbackSpecIso Γ(X, U) R Γ(G, W)).hom (ℓ q), ?_⟩
  rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc, ← Scheme.Hom.comp_apply, hℓ, hq]

theorem factor : ∀ (X : Scheme.{0}) (R : Type) [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ X) (U : X.Opens)
    (hU : IsAffineOpen U) (hx : ξ (IsLocalRing.closedPoint (CommRingCat.of R)) ∈ U),
    ξ = Spec.map (ξ.appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem ξ hx).ge ≫
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom) ≫ hU.fromSpec := by
  intro X R _ _ ξ U hU hx
  have h := IsAffineOpen.SpecMap_appLE_fromSpec ξ hU (isAffineOpen_top (Sp R))
    (Scheme.preimage_eq_top_of_closedPoint_mem ξ hx).ge
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]

theorem locnorm : ∀ (S : Scheme.{0}), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (W : S.Opens), IsAffineOpen W →
    ∀ (M : Submonoid Γ(S, W)) (C : Type) [CommRing C] [Algebra Γ(S, W) C] [IsLocalization M C]
    (Q : Ideal C) [Q.IsPrime], IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  intro S hS W hW M C _ _ _ Q _
  haveI hP : (Q.comap (algebraMap Γ(S, W) C)).IsPrime := Ideal.comap_isPrime _ _
  haveI : IsLocalization.AtPrime (Localization.AtPrime Q) (Q.comap (algebraMap Γ(S, W) C)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M (Localization.AtPrime Q) Q
  let y : PrimeSpectrum Γ(S, W) := ⟨Q.comap (algebraMap Γ(S, W) C), hP⟩
  have hy : hW.fromSpec y ∈ W := by
    have h0 : hW.fromSpec y ∈ Set.range hW.fromSpec := ⟨y, rfl⟩
    rwa [hW.range_fromSpec] at h0
  letI := TopCat.Presheaf.algebra_section_stalk S.presheaf ⟨hW.fromSpec y, hy⟩
  haveI : IsLocalization.AtPrime (S.presheaf.stalk (hW.fromSpec y)) (Q.comap (algebraMap Γ(S, W) C)) :=
    hW.isLocalization_stalk' y hy
  let e : S.presheaf.stalk (hW.fromSpec y) ≃+* Localization.AtPrime Q :=
    (IsLocalization.algEquiv (Q.comap (algebraMap Γ(S, W) C)).primeCompl _ _).toRingEquiv
  obtain ⟨h1, h2⟩ := hS (hW.fromSpec y)
  exact ⟨e.symm.toMulEquiv.isDomain _, .of_equiv e⟩

theorem eft : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (W : (gen Y).Opens), IsAffineOpen W →
    Algebra.EssFiniteType ℤ Γ(gen Y, W) := by
  intro E _ _ _ H D l Xo c Y W hW
  haveI := c.fin
  haveI : NumberField c.F := {}
  haveI := GlobalTheory.ThetaDescent.isProper_of_isProjOver Y.proj
  haveI : LocallyOfFiniteType (genStr Y) := inferInstance
  have h1 : ((genStr Y).appLE ⊤ W (fun _ _ => trivial)).hom.FiniteType :=
    (genStr Y).finiteType_appLE (isAffineOpen_top _) hW (fun _ _ => trivial)
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _ (fun y => ⟨(Scheme.ΓSpecIso (CommRingCat.of c.F)).hom y, by simp⟩)
  have hQ : Algebra.EssFiniteType ℤ ℚ := Algebra.EssFiniteType.of_isLocalization ℚ (nonZeroDivisors ℤ)
  have hZF : Algebra.EssFiniteType ℤ c.F := Algebra.EssFiniteType.comp ℤ ℚ c.F
  refine RingHom.essFiniteType_algebraMap.1 ?_
  convert ((RingHom.essFiniteType_algebraMap.2 hZF).comp h2.essFiniteType).comp h1.essFiniteType using 1
  exact Subsingleton.elim _ _

theorem stalk_of_chart {V : Scheme.{0}} (T : Type) [CommRing T] (ι : Sp T ⟶ V) [IsOpenImmersion ι]
    (v : V) (hv : v ∈ Set.range ι)
    (h : ∀ (Q : Ideal T) [Q.IsPrime], IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) ∧
      IsNoetherianRing (Localization.AtPrime Q)) :
    IsDomain (V.presheaf.stalk v) ∧ IsIntegrallyClosed (V.presheaf.stalk v) ∧ IsNoetherianRing (V.presheaf.stalk v) := by
  obtain ⟨t, rfl⟩ := hv
  haveI : t.asIdeal.IsPrime := PrimeSpectrum.isPrime (R := T) t
  let e : V.presheaf.stalk (ι t) ≃+* Localization.AtPrime t.asIdeal :=
    (asIso (ι.stalkMap t) ≪≫ Spec.stalkIso (CommRingCat.of T) t).commRingCatIsoToRingEquiv
  obtain ⟨h1, h2, h3⟩ := h t.asIdeal
  exact ⟨e.toMulEquiv.isDomain _, .of_equiv e.symm, isNoetherianRing_of_ringEquiv _ e.symm⟩

end GlobalTheory.FibreChart

namespace GlobalTheory.FibreChart
open scoped TensorProduct

end GlobalTheory.FibreChart
