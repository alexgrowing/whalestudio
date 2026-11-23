import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionIsDomainAndIsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeConditionsCoverModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkCharZeroEssFiniteTypeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericStalkPointInInteriorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkMapInjectiveBirationalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueCompFormalCompletionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompleteUnramifiedExtensionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionUnramifiedNormalStatement

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.TorRef.ChartAbove

theorem specMap_stalkCongr_fromSpecStalk {X : Scheme.{0}} {x y : X} (h : x = y) :
    Spec.map (X.presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫ X.fromSpecStalk x = X.fromSpecStalk y := by
  subst h
  simp

theorem exists_complete_normal_above (A B R : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [CommRing B] [IsDomain B] [IsLocalRing B]
    [IsIntegrallyClosed B] [CharZero B] [Algebra.EssFiniteType ℤ B] [CommRing R] [IsDomain R] [IsLocalRing R]
    (f : A →+* B) (g : A →+* R) (hA : IsNoetherianRing A) (hf : IsLocalHom f) (hfi : Function.Injective f)
    (hbir : ∀ b : B, ∃ a s : A, f s ≠ 0 ∧ f s * b = f a) (hg : IsLocalHom g) (hR : IsCN R)
    (het : IsEtaleCompletion g) (hfu : ((residue R).comp g).FormallyUnramified) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (φ : R →+* R') (ψ : B →+* R'),
      IsCN R' ∧ IsLocalHom ψ ∧ Function.Injective ψ ∧ IsEtaleCompletion ψ ∧
      ((residue R').comp ψ).FormallyUnramified ∧ Function.Injective φ ∧ IsLocalHom φ ∧ ψ.comp f = φ.comp g := by
  obtain ⟨C, _, _, _, φ0, ψ0, hCn, hφl, hφi, hψl, hψi, hψf, hψm, hψfin, hψfu, hcomm⟩ :=
    GlobalTheory.T.residue_comp_formal_completion A B R f g hA hR.1 inferInstance hf hfi hbir hg het hfu
  obtain ⟨R', _, _, ι, hRn, hRc, hιl, hιi, hιe, hιu⟩ := GlobalTheory.T.exists_complete_unramified_extension B C ψ0 hCn hψl hψf hψm hψfin hψfu
  have hBn : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing ℤ B
  obtain ⟨hd, hic⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed B
  haveI := hιl
  haveI := hψl
  haveI := hφl
  have hloc : IsLocalHom (ι.comp ψ0) := inferInstance
  obtain ⟨hRd, hRi⟩ := GlobalTheory.T.completion_unramified_normal B R' (ι.comp ψ0) hBn hd hic hRn hRc hloc hιe hιu
  have hinj : Function.Injective (ι.comp ψ0) := hιi.comp hψi
  haveI : CharZero R' := charZero_of_injective_ringHom hinj
  refine ⟨R', inferInstance, hRd, inferInstance, ι.comp φ0, ι.comp ψ0, ⟨hRn, hRi, hRc, inferInstance⟩, hloc, hinj,
    hιe, hιu, hιi.comp hφi, inferInstance, ?_⟩
  rw [RingHom.comp_assoc, hcomm, ← RingHom.comp_assoc]

theorem exists_chart_above : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (π : Z.X ⟶ X.X), Z.j ≫ π = X.j → π ≫ X.s = Z.s → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ X.X) (z : Z.X), IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → ξ (closedPoint R) = π z → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ξ' : Sp R' ⟶ Z.X) (φ : R →+* R'), IsCN R' ∧ ξ' (closedPoint R') = z ∧ IsEtaleCompletion (Scheme.stalkClosedPointTo ξ').hom ∧ ((residue R').comp (Scheme.stalkClosedPointTo ξ').hom).FormallyUnramified ∧ Function.Injective φ ∧ IsLocalHom φ ∧ ξ' ≫ π = spMap φ ≫ ξ ∧ Dense (ξ' ⁻¹' Set.range Z.j) := by
  intro E _ _ _ H D l Xo c X Z π hj hs R _ _ _ ξ z hR het hfu hpt
  haveI := (Z.normal z).1
  haveI := (Z.normal z).2
  haveI := (X.normal (ξ (closedPoint R))).1
  obtain ⟨hcz, hez⟩ := GlobalTheory.T.stalk_charZero_essFiniteType E H D l Xo c Z z
  obtain ⟨-, hexX⟩ := GlobalTheory.T.stalk_charZero_essFiniteType E H D l Xo c X (ξ (closedPoint R))
  have hAn : IsNoetherianRing (X.X.presheaf.stalk (ξ (closedPoint R))) := Algebra.EssFiniteType.isNoetherianRing ℤ _
  obtain ⟨hbi, hbb⟩ := GlobalTheory.T.stalk_map_injective_birational E H D l Xo c X Z π hj hs z
  let e := X.X.presheaf.stalkCongr (Inseparable.of_eq hpt)
  have heb : Function.Bijective e.hom.hom := ConcreteCategory.bijective_of_isIso e.hom
  let f : X.X.presheaf.stalk (ξ (closedPoint R)) →+* Z.X.presheaf.stalk z := (π.stalkMap z).hom.comp e.hom.hom
  have hfi : Function.Injective f := hbi.comp heb.1
  have hbir : ∀ b : Z.X.presheaf.stalk z, ∃ a s : X.X.presheaf.stalk (ξ (closedPoint R)), f s ≠ 0 ∧ f s * b = f a := by
    intro b
    obtain ⟨a, s, hs0, hsb⟩ := hbb b
    obtain ⟨a', rfl⟩ := heb.2 a
    obtain ⟨s', rfl⟩ := heb.2 s
    exact ⟨a', s', hs0, hsb⟩
  have hfl : IsLocalHom f := inferInstance
  let g := (Scheme.stalkClosedPointTo ξ).hom
  obtain ⟨R', _, _, _, φ, ψ, hR', hψl, hψi, het', hfu', hφi, hφl, hcomm⟩ :=
    exists_complete_normal_above _ _ R f g hAn hfl hfi hbir inferInstance hR het hfu

  haveI := hψl
  let ψc : Z.X.presheaf.stalk z ⟶ CommRingCat.of R' := CommRingCat.ofHom ψ
  haveI : IsLocalHom ψc.hom := hψl
  let ξ' : Sp R' ⟶ Z.X := (SpecToEquivOfLocalRing Z.X (CommRingCat.of R')).symm ⟨z, ⟨ψc, inferInstance⟩⟩
  have hsym := (SpecToEquivOfLocalRing Z.X (CommRingCat.of R')).apply_symm_apply ⟨z, ⟨ψc, inferInstance⟩⟩
  rw [SpecToEquivOfLocalRing_eq_iff] at hsym
  obtain ⟨h1, h2⟩ := hsym
  have hpt' : ξ' (closedPoint R') = z := h1
  have h2' : (Scheme.stalkClosedPointTo ξ').hom = ψ.comp (Z.X.presheaf.stalkCongr (Inseparable.of_eq h1)).hom.hom := by
    exact congrArg (fun q => q.hom) h2
  refine ⟨R', inferInstance, inferInstance, inferInstance, ξ', φ, hR', hpt', ?_, ?_, hφi, hφl, ?_, ?_⟩
  · rw [h2']
    exact isEtaleCompletion_comp_bij _ (ConcreteCategory.bijective_of_isIso _) ψ het'
  · rw [h2']
    have hsurj : Function.Surjective (Z.X.presheaf.stalkCongr (Inseparable.of_eq h1)).hom.hom :=
      (ConcreteCategory.bijective_of_isIso _).2
    have h3 := RingHom.FormallyUnramified.comp (RingHom.FormallyUnramified.of_surjective hsurj) hfu'
    exact h3
  · have hcomm' : Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom φ = e.hom ≫ π.stalkMap z ≫ ψc := by
      ext a
      have := congrArg (fun q : _ →+* R' => q a) hcomm
      exact this.symm
    calc ξ' ≫ π = Spec.map ψc ≫ Z.X.fromSpecStalk z ≫ π := by simp only [ξ', SpecToEquivOfLocalRing_symm_apply, Category.assoc]
      _ = Spec.map ψc ≫ Spec.map (π.stalkMap z) ≫ X.X.fromSpecStalk (π z) := by
          rw [Scheme.SpecMap_stalkMap_fromSpecStalk]
      _ = Spec.map ψc ≫ Spec.map (π.stalkMap z) ≫ Spec.map e.hom ≫ X.X.fromSpecStalk (ξ (closedPoint R)) := by
          rw [specMap_stalkCongr_fromSpecStalk hpt]
      _ = Spec.map (e.hom ≫ π.stalkMap z ≫ ψc) ≫ X.X.fromSpecStalk (ξ (closedPoint R)) := by
          simp only [Spec.map_comp, Category.assoc]
      _ = Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom φ) ≫ X.X.fromSpecStalk (ξ (closedPoint R)) := by
          rw [hcomm']
      _ = spMap φ ≫ ξ := by
          rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  · let η0 : PrimeSpectrum R' := ⟨⊥, Ideal.isPrime_bot⟩
    let η : Sp R' := η0
    have hη : η ∈ ξ' ⁻¹' Set.range Z.j := by
      show ξ' η ∈ Set.range Z.j
      have hxi : ξ' η = Z.X.fromSpecStalk z ((Spec.map ψc) η) := rfl
      rw [hxi]
      apply GlobalTheory.T.generic_stalk_point_in_interior E H D l Xo c Z z
      show Ideal.comap ψ ⊥ = ⊥
      rw [← RingHom.ker_eq_comap_bot]
      exact (RingHom.injective_iff_ker_eq_bot ψ).1 hψi
    have hcl0 : closure ({η0} : Set (PrimeSpectrum R')) = Set.univ := by
      rw [PrimeSpectrum.closure_singleton]
      exact PrimeSpectrum.zeroLocus_bot
    have hcl : closure ({η} : Set (Sp R')) = Set.univ := hcl0
    rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
    intro p
    have hp : p ∈ closure ({η} : Set (Sp R')) := by rw [hcl]; trivial
    exact closure_mono (Set.singleton_subset_iff.2 hη) hp

end GlobalTheory.TorRef.ChartAbove
