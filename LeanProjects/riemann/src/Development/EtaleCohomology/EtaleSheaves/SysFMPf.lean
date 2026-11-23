import Development.EtaleCohomology.EtaleSheaves.NbIsoPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.BuildCut

namespace LateralTheory.E.SysFMPf

def phi {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) : Γ(w.normalization, ⊤) →+* W :=
  (w.toNormalization.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of W)).hom).hom

def RR {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] {W : Type} [CommRing W]
    (w : Spec (CommRingCat.of W) ⟶ P) (q : PrimeSpectrum W) : Set w.normalization :=
  {y | ∀ s : Γ(w.normalization, ⊤), IsIdempotentElem (phi w s) → phi w s ∉ q.asIdeal → y ∈ w.normalization.basicOpen s}

def Sys : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ y : w.normalization,
    ∃ (q : PrimeSpectrum W) (J : Type) (_ : SmallCategory J) (_ : IsCofiltered J) (D : J ⥤ Scheme.{0})
      (ι : ∀ j, D.obj j ⟶ w.normalization),
      (∀ j, IsOpenImmersion (ι j) ∧ IsClosedImmersion (ι j) ∧ y ∈ Set.range (ι j)) ∧
      (∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j ∧ IsAffineHom (D.map f)) ∧
      ⋂ j, Set.range (ι j) = RR w q

def FMex : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ q : PrimeSpectrum W,
    ∃ m : (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).normalization ⟶ w.normalization,
      Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w.toNormalization =
        (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).toNormalization ≫ m ∧
      m ≫ w.fromNormalization = (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).fromNormalization ∧
      Mono m ∧ Flat m ∧ QuasiCompact m

def FMrange : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ (q : PrimeSpectrum W)
    (m : (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).normalization ⟶ w.normalization),
      Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w.toNormalization =
        (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).toNormalization ≫ m →
      m ≫ w.fromNormalization = (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).fromNormalization →
      Set.range m = RR w q

theorem SysFM_of (hS : Sys) (hE : FMex) (hR : FMrange) : LateralTheory.E.NbIsoPf.SysFM := by
  intro P _ _ W _ w hW y
  obtain ⟨q, J, _, _, D, ι, h1, h2, h3⟩ := hS W w hW y
  obtain ⟨m, e1, e2, hm, hf, hq⟩ := hE W w hW q
  refine ⟨q, J, inferInstance, inferInstance, D, ι, h1, h2, m, hm, hf, hq, ?_⟩
  rw [h3]
  exact hR W w hW q m e1 e2

end LateralTheory.E.SysFMPf
