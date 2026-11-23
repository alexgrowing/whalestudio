import Development.EtaleCohomology.EtaleSheaves.SysOf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.BuildCut

namespace LateralTheory.E.NbIsoPf

def FlatMonoLim : Prop := ∀ {Y : Scheme.{0}} {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0})
  (ι : ∀ j, D.obj j ⟶ Y), (∀ j, IsOpenImmersion (ι j) ∧ IsClosedImmersion (ι j)) →
  (∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j) →
  ∀ {X : Scheme.{0}} (m : X ⟶ Y), Mono m → Flat m → QuasiCompact m → Set.range m = ⋂ j, Set.range (ι j) →
  ∀ c : Cone D, IsLimit c → Nonempty (c.pt ≅ X)

def SysFM : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ y : w.normalization,
    ∃ (q : PrimeSpectrum W) (J : Type) (_ : SmallCategory J) (_ : IsCofiltered J) (D : J ⥤ Scheme.{0})
      (ι : ∀ j, D.obj j ⟶ w.normalization),
      (∀ j, IsOpenImmersion (ι j) ∧ IsClosedImmersion (ι j) ∧ y ∈ Set.range (ι j)) ∧
      (∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j ∧ IsAffineHom (D.map f)) ∧
      ∃ m : (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).normalization ⟶ w.normalization,
        Mono m ∧ Flat m ∧ QuasiCompact m ∧ Set.range m = ⋂ j, Set.range (ι j)

theorem NbIso_of (hS : SysFM) (hL : FlatMonoLim) : LateralTheory.E.SysPf.NbIso := by
  intro P _ _ W _ w hW y
  obtain ⟨q, J, _, _, D, ι, h1, h2, m, hm, hf, hq, hr⟩ := hS W w hW y
  refine ⟨q, J, inferInstance, inferInstance, D, ι, h1, h2, fun c hc => ?_⟩
  exact hL D ι (fun j => ⟨(h1 j).1, (h1 j).2.1⟩) (fun f => (h2 f).1) m hm hf hq hr c hc

end LateralTheory.E.NbIsoPf
