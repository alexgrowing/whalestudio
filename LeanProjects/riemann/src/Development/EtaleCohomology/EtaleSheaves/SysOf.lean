import Development.EtaleCohomology.EtaleSheaves.CompCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut LateralTheory.E.BuildCut LateralTheory.E.CompCut

namespace LateralTheory.E.SysPf

def HasLim : Prop := ∀ {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}),
  (∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)) → ∃ c : Cone D, Nonempty (IsLimit c)

def NbIso : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ y : w.normalization,
    ∃ (q : PrimeSpectrum W) (J : Type) (_ : SmallCategory J) (_ : IsCofiltered J) (D : J ⥤ Scheme.{0})
      (ι : ∀ j, D.obj j ⟶ w.normalization),
      (∀ j, IsOpenImmersion (ι j) ∧ IsClosedImmersion (ι j) ∧ y ∈ Set.range (ι j)) ∧
      (∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j ∧ IsAffineHom (D.map f)) ∧
      ∀ c : Cone D, IsLimit c →
        Nonempty (c.pt ≅ (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).normalization)

theorem Sys_of (hH : HasLim) (hN : NbIso) : Sys := by
  intro P _ _ W _ w hW y
  obtain ⟨q, J, _, _, D, ι, h1, h2, h3⟩ := hN W w hW y
  obtain ⟨c, ⟨hc⟩⟩ := hH D (fun f => (h2 f).2)
  exact ⟨q, J, inferInstance, inferInstance, D, c, ι, ⟨⟨hc⟩, h1, fun f => h2 f⟩, h3 c hc⟩

end LateralTheory.E.SysPf
