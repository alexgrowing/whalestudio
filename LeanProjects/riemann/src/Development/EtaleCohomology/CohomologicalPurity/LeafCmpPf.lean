import Development.EtaleCohomology.CohomologicalPurity.LeafClCut

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.CohomologicalPurity.Cl

def LeafCmpNb : Prop := ∀ (X : Scheme.{0}) (B B₀ : Type) [CommRing B] [CommRing B₀] (w : Spec (CommRingCat.of B) ⟶ X)
  (w₀ : Spec (CommRingCat.of B₀) ⟶ X), IsOpenImmersion w₀ → ∀ y, w y ∈ Set.range w₀ →
  ∃ (C : Type) (_ : CommRing C) (φ : B →+* C) (ψ : B₀ →+* C),
    IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)) ∧ y ∈ Set.range (Spec.map (CommRingCat.ofHom φ)) ∧
    Spec.map (CommRingCat.ofHom φ) ≫ w = Spec.map (CommRingCat.ofHom ψ) ≫ w₀

def LeafCmpId : Prop := ∀ (d : ℕ) (P : SP d) (F F₀ : Frame P) (C : Type) [CommRing C] (φ : F.B →+* C) (ψ : F₀.B →+* C),
  Spec.map (CommRingCat.ofHom φ) ≫ F.w = Spec.map (CommRingCat.ofHom ψ) ≫ F₀.w → F.I.map φ = F₀.I.map ψ

theorem spec_comp_ofHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [← Spec.map_comp]; rfl

theorem LeafCmp_of (hMat : LeafMat) (hNb : LeafCmpNb) (hId : LeafCmpId) : LeafCmp := by
  intro d P F F₀ h₀ y hy
  obtain ⟨C, _, φ, ψ, ho, ⟨z, rfl⟩, e⟩ := hNb P.X F.B F₀.B F.w F₀.w h₀ y hy
  have hI := hId d P F F₀ C φ ψ e
  obtain ⟨M, hdet, hM⟩ := hMat d C (ψ ∘ F₀.x) (φ ∘ F.x)
    (by rw [span_comp, span_comp, F.hx, F₀.hx, hI]) z
  let g : C := M.det
  let l : C →+* Localization.Away g := algebraMap C (Localization.Away g)
  have hl : IsOpenImmersion (Spec.map (CommRingCat.ofHom l)) :=
    Scheme.isOpenImmersion_SpecMap_localizationAway (R := CommRingCat.of C) g
  refine ⟨Localization.Away g, inferInstance, l.comp φ, l.comp ψ, M.map l, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [spec_comp_ofHom φ l]; infer_instance
  · have hr : z ∈ Set.range (PrimeSpectrum.comap l) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]; exact hdet
    obtain ⟨z', hz'⟩ := hr
    refine ⟨show Spec (CommRingCat.of (Localization.Away g)) from z', ?_⟩
    rw [spec_comp_ofHom φ l]
    show (Spec.map (CommRingCat.ofHom φ)) ((Spec.map (CommRingCat.ofHom l)) z') = _
    exact congrArg (Spec.map (CommRingCat.ofHom φ)) hz'
  · rw [spec_comp_ofHom φ l, spec_comp_ofHom ψ l, Category.assoc, Category.assoc, e]
  · rw [← Ideal.map_map, ← Ideal.map_map, hI]
  · change IsUnit (l.mapMatrix M).det
    rw [← RingHom.map_det]; exact IsLocalization.Away.algebraMap_isUnit g
  · funext j
    change l (φ (F.x j)) = _
    rw [show φ (F.x j) = (φ ∘ F.x) j from rfl, hM, RingHom.map_mulVec]
    rfl

end LateralTheory.CohomologicalPurity.Cl
