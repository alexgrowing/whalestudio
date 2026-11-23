import Development.EtaleCohomology.CohomologicalPurity.LeafExcPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity

theorem chainsInrSq (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) :
    (chains (ZMod q)).map (dbl.inr P') ≫ (chains (ZMod q)).map (dbl.map φ) =
      (chains (ZMod q)).map φ.right ≫ (chains (ZMod q)).map (dbl.inr P) := by
  rw [← Functor.map_comp, ← Functor.map_comp, dbl.inr_map]

abbrev cokC (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) :=
  cokernel.map ((chains (ZMod q)).map (dbl.inr P')) ((chains (ZMod q)).map (dbl.inr P))
    ((chains (ZMod q)).map φ.right) ((chains (ZMod q)).map (dbl.map φ)) (chainsInrSq q φ)

theorem HK.pull_comp' (R : Type) [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ)
    (x : HK R M F n) : HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := by
  rcases x.mk_surjective with ⟨z, rfl⟩
  simp only [HK.pull, HK.pre, cpre_mk]
  congr 1
  ext1
  simp [zcomp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

theorem HK.pull_id' (R : Type) [CommRing R] (K : Cx R) (F : Shv R) (n : ℤ) (x : HK R K F n) :
    HK.pull R (𝟙 K) F n x = x := by
  rcases x.mk_surjective with ⟨z, rfl⟩
  simp only [HK.pull, HK.pre, cpre_mk]
  congr 1
  ext1
  simp [zcomp]

theorem HK.pull_bij (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) [IsIso f] (F : Shv R) (n : ℤ) :
    Function.Bijective (HK.pull R f F n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨HK.pull R (inv f) F n, fun x => ?_, fun x => ?_⟩
  · rw [← HK.pull_comp', IsIso.inv_hom_id, HK.pull_id']
  · rw [← HK.pull_comp', IsIso.hom_inv_id, HK.pull_id']

def LeafExcIdent : Prop := ∀ (q : ℕ) (n i : ℤ), ∃ e : ∀ P : Arrow Spc,
    HK (ZMod q) (cokernel ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n ≃+ Hs q P n i,
  ∀ {P' P : Arrow Spc} (φ : P' ⟶ P) (x : HK (ZMod q) (cokernel ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n),
    Hs.pull q φ n i (e P x) = e P' (HK.pull (ZMod q) (cokC q φ) (tw q i) n x)

def LeafExcCx : Prop := ∀ (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P), IsIso (cokC q φ) → Exc q φ

theorem LeafExcCx_of (hI : LeafExcIdent) : LeafExcCx := by
  intro q P' P φ hφ n i
  obtain ⟨e, he⟩ := hI q n i
  have hfun : ⇑(Hs.pull q φ n i) = ⇑(e P') ∘ ⇑(HK.pull (ZMod q) (cokC q φ) (tw q i) n) ∘ ⇑(e P).symm := by
    funext y
    obtain ⟨x, rfl⟩ := (e P).surjective y
    simp [he]
  rw [hfun]
  exact (e P').bijective.comp ((HK.pull_bij _ _ _ _).comp (e P).symm.bijective)

def LeafExcDeg : Prop := ∀ (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P),
  (∀ p : SimplexCategoryᵒᵖ, IsIso (cokernel.map ((free (ZMod q)).map (P'.hom.app p)) ((free (ZMod q)).map (P.hom.app p))
    ((free (ZMod q)).map (φ.left.app p)) ((free (ZMod q)).map (φ.right.app p)) (freeSq _ φ p))) → IsIso (cokC q φ)

theorem LeafExcFormal_of (hI : LeafExcIdent) (hD : LeafExcDeg) : LeafExcFormal := by
  intro q P' P φ h
  exact LeafExcCx_of hI q φ (hD q φ h)

end LateralTheory.CohomologicalPurity
