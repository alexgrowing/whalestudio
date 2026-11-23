import Development.EtaleCohomology.EtaleSheaves.LeafSupport
import Development.EtaleCohomology.EtaleSheaves.FirstChernNaturality

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafCochainVanishPf

variable {R : Type} [CommRing R]

theorem free_ext_zero (P : PSh) (G : Shv R) (φ : (free R).obj P ⟶ G)
    (h : ∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.hom.app (op U)).hom (freeGen R P U x) = 0) : φ = 0 := by
  have h0 : (0 : (free R).obj P ⟶ G).hom = 0 := rfl
  refine Sheaf.hom_ext ?_
  rw [h0]
  refine sheafify_hom_ext _ _ _ G.property ?_
  ext U : 2
  refine ModuleCat.free_hom_ext (fun x => ?_)
  exact (h U.unop x.down).trans (by erw [Limits.comp_zero]; rfl)

theorem chains_isZero (E : Spc) (p : ℤ) (hp : 0 < p) : Limits.IsZero (((chains R).obj E).X p) := by
  refine HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => ?_)
  have : ComplexShape.embeddingDownNat.f i = -(i : ℤ) := rfl
  omega

theorem cochain_zero_of (E : Spc) {U V : Spc} (f : U ⟶ E) (g : V ⟶ E) (hc : Cover2 R f g) (K : Cx R) (k : ℤ)
    (γ : Cochain ((chains R).obj E) K k)
    (hU : ∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (Y : Scheme.{0}) (y : Sx U N Y), ev γ N w h Y ((f.app _).app _ y) = 0)
    (hV : ∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (Y : Scheme.{0}) (y : Sx V N Y), ev γ N w h Y ((g.app _).app _ y) = 0) :
    γ = 0 := by
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  rw [Cochain.zero_v]
  by_cases hp : 0 < p
  · exact (chains_isZero (R := R) E p hp).eq_of_src _ _
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, p = -(N : ℤ) := ⟨(-p).toNat, by omega⟩
  have hφ : (chainsXIso R E N).inv ≫ γ.v (-(N : ℤ)) q hpq = 0 := by
    have := hc.2.2 (op (SimplexCategory.mk N))
    rw [← cancel_epi (biprod.desc ((free R).map (f.app (op (SimplexCategory.mk N))))
      ((free R).map (g.app (op (SimplexCategory.mk N))))), Limits.comp_zero]
    apply biprod.hom_ext'
    · rw [biprod.inl_desc_assoc, Limits.comp_zero]
      refine free_ext_zero _ _ _ (fun Y y => ?_)
      have e := hU N q hpq Y y
      unfold ev at e
      rw [← LateralTheory.E.FirstChernNaturality.freeGen_nat (R := R)] at e
      exact e
    · rw [biprod.inr_desc_assoc, Limits.comp_zero]
      refine free_ext_zero _ _ _ (fun Y y => ?_)
      have e := hV N q hpq Y y
      unfold ev at e
      rw [← LateralTheory.E.FirstChernNaturality.freeGen_nat (R := R)] at e
      exact e
  rw [← Iso.hom_inv_id_assoc (chainsXIso R E N) (γ.v _ _ hpq), hφ, Limits.comp_zero]

end LateralTheory.E.LeafCochainVanishPf

theorem LateralTheory.E.LeafA6suppPf.LeafCochainVanish_of : LateralTheory.E.LeafA6suppPf.LeafCochainVanish := by
  intro R _ U V E f g hc K k γ hU hV
  exact LateralTheory.E.LeafCochainVanishPf.cochain_zero_of E f g hc K k γ hU hV
