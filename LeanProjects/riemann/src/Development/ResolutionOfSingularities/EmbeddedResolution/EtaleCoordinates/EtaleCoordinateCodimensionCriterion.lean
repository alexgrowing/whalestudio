import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ConstantCodimension
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsSmoothBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCenterChart
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineSpaceSmooth
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def castAddImage (c d : ℕ) : Finset (Fin (c + d)) :=
  (Finset.univ : Finset (Fin c)).image (Fin.castAdd d)

theorem castAddImage_eq_image_castAdd (c d : ℕ) :
    castAddImage c d = (Finset.univ : Finset (Fin c)).image (Fin.castAdd d) := rfl

theorem card_castAddImage (c d : ℕ) : (castAddImage c d).card = c := by
  have hinj : Function.Injective (Fin.castAdd d : Fin c → Fin (c + d)) := by
    intro a b hab
    have hv : ((Fin.castAdd d a : Fin (c + d)) : ℕ) = ((Fin.castAdd d b : Fin (c + d)) : ℕ) :=
      congrArg (fun z : Fin (c + d) => (z : ℕ)) hab
    exact Fin.ext hv
  rw [castAddImage_eq_image_castAdd, Finset.card_image_of_injective _ hinj, Finset.card_univ,
    Fintype.card_fin]

private theorem mem_image_ι_of_mem {X' : Scheme.{u}} (U : X'.Opens)
    (V : U.toScheme.Opens) (y : X') (hy : y ∈ U) (h : (⟨y, hy⟩ : ↥U) ∈ V) :
    y ∈ U.ι ''ᵁ V :=
  ⟨⟨y, hy⟩, h, rfl⟩

private theorem range_ι_comp_ι_eq_image {X' : Scheme.{u}} (U : X'.Opens) (V : U.toScheme.Opens) :
    Set.range ((V.ι ≫ U.ι).base) = (↑(U.ι ''ᵁ V) : Set ↥X') := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨_, w.2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

private def etaleChartTop (k : Type u) [Field k] (c : ℕ) :
    EtaleChart (affineSpaceFinToSpec k c) (⊤ : (affineSpaceFin k c).Opens) c where
  map := (⊤ : (affineSpaceFin k c).Opens).ι
  comp_struct := rfl
  isEtale := inferInstance

private theorem etaleChartTop_map (k : Type u) [Field k] (c : ℕ) :
    (etaleChartTop k c).map = (⊤ : (affineSpaceFin k c).Opens).ι := rfl

private theorem restrictIdeal_top_coordSubspaceIdeal_univ (k : Type u) [Field k] (c : ℕ) :
    restrictIdeal (coordSubspaceIdeal k c (Finset.univ : Finset (Fin c)))
      (⊤ : (affineSpaceFin k c).Opens) = (etaleChartTop k c).coordIdeal Finset.univ := by
  rw [restrictIdeal_eq_comap_ι, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, etaleChartTop_map]

theorem exists_etaleChart_image_of_restrictIdeal_eq {X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X' ⟶ Spec (CommRingCat.of k)) (U : X'.Opens) (V : U.toScheme.Opens) (n : ℕ)
    (ch : EtaleChart (U.ι ≫ p) V n) (D : X'.IdealSheafData) (S : Finset (Fin n))
    (h : restrictIdeal (restrictIdeal D U) V = ch.coordIdeal S) :
    ∃ ch' : EtaleChart p (U.ι ''ᵁ V) n, restrictIdeal D (U.ι ''ᵁ V) = ch'.coordIdeal S := by
  have hr : Set.range ((U.ι ''ᵁ V).ι).base = Set.range ((V.ι ≫ U.ι).base) := by
    rw [Scheme.Opens.range_ι, ← range_ι_comp_ι_eq_image]
  let φ : (U.ι ''ᵁ V).toScheme ≅ V.toScheme :=
    AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq ((U.ι ''ᵁ V).ι) (V.ι ≫ U.ι) hr
  have hfac : φ.hom ≫ (V.ι ≫ U.ι) = (U.ι ''ᵁ V).ι :=
    AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hr
  have hcs : (φ.hom ≫ ch.map) ≫ affineSpaceFinToSpec k n = (U.ι ''ᵁ V).ι ≫ p := by
    calc (φ.hom ≫ ch.map) ≫ affineSpaceFinToSpec k n
        = φ.hom ≫ (ch.map ≫ affineSpaceFinToSpec k n) := Category.assoc _ _ _
      _ = φ.hom ≫ (V.ι ≫ (U.ι ≫ p)) := by rw [ch.comp_struct]
      _ = (φ.hom ≫ (V.ι ≫ U.ι)) ≫ p := by simp only [Category.assoc]
      _ = (U.ι ''ᵁ V).ι ≫ p := by rw [hfac]
  have : AlgebraicGeometry.Etale ch.map := ch.isEtale
  have hkey : (D.comap U.ι).comap V.ι = (coordSubspaceIdeal k n S).comap ch.map := by
    rw [← restrictIdeal_eq_comap_ι, ← restrictIdeal_eq_comap_ι, h, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
  refine ⟨⟨φ.hom ≫ ch.map, hcs, inferInstance⟩, ?_⟩
  rw [restrictIdeal_eq_comap_ι, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
  calc D.comap (U.ι ''ᵁ V).ι
      = ((D.comap U.ι).comap V.ι).comap φ.hom := by
        rw [← hfac, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]
    _ = ((coordSubspaceIdeal k n S).comap ch.map).comap φ.hom := by rw [hkey]
    _ = (coordSubspaceIdeal k n S).comap (φ.hom ≫ ch.map) := by
        rw [Scheme.IdealSheafData.comap_comp]

theorem exists_etaleChart_of_restrictIdeal_ker_eq_comap
    {X X' : Scheme.{u}} {k : Type u} [Field k] (p : X' ⟶ Spec (CommRingCat.of k))
    (τ : X ⟶ X') (c : ℕ) (U : X'.Opens) (q : U.toScheme ⟶ affineSpaceFin k c)
    [AlgebraicGeometry.Smooth q] (hq : q ≫ affineSpaceFinToSpec k c = U.ι ≫ p)
    (hker : restrictIdeal τ.ker U =
      (coordSubspaceIdeal k c (Finset.univ : Finset (Fin c))).comap q)
    (x : X) (hx : τ.base x ∈ U) :
    ∃ (V : U.toScheme.Opens) (_ : IsAffineOpen V) (_ : (⟨τ.base x, hx⟩ : ↥U) ∈ V) (d : ℕ)
      (ch : EtaleChart (U.ι ≫ p) V (c + d)),
      restrictIdeal (restrictIdeal τ.ker U) V = ch.coordIdeal (castAddImage c d) := by
  have : AlgebraicGeometry.Smooth (affineSpaceFinToSpec k c) := affineSpaceIsSmooth ..
  obtain ⟨V, hVU, d, ch, hVaff, hyV, hcoord⟩ :=
    exists_etaleChart_comap_coord_eq (affineSpaceFinToSpec k c) q (etaleChartTop k c)
      (⟨τ.base x, hx⟩ : ↥U) (by trivial)
  have hidtop : (coordSubspaceIdeal k c (Finset.univ : Finset (Fin c))).ideal
      ⟨⊤, isAffineOpen_top (affineSpaceFin k c)⟩
      = Ideal.span ((etaleChartTop k c).coord ''
          ((Finset.univ : Finset (Fin c)) : Set (Fin c))) :=
    EtaleChart.ideal_eq_span_coord (etaleChartTop k c) (isAffineOpen_top (affineSpaceFin k c))
      (coordSubspaceIdeal k c (Finset.univ : Finset (Fin c))) Finset.univ
      (restrictIdeal_top_coordSubspaceIdeal_univ k c)
  have hspanV : (restrictIdeal τ.ker U).ideal ⟨V, hVaff⟩
      = Ideal.span (ch.coord ''
          ((castAddImage c d : Finset (Fin (c + d))) : Set (Fin (c + d)))) := by
    rw [hker,
      Scheme.IdealSheafData.comap_ideal_eq_map_appLE
        (coordSubspaceIdeal k c (Finset.univ : Finset (Fin c))) q
        ⟨⊤, isAffineOpen_top (affineSpaceFin k c)⟩ ⟨V, hVaff⟩ hVU,
      hidtop, Ideal.map_span]
    congr 1
    rw [Set.image_image, castAddImage_eq_image_castAdd, Finset.coe_image, Set.image_image]
    exact Set.image_congr (fun j _ => (hcoord j).symm)
  have hcs : ch.map ≫ affineSpaceFinToSpec k (c + d) = V.ι ≫ (U.ι ≫ p) := by
    rw [ch.comp_struct, hq]
  refine ⟨V, hVaff, hyV, d, ⟨ch.map, hcs, ch.isEtale⟩, ?_⟩
  exact restrictIdeal_eq_coordIdeal_of_ideal_eq_span hVaff _ _ (castAddImage c d) hspanV

theorem hasEtaleCoordCodim_of_locally_smooth_over_affineSpace {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X' ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (τ : X ⟶ X') (c : ℕ)
    (h : ∀ x : X, ∃ (U : X'.Opens) (_ : τ.base x ∈ U) (q : U.toScheme ⟶ affineSpaceFin k c),
      AlgebraicGeometry.Smooth q ∧ q ≫ affineSpaceFinToSpec k c = U.ι ≫ p ∧
        restrictIdeal τ.ker U =
          (coordSubspaceIdeal k c (Finset.univ : Finset (Fin c))).comap q) :
    HasEtaleCoordCodim p τ c := by
  intro x
  obtain ⟨U, hxU, q, hqsm, hqc, hker⟩ := h x
  have := hqsm
  obtain ⟨V, hVaff, hxV, d, ch, hch⟩ :=
    exists_etaleChart_of_restrictIdeal_ker_eq_comap p τ c U q hqc hker x hxU
  obtain ⟨ch', hch'⟩ :=
    exists_etaleChart_image_of_restrictIdeal_eq p U V (c + d) ch τ.ker (castAddImage c d) hch
  exact ⟨U.ι ''ᵁ V, mem_image_ι_of_mem U V (τ.base x) hxU hxV, c + d, ch',
    castAddImage c d, card_castAddImage c d, hch'⟩

end FunctorialResolution.EmbeddedResolution

end
