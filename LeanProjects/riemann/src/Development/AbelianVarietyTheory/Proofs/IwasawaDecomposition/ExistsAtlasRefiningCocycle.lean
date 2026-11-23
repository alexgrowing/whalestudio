import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag

theorem exists_finset_basicOpen_le {X : Scheme.{0}} (C : Coc X) {R : Type} [CommRing R] (χ : Sp R ⟶ X) :
    ∃ s : Finset R, (∀ g ∈ s, ∃ α, ∀ x : PrimeSpectrum R, g ∉ x.asIdeal → χ x ∈ C.B α) ∧
      ∀ x : PrimeSpectrum R, ∃ g ∈ s, g ∉ x.asIdeal := by
  classical
  have h : ∀ x : PrimeSpectrum R, ∃ g : R, g ∉ x.asIdeal ∧ ∃ α, ∀ y : PrimeSpectrum R, g ∉ y.asIdeal → χ y ∈ C.B α := by
    intro x
    obtain ⟨α, hα⟩ := C.cover (χ x)
    obtain ⟨_, ⟨g, rfl⟩, hx, hsub⟩ := (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open
      (a := x) (u := ((χ ⁻¹ᵁ C.B α : (Sp R).Opens) : Set (Sp R))) hα (χ ⁻¹ᵁ C.B α).2
    exact ⟨g, hx, α, fun y hy => hsub hy⟩
  choose g hg hα using h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : PrimeSpectrum R => (PrimeSpectrum.basicOpen (g x) : Set (PrimeSpectrum R)))
    (fun x => (PrimeSpectrum.basicOpen (g x)).2) (fun x _ => Set.mem_iUnion.2 ⟨x, hg x⟩)
  refine ⟨t.image g, fun a ha => ?_, fun x => ?_⟩
  · obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 ha
    exact hα x
  · obtain ⟨y, hy, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨g y, Finset.mem_image_of_mem g hy, hx⟩

theorem isOpenImmersion_spMap_away {R : Type} [CommRing R] (g : R) :
    IsOpenImmersion (spMap (algebraMap R (Localization.Away g))) :=
  IsOpenImmersion.of_isLocalization g

theorem mem_range_spMap_away {R : Type} [CommRing R] (g : R) (x : PrimeSpectrum R) :
    x ∈ Set.range (spMap (algebraMap R (Localization.Away g))) ↔ g ∉ x.asIdeal :=
  Set.ext_iff.1 (PrimeSpectrum.localization_away_comap_range (Localization.Away g) g) x

theorem Atlas.exists_refine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) [IsDiscreteValuationRing V] (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (C : Coc X), ∃ A' : Atlas M π ty, (∀ (K : Type) [Field K] (w : Sp K ⟶ X) (u : Vecs Dw M.t K), A'.FlagAt w u ↔ A.FlagAt w u) ∧ ∃ α : A'.ch.ι → C.A, ∀ a, ⊤ ≤ A'.ch.χ a ⁻¹ᵁ C.B (α a) := by
  intro E _ _ _ H Dw l Xo c V _ M X π ty A C
  choose s hs hcov using fun a => exists_finset_basicOpen_le C (A.ch.χ a)
  let P : PreAtlas M X :=
    { ch :=
        { ι := Σ a : A.ch.ι, {g // g ∈ s a}
          R := fun k => Localization.Away k.2.1
          χ := fun k => spMap (algebraMap (A.ch.R k.1) (Localization.Away k.2.1)) ≫ A.ch.χ k.1
          opn := fun k => by
            have := isOpenImmersion_spMap_away k.2.1
            infer_instance }
      alg := fun k => (algebraMap (A.ch.R k.1) (Localization.Away k.2.1)).comp (A.alg k.1)
      fr := fun k => (A.fr k.1).bc (algebraMap (A.ch.R k.1) (Localization.Away k.2.1)) }
  have key : ∀ (K : Type) [Field K] (w : Sp K ⟶ X) (u : Vecs Dw M.t K), P.FlagAt π ty w u ↔ A.FlagAt w u := by
    intro K _ w u
    constructor
    · rintro ⟨k, φ, e, hf, hS⟩
      refine ⟨k.1, φ.comp (algebraMap (A.ch.R k.1) (Localization.Away k.2.1)), ?_, hf, ?_⟩
      · rw [← spMap_comp', Category.assoc]; exact e
      · rw [← Vecs.bc_bc]; exact hS
    · rintro ⟨a, φ, e, hf, hS⟩
      obtain ⟨g, hg, hφ⟩ := hcov a ⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩
      have hu : IsUnit (φ g) := IsUnit.mk0 _ hφ
      have hψ : (IsLocalization.Away.lift (S := Localization.Away g) g hu).comp (algebraMap _ _) = φ :=
        IsLocalization.Away.lift_comp g hu
      refine ⟨⟨a, g, hg⟩, IsLocalization.Away.lift (S := Localization.Away g) g hu, ?_, ?_, ?_⟩
      · show spMap _ ≫ spMap _ ≫ _ = _
        rw [← Category.assoc, spMap_comp', hψ, e]
      · show LocM.IsFrame M.t (RingHom.comp _ (RingHom.comp _ _)) _ _
        rw [← RingHom.comp_assoc, hψ]; exact hf
      · show SameFlag ty M.t _ (((A.fr a).bc _).bc _) _
        rw [Vecs.bc_bc, hψ]; exact hS
  refine ⟨{ toPreAtlas := P, cover := ?_, alg_s := fun k => ?_, smooth := fun k => ?_, frame := fun k => ?_,
            glue := fun K _ k k' φ φ' e => ?_, bij := fun K _ f y hy u hu => ?_ }, key, ?_⟩
  · rw [← A.cover]
    ext x
    simp only [Charts.carrier, Set.mem_iUnion]
    constructor
    · rintro ⟨k, y, rfl⟩
      exact ⟨k.1, spMap (algebraMap (A.ch.R k.1) (Localization.Away k.2.1)) y, (Scheme.Hom.comp_apply _ _ _).symm⟩
    · rintro ⟨a, y, rfl⟩
      obtain ⟨g, hg, hy⟩ := hcov a y
      obtain ⟨z, rfl⟩ := (mem_range_spMap_away g y).2 hy
      exact ⟨⟨a, g, hg⟩, z, Scheme.Hom.comp_apply _ _ _⟩
  · exact A.affineOpenChart_comp_structure_eq_spMap (a := k.1) rfl
  · have := isOpenImmersion_spMap_away k.2.1
    have := A.smooth k.1
    show Smooth ((spMap (algebraMap (A.ch.R k.1) (Localization.Away k.2.1)) ≫ A.ch.χ k.1) ≫ π)
    rw [Category.assoc]
    infer_instance
  · exact A.isFrame_bc (a := k.1) rfl
  · have e' : spMap φ ≫ spMap _ ≫ A.ch.χ k.1 = spMap φ' ≫ spMap _ ≫ A.ch.χ k'.1 := e
    rw [← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp'] at e'
    have h := A.glue K k.1 k'.1 _ _ e'
    rw [← Vecs.bc_bc, ← Vecs.bc_bc, ← spMap_comp', Category.assoc] at h
    show SameFlag ty M.t (spMap φ ≫ (spMap _ ≫ A.ch.χ k.1) ≫ π) _ _
    rw [Category.assoc]
    exact h
  · exact (existsUnique_congr fun w => and_congr_right' (key K w u)).2 (A.bij K f y hy u hu)
  · choose α hα using fun k : P.ch.ι => hs k.1 k.2.1 k.2.2
    refine ⟨α, fun k z _ => ?_⟩
    have := hα k _ ((mem_range_spMap_away k.2.1 _).1 ⟨z, rfl⟩)
    rw [← Scheme.Hom.comp_apply] at this
    exact this

end GlobalTheory.DRFlag
