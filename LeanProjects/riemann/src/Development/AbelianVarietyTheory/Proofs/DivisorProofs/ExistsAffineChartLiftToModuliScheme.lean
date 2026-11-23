import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnivBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.Points

namespace GlobalTheory.Poinc.ChartAt

theorem exists_affine_chart_lift : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (w : X₁.M.Z), X₁.π w ∈ Set.range i → ∃ (U : X₁.M.Z.Opens) (u : Sp (X₁.M.ringOn U) ⟶ F.X), IsAffineOpen U ∧ w ∈ U ∧ (∀ w' ∈ U, X₁.π w' ∈ Set.range i) ∧ spMap (X₁.M.ringOn U).val.toRingHom ≫ u = spMap X₁.S.R.val.toRingHom ≫ X₁.u := by
  intro g n F W Z i X₁ w hw
  haveI := X₁.imm
  set V : X₁.M.Z.Opens := X₁.π ⁻¹ᵁ i.opensRange with hVdef
  have hwV : w ∈ V := by
    show X₁.π w ∈ (i.opensRange : Set Z)
    simpa [Scheme.Hom.coe_opensRange] using hw
  obtain ⟨U, hU, hwU, hUV⟩ := exists_isAffineOpen_mem_and_subset (X := X₁.M.Z) (U := V) hwV
  have hne : ((U : X₁.M.Z.Opens) : Set X₁.M.Z).Nonempty := ⟨w, hwU⟩
  have hUi : ∀ w' ∈ U, X₁.π w' ∈ Set.range i := by
    intro w' hw'
    have := hUV hw'
    simpa [hVdef, Scheme.Hom.coe_opensRange] using this
  let φ : Γ(X₁.M.Z, U) ⟶ CommRingCat.of (X₁.M.ringOn U) :=
    CommRingCat.ofHom (X₁.M.sectionsEquiv U hne).toRingHom
  let f : Sp (X₁.M.ringOn U) ⟶ X₁.M.Z := Spec.map φ ≫ hU.fromSpec
  have hrange : Set.range (f ≫ X₁.π) ⊆ Set.range i := by
    rintro _ ⟨y, rfl⟩
    apply hUi
    have : hU.fromSpec (Spec.map φ y) ∈ Set.range hU.fromSpec := ⟨_, rfl⟩
    rw [hU.range_fromSpec] at this
    exact this
  refine ⟨U, IsOpenImmersion.lift i (f ≫ X₁.π) hrange, hU, hwU, hUi, ?_⟩
  rw [← cancel_mono i, Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, Category.assoc, ← X₁.comp]
  have hpt : ⊤ ≤ X₁.M.pt ⁻¹ᵁ U := X₁.M.top_le_preimage_pt hne
  have hφ : φ ≫ CommRingCat.ofHom (X₁.M.ringOn U).val.toRingHom = valMap X₁.M.pt U hpt := by
    ext a
    show ((X₁.M.sectionsEquiv U hne a : X₁.M.ringOn U) : X₁.Ω₁) = _
    rw [RatModel.coe_sectionsEquiv, ← valR_eq, valF_eq_valR]
  have hf : spMap (X₁.M.ringOn U).val.toRingHom ≫ f = X₁.M.pt := by
    simp only [f, ← Category.assoc]
    rw [spMap, ← Spec.map_comp, hφ, specMap_valMap_fromSpec]
  rw [← hf]
  simp only [f, Category.assoc]

end GlobalTheory.Poinc.ChartAt
