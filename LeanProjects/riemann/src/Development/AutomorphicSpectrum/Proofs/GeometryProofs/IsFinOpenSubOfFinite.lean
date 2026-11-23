import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteOpenLeClosedFibreStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem mem_of_finite_of_closedFibre {R : Type} [CommRing R] [IsLocalRing R]
    {X : Over (Spec (CommRingCat.of R))} (W : X.left.Opens)
    (hW : ∀ x : X.left, X.hom x = IsLocalRing.closedPoint R → x ∈ W)
    (Y : Over (Spec (CommRingCat.of R))) (hY : IsFinite Y.hom) (h : Y ⟶ X) (z : Y.left) :
    h.left z ∈ W := by
  haveI := hY
  haveI : IsIso (⊤ : Y.left.Opens).ι := by rw [← Scheme.topIso_hom]; infer_instance
  have hfin : IsFinite ((⊤ : Y.left.Opens).ι ≫ Y.hom) := inferInstance
  have hle := GlobalTheory.T.finite_open_le_closed_fibre R Y.left Y.hom ⊤ (h.left ⁻¹ᵁ W) hfin (fun x hx => by
    apply hW
    have hw : h.left ≫ X.hom = Y.hom := Over.w h
    have hc := Scheme.Hom.comp_apply h.left X.hom x
    rw [hw] at hc
    rw [← hc]
    exact hx)
  exact hle (show z ∈ (⊤ : Y.left.Opens) from trivial)

abbrev openOver {S : Scheme.{0}} (X : Over S) (U : X.left.Opens) : Over S := Over.mk (U.ι ≫ X.hom)

abbrev openIncl {S : Scheme.{0}} (X : Over S) (U : X.left.Opens) : openOver X U ⟶ X := Over.homMk U.ι rfl

theorem exists_factor_openIncl {S : Scheme.{0}} {X Y : Over S} (U : X.left.Opens) (x : Y ⟶ X)
    (hx : ∀ z, x.left z ∈ U) : ∃ x' : Y ⟶ openOver X U, x' ≫ openIncl X U = x := by
  have hr : Set.range x.left ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    exact hx z
  have hc : IsOpenImmersion.lift U.ι x.left hr ≫ U.ι = x.left := IsOpenImmersion.lift_fac _ _ _
  refine ⟨Over.homMk (IsOpenImmersion.lift U.ι x.left hr) ?_, ?_⟩
  · simp only [Over.mk_hom]
    rw [← Category.assoc, hc]
    exact Over.w x
  · ext1
    exact hc

theorem QFGroup.isFinOpenSub_of_closedFibre :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (T : Type) [CommGroup T] (Γ : QFGroup R T)
      (U : Γ.G.left.Opens), IsFinite (U.ι ≫ Γ.G.hom) →
      (∀ x : Γ.G.left, Γ.G.hom x = IsLocalRing.closedPoint R → x ∈ U) → Γ.IsFinOpenSub U := by
  intro R _ _ _ T _ Γ U hfin hU
  haveI := hfin
  have hV : IsFinite (openOver Γ.G U).hom := hfin
  haveI := hV
  refine ⟨hfin, ?_, ?_, ?_⟩
  · intro x
    refine mem_of_finite_of_closedFibre U hU (𝟙_ _) ?_ η[Γ.G] x
    show IsFinite (𝟙 _)
    infer_instance
  · intro S x y hx hy z
    obtain ⟨x', rfl⟩ := exists_factor_openIncl U x hx
    obtain ⟨y', rfl⟩ := exists_factor_openIncl U y hy
    have hP : IsFinite (openOver Γ.G U ⊗ openOver Γ.G U).hom := by
      rw [Over.tensorObj_hom]
      infer_instance
    have key := mem_of_finite_of_closedFibre U hU _ hP
      ((fst _ _ ≫ openIncl Γ.G U) * (snd _ _ ≫ openIncl Γ.G U))
    have heq : x' ≫ openIncl Γ.G U * y' ≫ openIncl Γ.G U =
        lift x' y' ≫ ((fst _ _ ≫ openIncl Γ.G U) * (snd _ _ ≫ openIncl Γ.G U)) := by
      rw [comp_mul]
      simp
    rw [heq]
    simpa using key ((lift x' y').left z)
  · intro S x hx z
    obtain ⟨x', rfl⟩ := exists_factor_openIncl U x hx
    have key := mem_of_finite_of_closedFibre U hU _ hV (openIncl Γ.G U)⁻¹
    have heq : (x' ≫ openIncl Γ.G U)⁻¹ = x' ≫ (openIncl Γ.G U)⁻¹ := by
      simp [Hom.inv_def]
    rw [heq]
    simpa using key (x'.left z)

end GlobalTheory.CompanionTheory.Ar.BT
