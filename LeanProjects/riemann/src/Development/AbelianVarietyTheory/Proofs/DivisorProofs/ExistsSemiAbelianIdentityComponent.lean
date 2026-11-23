import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsThetaMeanSquareNorm
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSemiStable
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IdentityComponentOpen
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIsoOfIsOpenImmersionOfGeometricallyConnected
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfSection
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GeometricallyConnectedOfIsPullbackOfSurjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.CxPts GlobalTheory.Points
open scoped CategoryTheory.Obj
open GlobalTheory.MBLit

noncomputable section

namespace GlobalTheory.SemiStableId

def transportExt {K : Type} [Field K] {G₁ H : Over (Spec (.of K))} [GrpObj G₁] [GrpObj H]
    (E : TorusExtension G₁) (e : G₁ ≅ H) [IsMonHom e.hom] : TorusExtension H where
  X := E.X
  addCommGroup := E.addCommGroup
  free := E.free
  finite := E.finite
  B := E.B
  grpB := E.grpB
  isAbelian := E.isAbelian
  q := e.inv ≫ E.q
  q_hom := by have := E.q_hom; infer_instance
  q_flat := by have := E.q_flat; have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv)); show Flat (e.inv.left ≫ E.q.left); infer_instance
  q_surjective := by have := E.q_surjective; have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv)); show Surjective (e.inv.left ≫ E.q.left); infer_instance
  q_quasiCompact := by
    have := E.q_quasiCompact; have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv)); show QuasiCompact (e.inv.left ≫ E.q.left); infer_instance
  i := E.i ≫ e.hom
  i_hom := by have := E.i_hom; infer_instance
  isKernel := by
    have h2 : IsPullback e.hom E.q (e.inv ≫ E.q) (𝟙 _) := IsPullback.of_horiz_isIso ⟨by simp⟩
    simpa using E.isKernel.paste_horiz h2

end GlobalTheory.SemiStableId

namespace GlobalTheory.SemiStableId

variable {S : Scheme.{0}} {G G₀ : Over S} [GrpObj G] (j : G₀ ⟶ G)

abbrev RangeIsId : Prop := ∀ x : G.left, x ∈ Set.range j.left ↔
  x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))

include j in
theorem unit_mem_fibre (s : S) : (η[G]).left s ∈ G.hom ⁻¹' {s} := by
  show G.hom ((η[G]).left s) = s
  rw [← Scheme.Hom.comp_apply, Over.w]
  rfl

theorem isConnected_fibre [IsOpenImmersion j.left] (hr : RangeIsId j) (s : S) :
    _root_.IsConnected (G₀.hom ⁻¹' {s}) := by
  have hw : ∀ x, G.hom (j.left x) = G₀.hom x := fun x => by
    rw [← Scheme.Hom.comp_apply, Over.w]
  have himg : j.left '' (G₀.hom ⁻¹' {s}) = connectedComponentIn (G.hom ⁻¹' {s}) ((η[G]).left s) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have := (hr (j.left x)).1 ⟨x, rfl⟩
      rwa [hw, show G₀.hom x = s from hx] at this
    · intro hy
      have hys : G.hom y = s := connectedComponentIn_subset (G.hom ⁻¹' {s}) _ hy
      obtain ⟨x, rfl⟩ := (hr y).2 (by rwa [hys])
      exact ⟨x, by rw [Set.mem_preimage, ← hw, hys]; rfl, rfl⟩
  have hc : _root_.IsConnected (connectedComponentIn (G.hom ⁻¹' {s}) ((η[G]).left s)) :=
    isConnected_connectedComponentIn_iff.mpr (unit_mem_fibre j s)
  rw [← himg] at hc
  exact ⟨hc.nonempty.of_image, j.left.isOpenEmbedding.isInducing.isPreconnected_image.1 hc.isPreconnected⟩

end GlobalTheory.SemiStableId

namespace GlobalTheory.SemiStableId

end GlobalTheory.SemiStableId

namespace GlobalTheory.SemiStableId

end GlobalTheory.SemiStableId

namespace GlobalTheory.SemiStableId

end GlobalTheory.SemiStableId
