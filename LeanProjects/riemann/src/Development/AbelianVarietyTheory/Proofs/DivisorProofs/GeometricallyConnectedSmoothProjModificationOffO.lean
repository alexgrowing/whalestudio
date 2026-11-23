import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVarietyCompactifyingConnectedComponent
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompHS

set_option autoImplicit false

namespace GlobalTheory.ModifGeomConn

theorem geometricallyConnected_of_geometricallyIrreducible {X Y : Scheme.{0}} (f : X ⟶ Y)
    [GeometricallyIrreducible f] : GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  have : IrreducibleSpace ↥(Limits.pullback f x) :=
    GeometricallyIrreducible.geometrically_irreducibleSpace _ _ _ (.of_hasPullback _ _)
  infer_instance

theorem geometricallyConnected_modif : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (sX : X ⟶ Sp F) (n : ℕ) [SmoothOfRelativeDimension n sX] (U : X.Opens) (M : Modif sX U n) [IsIntegral M.X] [GeometricallyConnected sX], (U : Set X).Nonempty → GeometricallyConnected M.str := by
  intro F _ X _ sX n _ U M _ _ hU
  have : Smooth sX := SmoothOfRelativeDimension.smooth n sX
  have : GeometricallyIntegral sX := GlobalTheory.geometricallyIntegral_of_smooth sX
  obtain ⟨x, hx⟩ := hU
  have : Surjective (U.ι ≫ sX) := ⟨fun s => ⟨⟨x, hx⟩, Subsingleton.elim _ _⟩⟩
  have h2 : GeometricallyConnected (U.ι ≫ sX) := geometricallyConnected_of_geometricallyIrreducible _
  have := M.iso
  have h3 : GeometricallyConnected (M.opn.ι ≫ M.str) := by
    have e : M.opn.ι ≫ M.str = (M.σ ∣_ U) ≫ (U.ι ≫ sX) := by
      rw [Modif.str, ← Category.assoc, ← Category.assoc, morphismRestrict_ι]
    rw [e]
    rw [GeometricallyConnected.eq_geometrically] at h2 ⊢
    exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).2 h2
  exact GlobalTheory.CompactVar.geometricallyConnected_of_denseRange M.opn.ι M.str
    (by rw [Scheme.Opens.range_ι]; exact M.dense)

end GlobalTheory.ModifGeomConn
