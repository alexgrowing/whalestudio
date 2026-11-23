import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomExtOfSecCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecCoordOfSubsingletonPic
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.CrdBasic

theorem pCrd_basic : (∀ (o R R' : Type) [CommRing o] [CommRing R] [CommRing R'] (n : ℕ) (x : Sp R ⟶ PSpace o n) (v : Fin (n + 1) → R) (i : R →+* R'), PCrd x v → PCrd (spMap i ≫ x) (fun j => i (v j))) ∧ (∀ (o R : Type) [CommRing o] [CommRing R] (n : ℕ) (x : Sp R ⟶ PSpace o n) (v : Fin (n + 1) → R) (a : R), IsUnit a → PCrd x v → PCrd x (fun j => a * v j)) ∧ ∀ (o K : Type) [CommRing o] [Field K] (n : ℕ) (x : Sp K ⟶ PSpace o n), (∃ v, PCrd x v) ∧ ∀ v, PCrd x v → ∃ j, v j ≠ 0 := by
  refine ⟨fun o R R' _ _ _ n x v i h => ?_, fun o R _ _ n x v a ha h => ?_, fun o K _ _ n x => ⟨?_, fun v h => ?_⟩⟩
  · exact (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ (ProjSpace.O1_isLB o n) h).1 R' i
  · exact (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ (ProjSpace.O1_isLB o n) h).2.1 ha.unit
  · exact GlobalTheory.ZM.FieldPoint.exists_secCoord o n K x
  · obtain ⟨c, hc⟩ := RepUniq.exists_spMap (x ≫ PSpace.str o n)
    obtain ⟨hv, -⟩ := GlobalTheory.ZM.ProjExt.eq_pt_of_secCoord c x hc v h
    by_contra h0
    push_neg at h0
    have : Ideal.span (Set.range v) = ⊥ := by
      rw [Ideal.span_eq_bot]
      rintro _ ⟨j, rfl⟩
      exact h0 j
    rw [this] at hv
    exact bot_ne_top hv

end GlobalTheory.UMin.CrdBasic
