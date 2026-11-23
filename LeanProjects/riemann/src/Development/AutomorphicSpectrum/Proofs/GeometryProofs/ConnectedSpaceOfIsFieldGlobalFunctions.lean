import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentOfClopen
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem connectedSpace_of_isField_globalFunctions (Z : Scheme.{0}) (h : IsField Γ(Z, ⊤)) :
    ConnectedSpace Z := by
  have hne : Nonempty Z := by
    by_contra hZ
    have hb : (⊤ : Z.Opens) = ⊥ := by
      ext x
      exact (hZ ⟨x⟩).elim
    have hs : Subsingleton Γ(Z, ⊤) := by
      rw [hb]
      infer_instance
    obtain ⟨a, b, hab⟩ := h.exists_pair_ne
    exact hab (Subsingleton.elim a b)
  have hp : PreconnectedSpace Z := by
    refine preconnectedSpace_iff_clopen.2 fun U hU => ?_
    obtain ⟨e, he, hUe⟩ := GlobalTheory.exists_idempotent_basicOpen_eq_of_isClopen Z U hU
    by_cases h0 : e = 0
    · left
      rw [← hUe, h0, Z.basicOpen_zero]
      rfl
    · right
      obtain ⟨b, hb⟩ := h.mul_inv_cancel h0
      have h1 : e = 1 := by
        calc e = e * e * b := by rw [_root_.mul_assoc, hb, _root_.mul_one]
          _ = e * b := by rw [he]
          _ = 1 := hb
      rw [← hUe, h1, Z.basicOpen_of_isUnit isUnit_one]
      rfl
  exact { toPreconnectedSpace := hp, toNonempty := hne }

theorem geometricallyConnected_of_isIso_appTop :
    ∀ (K : Type) [Field K] (X : Scheme.{0}) (p : X ⟶ Sp K), QuasiCompact p → QuasiSeparated p →
      IsIso p.appTop → GeometricallyConnected p := by
  intro K _ X p _ _ _
  refine ⟨fun L _ y Z a q H => ?_⟩
  have hy : Flat y := by
    obtain ⟨φ, rfl⟩ := Spec.map_surjective y
    rw [Flat.SpecMap_iff]
    algebraize [φ.hom]
    exact inferInstanceAs (Module.Flat K L)
  have hq : IsIso q.appTop := GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback H
  let e₁ : Γ(Spec (.of L), ⊤) ≃+* Γ(Z, ⊤) := (asIso q.appTop).commRingCatIsoToRingEquiv
  let e₂ : Γ(Spec (.of L), ⊤) ≃+* L := (Scheme.ΓSpecIso (.of L)).commRingCatIsoToRingEquiv
  have hL : IsField Γ(Spec (.of L), ⊤) := MulEquiv.isField (Field.toIsField L) e₂.toMulEquiv
  exact connectedSpace_of_isField_globalFunctions Z (MulEquiv.isField hL e₁.symm.toMulEquiv)

end GlobalTheory.CompanionTheory.Ar.Approx
