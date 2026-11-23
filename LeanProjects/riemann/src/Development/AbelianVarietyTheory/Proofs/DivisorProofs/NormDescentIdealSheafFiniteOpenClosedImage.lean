import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescendedNormIdealSheafFiniteNormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCoefficientIdealMapCompleteDvrEqProdLiftsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftPointAffineHomSectionsRingHomStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM

namespace GlobalTheory.NormSheaf

theorem normDescentSheaf : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z), IsFinite π → IsIntegral Y → IsLocallyNoetherian Y →
    GlobalTheory.IsNormalScheme Y → GlobalTheory.IsNormalScheme Z → IsOpen (Set.range π) →
    CharZero Γ(Y, ⊤) → ∀ I : Y.IdealSheafData, ∃ (d : ℕ) (J : Z.IdealSheafData), 1 ≤ d ∧
      (∀ x ∈ J.support, ∃ y ∈ I.support, π y = x) ∧
      ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
        IsAdicComplete (maximalIdeal V) V → ∀ ξ : Sp V ⟶ Z, ξ (closedPoint V) ∈ Set.range π →
        ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : CharZero V')
          (f : V →+* V') (ψ : Fin d → (Sp V' ⟶ Y)), IsAdicComplete (maximalIdeal V') V' ∧ Function.Injective f ∧
          IsLocalHom f ∧ (∀ j, ψ j ≫ π = spMap f ≫ ξ) ∧ (idlAlong J ξ).map f = ∏ j, idlAlong I (ψ j) := by
  intro Y Z π hπ hY hYn hYN hZN hopen hchar I
  haveI : IsAffineHom π := hπ.toIsAffineHom
  obtain ⟨K, L, _, _, _, _, hK, J, hsupp, hJ⟩ := GlobalTheory.T.exists_descended_normIdealSheaf_finite_normal Y Z π hY hYn hYN hZN hopen hchar I
  refine ⟨Module.finrank K L, J, Module.finrank_pos, hsupp, ?_⟩
  intro V _ _ _ _ hV ξ hξ
  obtain ⟨U, hU, hxU, hUW⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens
    (show ξ (closedPoint V) ∈ (⟨Set.range π, hopen⟩ : Z.Opens) from hξ)
  have hle : ⊤ ≤ ξ ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem ξ hxU).ge
  let U' : Z.affineOpens := ⟨U, hU⟩
  obtain ⟨_, _, hA, hAc, hB, hfin, hKf, hLf, hsq, hJU⟩ := hJ U' hUW ⟨_, hxU⟩
  obtain ⟨V', _, _, _, _, f, ψ', hV', hf, hfl, hψc, hprod⟩ := GlobalTheory.T.normCoefficientIdeal_map_complete_dvr_eq_prod_lifts Γ(Z, U') Γ(Y, π ⁻¹ᵁ U) K L (π.app U).hom
    hfin hsq (I.ideal ⟨π ⁻¹ᵁ U, U'.2.preimage π⟩) V hV (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (.of V)).hom).hom
  choose ψ hψ hψI using fun j => GlobalTheory.T.exists_lift_point_affineHom_sections_ringHom Y Z π U' V V' ξ hle f (ψ' j) (hψc j)
  refine ⟨V', inferInstance, inferInstance, inferInstance, inferInstance, f, ψ, hV', hf, hfl, hψ, ?_⟩
  rw [GlobalTheory.TraitOrder.idlAlong_eq_map J ξ U' hle, hJU, Ideal.map_map]
  simp only [hψI]
  exact hprod

end GlobalTheory.NormSheaf
