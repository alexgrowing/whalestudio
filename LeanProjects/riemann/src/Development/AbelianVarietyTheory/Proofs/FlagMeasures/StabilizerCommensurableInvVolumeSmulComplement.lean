import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNondegenerateTupleComplementFixerStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeStabilizerCommensurableUnramifiedHermitiaStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DatumStabilizerBetweenLatticeStabilizersStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryGroupOrthogonalComplementUnimodularStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFactsStatement

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem Frames.stab_commensurable_invVol_smul : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ Λ : Submodule L.O S.V, IsLat L Λ → S.complementReferenceCompactSubgroup.relIndex (S.H0 ⊓ MulAction.stabilizer S.GLV Λ) ≠ 0 ∧ (S.H0 ⊓ MulAction.stabilizer S.GLV Λ).relIndex S.complementReferenceCompactSubgroup ≠ 0 ∧ ∀ h ∈ S.H0, invVol S.complementReferenceCompactSubgroup (S.H0 ⊓ MulAction.stabilizer S.GLV (h • Λ)) = invVol S.complementReferenceCompactSubgroup (S.H0 ⊓ MulAction.stabilizer S.GLV Λ)) ∧ ∀ d Λ, S.IsTerm d Λ → S.complementReferenceCompactSubgroup.relIndex (S.H0 ⊓ MulAction.stabilizer S.GLV d) ≠ 0 ∧ (S.H0 ⊓ MulAction.stabilizer S.GLV d).relIndex S.complementReferenceCompactSubgroup ≠ 0 := by
  intro F _ _ _ _ _ E _ _ _ L r k S
  obtain ⟨x, hdet, hspan, hH0, hstd, -⟩ := GlobalTheory.T.exists_nondegenerate_tuple_complement_fixer L r k S
  set Λs : Submodule L.O S.V := Submodule.span L.O (Set.range fun i => (Pi.single i 1 : S.V)) with hΛs
  have hK : S.complementReferenceCompactSubgroup = S.H0 ⊓ MulAction.stabilizer S.GLV Λs := rfl
  have comm : ∀ Λ Λ' : Submodule L.O S.V, IsLat L Λ → IsLat L Λ' →
      (S.H0 ⊓ MulAction.stabilizer S.GLV Λ').relIndex (S.H0 ⊓ MulAction.stabilizer S.GLV Λ) ≠ 0 :=
    fun Λ Λ' hΛ hΛ' => (GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L Λ Λ' hΛ hΛ' S.H0).1
  have latPart : ∀ Λ : Submodule L.O S.V, IsLat L Λ →
      S.complementReferenceCompactSubgroup.relIndex (S.H0 ⊓ MulAction.stabilizer S.GLV Λ) ≠ 0 ∧
        (S.H0 ⊓ MulAction.stabilizer S.GLV Λ).relIndex S.complementReferenceCompactSubgroup ≠ 0 := by
    intro Λ hΛ
    rw [hK]
    exact ⟨comm Λ Λs hΛ hstd, comm Λs Λ hstd hΛ⟩
  refine ⟨fun Λ hΛ => ⟨(latPart Λ hΛ).1, (latPart Λ hΛ).2, ?_⟩, ?_⟩
  · intro h hh
    have hfix : S.H0 = fixG L S.Hm (Submodule.span E (Set.range x)) := by rw [hspan]; exact hH0
    have hh' : h ∈ fixG L S.Hm (Submodule.span E (Set.range x)) := hfix ▸ hh
    have key := GlobalTheory.T.unitaryGroup_orthogonalComplement_unimodular L S.Hm S.herm (2 * r + 2) x hdet Λs Λ hstd hΛ h hh'
    rw [hK, hfix]
    exact key
  · intro d Λ hT
    have hΛ : IsLat L Λ := (GlobalTheory.T.hermitian_double_coset_term_basic_facts L r k S d Λ hT).1.1
    obtain ⟨hlo, Λ₂, hΛ₂, hhi⟩ := GlobalTheory.T.datum_stabilizer_between_lattice_stabilizers L r k S d Λ hT
    refine ⟨fun h0 => (latPart Λ₂ hΛ₂).1 (Subgroup.relIndex_eq_zero_of_le_right hhi h0),
      fun h0 => (latPart Λ hΛ).2 (Subgroup.relIndex_eq_zero_of_le_left hlo h0)⟩

end GlobalTheory.HL
