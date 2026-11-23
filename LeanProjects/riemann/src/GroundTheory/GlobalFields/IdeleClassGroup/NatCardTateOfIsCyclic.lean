import Mathlib
import GroundTheory.GlobalFields.IdeleClassGroup.InvariantsGalois
import GroundTheory.GlobalFields.SecondInequality.Cyclic
import GroundTheory.LocalFields.HerbrandCyclic

namespace GroundTheory.Global

open NumberField IntermediateField GroundTheory.LocalField.Abstract

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

namespace IdeleClassLimit

open FiniteSubfield

theorem natCard_tate_of_isCyclic (K L : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) [(L.subgroupOf K).Normal]
    [(L.subgroupOf K).FiniteIndex] {F E : FiniteSubfield} (hFE : F ≤ E)
    (hK : K = F.1.fixingSubgroup) (hL : L = E.1.fixingSubgroup)
    (hcyc : IsCyclic (K ⧸ L.subgroupOf K)) :
    Nat.card (tateZero IdeleClassLimit K L) = L.relIndex K ∧
      Nat.card (tateNegOne IdeleClassLimit K L) = 1 := by
  subst hK hL
  have : Fact (F ≤ E) := ⟨hFE⟩
  have : IsGalois F.1 E.1 := isGalois_of_normal (F := F) (E := E)

  have hcycE : IsCyclic (E.1 ≃ₐ[F.1] E.1) := by
    let φ := QuotientGroup.lift (E.1.fixingSubgroup.subgroupOf F.1.fixingSubgroup)
      (restrictHom (F := F) (E := E)) (ker_restrictHom (F := F) (E := E)).ge
    refine isCyclic_of_surjective φ fun x ↦ ?_
    obtain ⟨g, rfl⟩ := restrictHom_surjective (F := F) (E := E) x
    exact ⟨g, rfl⟩
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := E.1 ≃ₐ[F.1] E.1)
  have hax := classFieldAxiom_ideleClassGroup (K := F.1) (L := E.1) σ hσ
  refine ⟨?_, ?_⟩
  · rw [Nat.card_congr (tateZeroEquivGalois (F := F) (E := E)).toEquiv,
      GroundTheory.LocalField.natCard_tateZero_eq hσ, hax.1]
    exact (relIndex_fixingSubgroup hFE).symm
  · rw [Nat.card_congr (tateNegOneEquivGalois (F := F) (E := E)).toEquiv,
      GroundTheory.LocalField.natCard_tateNegOne_eq hσ, hax.2]

theorem classFieldAxiom : ClassFieldAxiom (ℚ̄ ≃ₐ[ℚ] ℚ̄) IdeleClassLimit := by
  intro U V hVU _ hcyc
  exact natCard_tate_of_isCyclic (U : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) (V : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄))
    (ofOpenSubgroup_le hVU) (fixingSubgroup_ofOpenSubgroup U).symm
    (fixingSubgroup_ofOpenSubgroup V).symm hcyc

end IdeleClassLimit

end

end GroundTheory.Global
