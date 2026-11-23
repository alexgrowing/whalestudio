import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitOfSumEqOne
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

theorem algebraicIndependent_of_mem_adjoin_range :
    ∀ {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] {ι : Type} [Finite ι] (u v : ι → K),
      AlgebraicIndependent Ω u → (∀ a, u a ∈ IntermediateField.adjoin Ω (Set.range v)) →
      AlgebraicIndependent Ω v := by
  intro Ω K _ _ _ ι _ u v hu hmem
  set L := IntermediateField.adjoin Ω (Set.range v) with hL
  let v' : ι → L := fun a => ⟨v a, IntermediateField.subset_adjoin Ω _ ⟨a, rfl⟩⟩
  let u' : ι → L := fun a => ⟨u a, hmem a⟩
  have hu' : AlgebraicIndependent Ω u' := AlgebraicIndependent.of_comp (x := u') L.val hu
  have htop : IntermediateField.adjoin Ω (Set.range v') = ⊤ := by
    apply IntermediateField.map_injective L.val
    have hcomp : (⇑L.val ∘ v') = v := rfl
    rw [IntermediateField.adjoin_map, ← Set.range_comp, hcomp, ← AlgHom.fieldRange_eq_map,
      IntermediateField.fieldRange_val]
    try rfl
  haveI : Algebra.IsAlgebraic (Algebra.adjoin Ω (Set.range v')) L := by
    rw [← IntermediateField.isAlgebraic_adjoin_iff_top]
    refine ⟨fun x => ?_⟩
    have hx : x ∈ IntermediateField.adjoin Ω (Set.range v') := by
      rw [htop]
      exact IntermediateField.mem_top
    exact isAlgebraic_algebraMap (⟨x, hx⟩ : IntermediateField.adjoin Ω (Set.range v'))
  haveI : FaithfulSMul Ω L :=
    (faithfulSMul_iff_algebraMap_injective Ω L).mpr (algebraMap Ω L).injective
  obtain ⟨t, hts, htb⟩ := exists_isTranscendenceBasis_subset (R := Ω) (Set.range v')
  have hle : Cardinal.mk ι ≤ Cardinal.mk t :=
    hu'.cardinalMk_le_trdeg.trans htb.cardinalMk_eq_trdeg.symm.le
  haveI : Finite t := ((Set.finite_range v').subset hts).to_subtype
  have hcard : Nat.card ι ≤ Nat.card t := by
    letI := Fintype.ofFinite ι
    letI := Fintype.ofFinite t
    rw [Cardinal.mk_fintype, Cardinal.mk_fintype] at hle
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact_mod_cast hle
  have heq : t = Set.range v' :=
    Set.eq_of_subset_of_ncard_le hts
      (by
        rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
        exact (Finite.card_range_le v').trans hcard)
      (Set.finite_range v')
  subst heq
  have hinj : Function.Injective v' := by
    have hbij := (Set.rangeFactorization_surjective (f := v')).bijective_of_nat_card_le hcard
    intro a b hab
    exact hbij.1 (Subtype.ext hab)
  have hv' : AlgebraicIndependent Ω v' := (algebraicIndependent_subtype_range hinj).mp htb.1
  exact hv'.map' (f := L.val) Subtype.val_injective

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
