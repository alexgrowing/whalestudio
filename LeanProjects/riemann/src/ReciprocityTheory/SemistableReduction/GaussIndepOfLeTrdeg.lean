import Mathlib

namespace ReciprocityTheory.MultiplicativeHeights

open MvPolynomial

private theorem exists_transcendenceBasis_subset_adjoin_range {E C : Type} [Field E] [Field C] [Algebra E C] {σ : Type}
    (tb : σ → C) : ∃ t ⊆ ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))),
      IsTranscendenceBasis E (Subtype.val : t → Algebra.adjoin E (Set.range tb)) := by
  have htop : Algebra.adjoin E ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))) = ⊤ :=
    Algebra.adjoin_adjoin_coe_preimage
  haveI : FaithfulSMul E (Algebra.adjoin E (Set.range tb)) :=
    (faithfulSMul_iff_algebraMap_injective E _).mpr (algebraMap E _).injective
  haveI : Algebra.IsAlgebraic
      (Algebra.adjoin E ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))))
      (Algebra.adjoin E (Set.range tb)) := ⟨fun a => by
    have ha : a ∈ Algebra.adjoin E ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))) := by
      rw [htop]; exact Algebra.mem_top
    exact isAlgebraic_algebraMap (⟨a, ha⟩ : Algebra.adjoin E _)⟩
  exact exists_isTranscendenceBasis_subset (R := E) _

theorem gauss_trdeg_adjoin_le {E C : Type} [Field E] [Field C] [Algebra E C] {σ : Type}
    (tb : σ → C) : Algebra.trdeg E (Algebra.adjoin E (Set.range tb)) ≤ Cardinal.mk σ := by
  obtain ⟨t, hts, hb⟩ := exists_transcendenceBasis_subset_adjoin_range (E := E) tb
  rw [← hb.cardinalMk_eq_trdeg]
  calc Cardinal.mk t ≤ Cardinal.mk ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))) :=
        Cardinal.mk_le_mk_of_subset hts
    _ ≤ Cardinal.mk (Set.range tb) := Cardinal.mk_preimage_of_injective _ _ Subtype.val_injective
    _ ≤ Cardinal.mk σ := Cardinal.mk_range_le

theorem gauss_card_le_trdeg_add {F E C : Type} [Field F] [Field E] [Field C] [Algebra F E] [Algebra E C]
    [Algebra F C] [IsScalarTower F E C] {σ τ : Type} (tb : σ → C) (ub : τ → C)
    (hu : AlgebraicIndependent F ub) (hmem : ∀ j, ub j ∈ Algebra.adjoin E (Set.range tb)) :
    Cardinal.mk τ ≤ Algebra.trdeg F E + Algebra.trdeg E (Algebra.adjoin E (Set.range tb)) := by
  haveI : FaithfulSMul F E :=
    (faithfulSMul_iff_algebraMap_injective F E).mpr (algebraMap F E).injective
  haveI : FaithfulSMul E (Algebra.adjoin E (Set.range tb)) :=
    (faithfulSMul_iff_algebraMap_injective E _).mpr (algebraMap E _).injective
  rw [trdeg_add_eq F E (A := Algebra.adjoin E (Set.range tb))]
  have hu' : AlgebraicIndependent F (fun j => (⟨ub j, hmem j⟩ : Algebra.adjoin E (Set.range tb))) :=
    AlgebraicIndependent.of_comp ((Algebra.adjoin E (Set.range tb)).val.restrictScalars F) hu
  exact hu'.cardinalMk_le_trdeg

theorem gauss_indep_of_le_trdeg {E C : Type} [Field E] [Field C] [Algebra E C] {σ : Type}
    [Finite σ] (tb : σ → C)
    (h : Cardinal.mk σ ≤ Algebra.trdeg E (Algebra.adjoin E (Set.range tb))) :
    AlgebraicIndependent E tb := by
  classical
  obtain ⟨t, hts, hb⟩ := exists_transcendenceBasis_subset_adjoin_range (E := E) tb
  have ht := hb.cardinalMk_eq_trdeg
  have h1 : Cardinal.mk t ≤ Cardinal.mk ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))) :=
    Cardinal.mk_le_mk_of_subset hts
  have h2 : Cardinal.mk ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))) ≤
      Cardinal.mk (Set.range tb) := Cardinal.mk_preimage_of_injective _ _ Subtype.val_injective
  have h3 : Cardinal.mk (Set.range tb) ≤ Cardinal.mk σ := Cardinal.mk_range_le
  have hσt : Cardinal.mk σ ≤ Cardinal.mk t := ht ▸ h

  have hinj : Function.Injective tb := by
    obtain ⟨e⟩ := Cardinal.eq.1 (le_antisymm h3 (hσt.trans (h1.trans h2)))
    have hr : Function.Injective (Set.rangeFactorization tb) :=
      (Finite.injective_iff_surjective_of_equiv e.symm).2 Set.rangeFactorization_surjective
    exact fun a b hab => hr (Subtype.ext hab)

  have hsf : ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))).Finite :=
    (Set.finite_range tb).preimage Subtype.val_injective.injOn
  have hle : ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))).ncard ≤ t.ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact Cardinal.toNat_le_toNat ((h2.trans h3).trans hσt) (hsf.subset hts).lt_aleph0
  rw [Set.eq_of_subset_of_ncard_le hts hle hsf] at hb
  let g : σ → Algebra.adjoin E (Set.range tb) := fun i => ⟨tb i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  have hginj : Function.Injective g := fun a b hab => hinj (congrArg Subtype.val hab)
  have hrange : Set.range g = ((↑) ⁻¹' Set.range tb : Set (Algebra.adjoin E (Set.range tb))) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, Subtype.ext hi⟩
  have hg : AlgebraicIndependent E g := by
    rw [← algebraicIndependent_subtype_range hginj, hrange]
    exact hb.1
  exact hg.map' (f := (Algebra.adjoin E (Set.range tb)).val) Subtype.val_injective

theorem gauss_card_arith {a b : Cardinal} {s d : ℕ} (h : ((s + d : ℕ) : Cardinal) ≤ a + b)
    (ha : a ≤ d) (hb : b ≤ s) : a = d ∧ b = s := by
  obtain ⟨a', rfl⟩ := Cardinal.lt_aleph0.1 (ha.trans_lt (Cardinal.nat_lt_aleph0 d))
  obtain ⟨b', rfl⟩ := Cardinal.lt_aleph0.1 (hb.trans_lt (Cardinal.nat_lt_aleph0 s))
  have h' : s + d ≤ a' + b' := by exact_mod_cast h
  have ha' : a' ≤ d := by exact_mod_cast ha
  have hb' : b' ≤ s := by exact_mod_cast hb
  constructor
  · exact_mod_cast (by omega : a' = d)
  · exact_mod_cast (by omega : b' = s)

theorem gauss_aeval_mem {B C : Type} [CommRing B] [CommRing C] [Algebra B C] {σ : Type}
    (g : σ → C) (P : MvPolynomial σ B) (R : Subring C)
    (hc : ∀ α, algebraMap B C (P.coeff α) ∈ R) (hg : ∀ s, g s ∈ R) : aeval g P ∈ R := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  exact R.sum_mem fun α _ => R.mul_mem (hc α) (R.prod_mem fun i _ => R.pow_mem (hg i) _)

end ReciprocityTheory.MultiplicativeHeights
