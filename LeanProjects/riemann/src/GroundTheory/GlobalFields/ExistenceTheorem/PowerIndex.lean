import Mathlib
import GroundTheory.GlobalFields.SUnits

namespace GroundTheory.Global

open NumberField IsDedekindDomain Module

noncomputable section

section PowerIndex

variable {G : Type*} [CommGroup G]

theorem mem_torsion_of_pow_mem_torsion {n : ℕ} (hn : n ≠ 0) {x : G}
    (hx : x ^ n ∈ CommGroup.torsion G) : x ∈ CommGroup.torsion G := by
  rw [CommGroup.mem_torsion] at hx ⊢
  exact (isOfFinOrder_pow.1 hx).resolve_right hn

theorem range_powMonoidHom_subgroupOf_torsion {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : G →* G).range.subgroupOf (CommGroup.torsion G) =
      (powMonoidHom n : CommGroup.torsion G →* CommGroup.torsion G).range := by
  ext ⟨t, ht⟩
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range, MonoidHom.mem_range]
  constructor
  · rintro ⟨x, hx⟩
    rw [powMonoidHom_apply] at hx
    refine ⟨⟨x, mem_torsion_of_pow_mem_torsion hn ?_⟩, Subtype.ext ?_⟩
    · rw [hx]
      exact ht
    · exact hx
  · rintro ⟨x, hx⟩
    exact ⟨x, congrArg Subtype.val hx⟩

theorem range_powMonoidHom_sup_torsion (n : ℕ) :
    (powMonoidHom n : G →* G).range ⊔ CommGroup.torsion G =
      (powMonoidHom n : G ⧸ CommGroup.torsion G →* G ⧸ CommGroup.torsion G).range.comap
        (QuotientGroup.mk' (CommGroup.torsion G)) := by
  ext x
  simp only [Subgroup.mem_comap, MonoidHom.mem_range, powMonoidHom_apply]
  constructor
  · intro hx
    obtain ⟨_, ⟨b, rfl⟩, t, ht, rfl⟩ := Subgroup.mem_sup.1 hx
    refine ⟨QuotientGroup.mk' _ b, ?_⟩
    have h1 : QuotientGroup.mk' (CommGroup.torsion G) t = 1 := (QuotientGroup.eq_one_iff t).2 ht
    rw [map_mul, h1, mul_one, powMonoidHom_apply, map_pow]
  · rintro ⟨q, hq⟩
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (CommGroup.torsion G) q
    have ht : (b ^ n)⁻¹ * x ∈ CommGroup.torsion G := by
      rw [← QuotientGroup.eq]
      rw [← map_pow] at hq
      exact hq
    have h := Subgroup.mul_mem_sup (S := (powMonoidHom n : G →* G).range)
      (T := CommGroup.torsion G) ⟨b, rfl⟩ ht
    rwa [powMonoidHom_apply, mul_inv_cancel_left] at h

instance finite_additive_quotient_torsion [Group.FG G] :
    Module.Finite ℤ (Additive (G ⧸ CommGroup.torsion G)) := by
  rw [Module.Finite.iff_addGroup_fg, AddGroup.fg_iff_addMonoid_fg, ← Monoid.fg_iff_add_fg,
    ← Group.fg_iff_monoid_fg]
  infer_instance

theorem index_range_powMonoidHom_eq_pow_mul [Group.FG G] {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : G →* G).range.index =
      n ^ finrank ℤ (Additive (G ⧸ CommGroup.torsion G)) *
        (powMonoidHom n : CommGroup.torsion G →* CommGroup.torsion G).range.index := by
  set T := CommGroup.torsion G
  set N := (powMonoidHom n : G →* G).range
  have hQ : (powMonoidHom n : G ⧸ T →* G ⧸ T).range.index =
      n ^ finrank ℤ (Additive (G ⧸ T)) :=
    AddSubgroup.index_range_nsmul (Additive (G ⧸ T)) n
  have hsup : (N ⊔ T).index = n ^ finrank ℤ (Additive (G ⧸ T)) := by
    rw [range_powMonoidHom_sup_torsion, Subgroup.index_comap_of_surjective _
      (QuotientGroup.mk'_surjective T), hQ]
  have hrel : N.relIndex T = (powMonoidHom n : T →* T).range.index := by
    rw [Subgroup.relIndex, range_powMonoidHom_subgroupOf_torsion hn]
  rw [← Subgroup.relIndex_mul_index (le_sup_left : N ≤ N ⊔ T), Subgroup.relIndex_sup_left, hrel,
    hsup, mul_comm]

end PowerIndex

section SUnit

variable {K : Type*} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))

namespace SUnit

theorem finrank_quotient_torsion [Finite S] :
    finrank ℤ (Additive (S.unit K ⧸ CommGroup.torsion (S.unit K))) = Units.rank K + Nat.card S := by
  rw [← finrank_eq S]
  exact finrank_quotient_torsion_eq (M := Additive (S.unit K))

theorem dvd_natCard_torsion (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n] :
    n ∣ Nat.card (CommGroup.torsion (S.unit K)) := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  set u : Kˣ := (hζ.isUnit (NeZero.ne n)).unit
  have hu : IsPrimitiveRoot u n := IsPrimitiveRoot.coe_units_iff.1 hζ
  have hfin : IsOfFinOrder u := by
    rw [← orderOf_pos_iff, ← hu.eq_orderOf]
    exact NeZero.pos n
  let u' : S.unit K := ⟨u, fun v _ ↦ valuation_eq_one_of_isOfFinOrder hfin v⟩
  have hfin' : IsOfFinOrder u' := by
    rw [← orderOf_pos_iff, ← orderOf_injective (S.unit K).subtype Subtype.val_injective]
    exact orderOf_pos_iff.mpr hfin
  let t : CommGroup.torsion (S.unit K) := ⟨u', hfin'⟩
  have ht : orderOf t = n := by
    rw [← orderOf_injective (CommGroup.torsion (S.unit K)).subtype Subtype.val_injective,
      ← orderOf_injective (S.unit K).subtype Subtype.val_injective]
    exact hu.eq_orderOf.symm
  rw [← ht]
  exact orderOf_dvd_natCard t

theorem index_range_powMonoidHom (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n] [Finite S] :
    (powMonoidHom n : S.unit K →* S.unit K).range.index =
      n ^ (Fintype.card (InfinitePlace K) + Nat.card S) := by
  have hpos : 0 < InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K := by
    rw [← InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
    exact Fintype.card_pos
  rw [index_range_powMonoidHom_eq_pow_mul (NeZero.ne n), finrank_quotient_torsion,
    IsCyclic.index_powMonoidHom_range, Nat.gcd_eq_right (dvd_natCard_torsion S n), ← pow_succ,
    Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  congr 1
  omega

end SUnit

end SUnit

end

end GroundTheory.Global
