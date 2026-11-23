import Mathlib
import GroundTheory.ProfiniteCohomology.InflationRestriction.Higher
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolReal
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolNorm
import GroundTheory.TateCohomology.Characters
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

attribute [local instance 2000] Rep.hV2 Submodule.module Submodule.Quotient.module

section CyclicChar

variable (Q : Type) [Group Q] [Finite Q] [IsCyclic Q]

theorem exists_injective_addCircle_char : ∃ ψ : Additive Q →+ AddCircle (1 : ℚ), Function.Injective ψ := by
  have := Fintype.ofFinite Q
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Q)
  refine ⟨GroundTheory.GroupCoh.cyclicChar σ hσ, (injective_iff_map_eq_zero _).2 fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hσ (Additive.toMul x))
  have hxk : x = k • Additive.ofMul σ := by rw [← ofMul_zpow, hk, ofMul_toMul]
  rw [hxk, map_zsmul, GroundTheory.GroupCoh.cyclicChar_apply_gen] at hx
  have hn : (Nat.card Q : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have h' : (((k : ℚ) * (1 / Nat.card Q) : ℚ) : AddCircle (1 : ℚ)) = 0 := by
    rw [← zsmul_eq_mul]
    exact hx
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff _).1 h'
  rw [zsmul_one] at hm
  have hkm : k = m * (Nat.card Q : ℤ) := by
    have : (k : ℚ) = m * Nat.card Q := by
      field_simp at hm
      linarith
    exact_mod_cast this
  rw [hxk, hkm, mul_comm, ← ofMul_zpow, zpow_mul, zpow_natCast, pow_card_eq_one', one_zpow, ofMul_one]

end CyclicChar

section Main

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

theorem exists_cupCharClassProf_eq_of_cohomologyRes_eq_zero (A : Rep ℤ G) [IsDiscreteRep A]
    (N : Subgroup G) [N.Normal] (hN : IsOpen (N : Set G)) [IsCyclic (G ⧸ N)]
    (h1 : IsZero (cohomology (Rep.res N.subtype A) 1)) (x : cohomology A 2)
    (hx : (cohomologyRes A N 2).hom x = 0) :
    ∃ (χ : Additive G →ₜ+ QZ) (a : A.ρ.invariants), (∀ n ∈ N, χ (Additive.ofMul n) = 0) ∧
      (cupCharClassProf A χ).hom a = x := by
  have hNc : IsClosed (N : Set G) := Subgroup.isClosed_of_isOpen N hN
  have hmem : x ∈ LinearMap.range (cohomologyInfl A N 2).hom := by
    rw [range_cohomologyInfl_eq_ker_cohomologyRes hNc two_ne_zero]
    · exact hx
    · intro i hi hi2
      obtain rfl : i = 1 := by omega
      exact h1
  obtain ⟨y, rfl⟩ := hmem
  have : DiscreteTopology (G ⧸ N) := QuotientGroup.discreteTopology hN
  have : Finite (G ⧸ N) := Subgroup.quotient_finite_of_isOpen N hN
  have := Fintype.ofFinite (G ⧸ N)
  obtain ⟨ψ, hψ⟩ := exists_injective_addCircle_char (G ⧸ N)
  let χ₀ : Additive (G ⧸ N) →ₜ+ QZ :=
    { toAddMonoidHom := QZ.toAddCircle.symm.toAddMonoidHom.comp ψ
      continuous_toFun := continuous_of_discreteTopology }
  have hχ₀ : Function.Injective χ₀ := QZ.toAddCircle.symm.injective.comp hψ
  obtain ⟨a, rfl⟩ := cupCharClassProf_surjective (A.quotientToInvariants N) χ₀ hχ₀ y
  let f : Rep.res (QuotientGroup.mk' N) (A.quotientToInvariants N) ⟶ A :=
    Rep.ofHom (A.ρ.quotientToInvariants_lift N)
  let b : A.ρ.invariants := ⟨f.hom (a : A.quotientToInvariants N), fun g => by
    have hc := Rep.hom_comm_apply f g (a : A.quotientToInvariants N)
    rw [← hc]
    congr 1
    exact a.2 (QuotientGroup.mk' N g)⟩
  refine ⟨contCharComp χ₀ (QuotientGroup.mk' N) (continuous_quotientGroup_mk' N), b, fun n hn => ?_, ?_⟩
  · rw [contCharComp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).2 hn, ofMul_one, map_zero]
  · rw [cohomologyInfl_eq]
    exact (cohomologyMapAlong_cupCharClassProf (QuotientGroup.mk' N) (continuous_quotientGroup_mk' N) f χ₀
      a b rfl).symm

end Main

end GroundTheory.ProfCoh
