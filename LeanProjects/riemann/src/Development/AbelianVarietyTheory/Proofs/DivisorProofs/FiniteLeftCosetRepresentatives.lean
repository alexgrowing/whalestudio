import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySimilitudeIntegralSubgroupCommensuratedFrStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinCmd

theorem exists_finset_mul_eq_of_relIndex {H : Type} [Group H] (K : Subgroup H) (s : H)
    (h : (K.map (MulAut.conj s).toMonoidHom).relIndex K ≠ 0) :
    ∃ S : Finset H, ∀ k ∈ K, ∃ s' ∈ S, ∃ k' ∈ K, k * s = s' * k' := by
  set L := K.map (MulAut.conj s).toMonoidHom with hL
  haveI : Finite (K ⧸ L.subgroupOf K) := by
    haveI : (L.subgroupOf K).FiniteIndex := ⟨h⟩
    exact Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (K ⧸ L.subgroupOf K) := Fintype.ofFinite _
  refine ⟨Finset.univ.image fun q : K ⧸ L.subgroupOf K => ((Quotient.out q : K) : H) * s, ?_⟩
  intro k hk
  set q : K ⧸ L.subgroupOf K := QuotientGroup.mk ⟨k, hk⟩
  have hq : (Quotient.out q)⁻¹ * (⟨k, hk⟩ : K) ∈ L.subgroupOf K := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  rw [Subgroup.mem_subgroupOf] at hq
  obtain ⟨x, hx, hxe⟩ := hq
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at hxe
  refine ⟨((Quotient.out q : K) : H) * s, Finset.mem_image_of_mem _ (Finset.mem_univ _), x, hx, ?_⟩
  have : k = ((Quotient.out q : K) : H) * (s * x * s⁻¹) := by
    rw [hxe, mul_inv_cancel_left]
  rw [this]
  group

end GlobalTheory.OrbFinCmd

open GlobalTheory.OrbFinCmd in

theorem GlobalTheory.orbFin_KHT_cmd :
    ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r → ∀ s : Gr G r, ∃ S : Finset (Gr G r),
      ∀ k ∈ KHT p G.m G.n r G.Fw, ∃ s' ∈ S, ∃ k' ∈ KHT p G.m G.n r G.Fw, k * s = s' * k' := by
  intro p _ G r hr s
  exact exists_finset_mul_eq_of_relIndex _ s ((GlobalTheory.T.unitarySimilitudeIntegralSubgroup_commensurated_frobenius p G r hr).1 s).1
