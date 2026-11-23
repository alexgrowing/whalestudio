import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.BoundaryCreationAnticommutatorStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviActionUnitaryAdjointStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FiniteDimInvariantSubspaceAdjointPairStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LocallyFiniteLeviInvariantSubspaceStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HighestWeightVectorKilledByRaisingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.OrderedCreationCommutesPastLeviStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsOrderedCreationListStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CreationProductSingleBasisStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CreationProductSupportDegreeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviActionCommutesWithBoundaryStatement

noncomputable section

open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RgExh

theorem injU_of_injR : CompanionTheory.RgExh.U.InjR → CompanionTheory.RgExh.U.InjU := by
  intro hR n ε γ lev V _ _ E hG hE hU hL hM u y hu hy hd hb
  have hmono := hG.2.1
  have hsingle := GlobalTheory.T.highest_weight_vector_killed_by_raising n ε lev V E γ u hu
  obtain ⟨T, hTf, hyT, hTS, hTs⟩ := GlobalTheory.T.locally_finite_levi_invariant_subspace n ε lev V E _ y hL hy hd
  obtain ⟨y', hy'T, hy'0, hy'b⟩ := GlobalTheory.T.finite_dim_invariant_subspace_adjoint_pair n V
    {pq : Fin n × Fin n // pq.1 < pq.2 ∧ ε pq.1 = ε pq.2 ∧ lev pq.1 = lev pq.2} T
    (fun i => lF E i.1.1 i.1.2) (fun i => lF E i.1.2 i.1.1) (bd (allT n) E) y hTf
    (fun i x z => GlobalTheory.T.levi_action_unitary_adjoint n ε V E hU _ _ i.2.2.1 x z)
    (fun i t ht => hTs _ _ i.2.2.1 i.2.2.2 t ht)
    (fun i t ht => hTs _ _ i.2.2.1.symm i.2.2.2.symm t ht)
    (fun i t ht => GlobalTheory.T.levi_action_commutes_with_boundary n lev V E hmono hE _ _ i.2.2.2 t (hTS t ht).1)
    (fun i t ht => GlobalTheory.T.levi_action_commutes_with_boundary n lev V E hmono hE _ _ i.2.2.2.symm t (hTS t ht).1) hyT
    (fun i => by rw [hb]; exact hsingle _ _ i.2.1 i.2.2.1 i.2.2.2)
  obtain ⟨hy's, hy'd⟩ := hTS y' hy'T
  obtain ⟨l, hnd, hmem, hcl⟩ := GlobalTheory.T.exists_ordered_creation_list n ε lev hmono
  have hlc : ∀ e ∈ l, e.1.1 < e.1.2 ∧ ε e.1.1 = ε e.1.2 ∧ lev e.1.1 = lev e.1.2 := fun e he => by
    obtain ⟨h1, h2⟩ := (hmem e).1 he
    have hc : ε e.1.1 = ε e.1.2 := (Finset.mem_filter.1 h1).2
    refine ⟨e.2, hc, le_antisymm (hmono e.2.le) ?_⟩
    by_contra h3
    exact h2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hc, not_le.1 h3⟩)
  have hbd := GlobalTheory.T.ordered_creation_commutes_past_levi n V E (GlobalTheory.T.boundary_creation_anticommutator n V E) l y' hcl
    (fun e he => hy'0 ⟨e.1, hlc e he⟩)
  obtain ⟨c, hc0, hcw⟩ := GlobalTheory.T.creation_product_single_basis n V l (omU ε lev) u hnd (fun i hi => ((hmem i).1 hi).2)
  have hun : omU ε lev ∪ l.toFinset = om ε := by
    ext i
    simp only [Finset.mem_union, List.mem_toFinset, hmem]
    constructor
    · rintro (h | h)
      · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 h).2.1⟩
      · exact h.1
    · intro h
      by_cases h2 : i ∈ omU ε lev
      · exact Or.inl h2
      · exact Or.inr ⟨h, h2⟩
  have hcard : (om ε).card = (omU ε lev).card + l.length := by
    rw [← hun, Finset.card_union_of_disjoint, List.toFinset_card_of_nodup hnd]
    exact Finset.disjoint_left.2 fun i h1 h2 => ((hmem i).1 (List.mem_toFinset.1 h2)).2 h1
  obtain ⟨hs1, hs2⟩ := GlobalTheory.T.creation_product_support_degree n V (inR ε lev) l y' _ (fun i hi => Or.inl (hlc i hi).2.1)
    (fun A hA i hi => Or.inr (hy's A hA i hi)) hy'd
  set C : Cn n V := ((l.map cre).prod : Module.End ℂ (Cn n V)) y' with hC
  have hsm : ∀ (s : ℂ) (x : Cn n V) (A : Finset (Pos n)), s • x A ≠ 0 → x A ≠ 0 := fun s x A h h0 => h (by rw [h0, smul_zero])
  refine hR n ε γ lev V E hG hE hU hL hM u ((c⁻¹ * (-1 : ℂ) ^ l.length) • C) hu.1 ?_ ?_ ?_
  · exact fun A hA => hs1 A (hsm _ C A hA)
  · intro A hA
    have h3 := hs2 A (hsm _ C A hA)
    refine ⟨Finset.filter_false_of_mem fun _ _ h => h rfl, ?_⟩
    rw [Finset.filter_true_of_mem (fun _ _ => rfl), h3, hcard]
    omega
  · rw [map_smul, hC, hbd, hy'b, hb, hcw, hun, smul_smul, smul_smul]
    have h1 : ((-1 : ℂ) ^ l.length) * ((-1 : ℂ) ^ l.length) = 1 := by
      rw [← mul_pow]; simp
    have h2 : c⁻¹ * (-1 : ℂ) ^ l.length * (-1 : ℂ) ^ l.length * c = 1 := by
      rw [mul_assoc c⁻¹, h1, mul_one, inv_mul_cancel₀ hc0]
    rw [h2, one_smul]

end GlobalTheory.CompanionTheory.RgExh
