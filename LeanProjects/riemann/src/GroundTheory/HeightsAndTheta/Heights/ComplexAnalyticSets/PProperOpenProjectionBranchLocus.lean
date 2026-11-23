import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProperOpenProjectionBranchLocus
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProperOpenProjectionLocalCover
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFibreDiscriminantHolomorphic
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StMaximalCountUnbranched
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem ProperOpenProjectionBranchLocus.proof (hL : ProperOpenProjectionLocalCover.Statement)
    (hH : FibreDiscriminantHolomorphic.Statement) (hM : MaximalCountUnbranched.Statement) :
    ProperOpenProjectionBranchLocus.Statement := by
  intro σ _ X B k f d A D hB hf hXB hDo hDc hDne hmaps hprop hopen
  have loc := hL σ X B k f d A D hB hf hXB hDo hmaps hprop hopen
  choose! U g n hUo hyU hUD hg hgd hle hgen using loc

  have key : ∀ y₀ ∈ D, ∀ y ∈ U y₀, n y = n y₀ := by
    intro y₀ hy₀ y hy
    have hyD : y ∈ D := hUD y₀ hy₀ hy
    obtain ⟨t₁, ht₁, hgt₁⟩ := hgd y₀ hy₀ (U y ∩ U y₀) ((hUo y hyD).inter (hUo y₀ hy₀))
      Set.inter_subset_right ⟨y, hyU y hyD, hy⟩
    have hWo : IsOpen (U y ∩ (U y₀ ∩ g y₀ ⁻¹' {0}ᶜ)) :=
      (hUo y hyD).inter ((hg y₀ hy₀).continuousOn.isOpen_inter_preimage (hUo y₀ hy₀) isOpen_compl_singleton)
    obtain ⟨t, ht, hgt⟩ := hgd y hyD _ hWo Set.inter_subset_left
      ⟨t₁, ht₁.1, ht₁.2, by simpa using hgt₁⟩
    have e1 := (hgen y hyD t ht.1 hgt).1
    have e2 := (hgen y₀ hy₀ t ht.2.1 (by simpa using ht.2.2)).1
    exact_mod_cast e1.symm.trans e2
  obtain ⟨y₀, hy₀⟩ := hDne
  have hcont : ContinuousOn n D := by
    intro y hy
    have hc0 : ContinuousAt (fun _ : Fin d → ℂ => n y) y := continuousAt_const
    have hca : ContinuousAt n y := by
      refine hc0.congr ?_
      filter_upwards [(hUo y hy).mem_nhds (hyU y hy)] with z hz
      exact (key y hy z hz).symm
    exact hca.continuousWithinAt
  have hN : ∀ y ∈ D, n y = n y₀ := fun y hy => hDc.constant hcont hy hy₀

  have hcov : IsGenericCountCover (X ∩ B) A D (n y₀) := by
    refine ⟨fun y hy => ?_, fun y hy => ⟨U y, g y, hUo y hy, hyU y hy, hUD y hy, hg y hy, hgd y hy,
      fun z hz hgz => ?_⟩⟩
    · have := hle y hy y (hyU y hy)
      rwa [hN y hy] at this
    · obtain ⟨h1, h2⟩ := hgen y hy z hz hgz
      exact ⟨by rw [h1, hN y hy], h2⟩

  obtain ⟨ys, hysU, hgys⟩ := hgd y₀ hy₀ (U y₀) (hUo y₀ hy₀) subset_rfl ⟨y₀, hyU y₀ hy₀⟩
  have hysD : ys ∈ D := hUD y₀ hy₀ hysU
  have hcys : {x | x ∈ X ∩ B ∧ A x = ys}.encard = (n y₀ : ℕ∞) := (hgen y₀ hy₀ ys hysU hgys).1
  have hfin := Set.finite_of_encard_eq_coe hcys
  obtain ⟨l₀, hl₀⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℂ)
    (fun p : hfin.toFinset.offDiag => (p.1.1 - p.1.2 : σ → ℂ))
    (fun p => sub_ne_zero.2 (Finset.mem_offDiag.1 p.2).2.2)
  let l : (σ → ℂ) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap l₀
  refine ⟨fibreDiscr (X ∩ B) A l (n y₀), hH σ (X ∩ B) d A D (n y₀) l hDo hmaps hprop hopen hcov,
    ⟨ys, hysD, ?_⟩, ?_⟩
  · unfold fibreDiscr
    rw [dif_pos hcys, Finset.prod_ne_zero_iff]
    intro p hp
    have := hl₀ ⟨p, hp⟩
    simpa [l, map_sub, sub_eq_zero] using this
  · intro x hx hδ
    have hc : {x' | x' ∈ X ∩ B ∧ A x' = A x}.encard = (n y₀ : ℕ∞) := by
      by_contra hne
      exact hδ (by unfold fibreDiscr; rw [dif_neg hne])
    exact hM σ (X ∩ B) d A D (n y₀) hDo hmaps hprop hopen hcov x hx hc

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
