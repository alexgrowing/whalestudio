import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

theorem UpperTheory.Gal.productCup_of_system.kSub_of :
    FiltrationBoundaryCriterion → SubQEx → KSub := by
  intro gl sub S E _ _ _ _ act κ _ _ R M r hst hr
  refine ⟨?_, ?_⟩
  · intro d e hK m hm c hc
    have hW : WOk (fun _ : Finset κ => M) (fun l => act (r l)) := by
      refine ⟨fun i j => ?_, fun s i _ x hx => hst _ (hr i) x hx⟩
      show act (r i) * act (r j) = act (r j) * act (r i)
      rw [← map_mul, ← map_mul, mul_comm]
    have hQ := sub S E act κ M r d e hK
    have hcard : (img e).card = d := by simp [img]
    refine gl κ E (fun _ => M) (fun l => act (r l)) (img e) d m hW hQ c hc ?_
      ⟨0, Submodule.zero_mem _, fun _ _ => rfl, ?_⟩
    · intro s hs
      exfalso
      apply hs
      have h1 : (s ∩ img e).card ≤ (img e).card := Finset.card_le_card Finset.inter_subset_right
      rw [hcard] at h1
      exact_mod_cast h1
    · intro s hs
      have h1 : (s ∩ img e).card ≤ s.card := Finset.card_le_card Finset.inter_subset_left
      have hne : (s.card : ℤ) ≠ m := by
        have : ((s ∩ img e).card : ℤ) ≤ s.card := by exact_mod_cast h1
        omega
      have h2 : c s ∈ (if (s.card : ℤ) = m then M else ⊥ : Submodule ℂ E) := hc.1 s (Set.mem_univ s)
      rw [if_neg hne, Submodule.mem_bot] at h2
      rw [h2, map_zero]
      rfl
  · intro n c hc L
    obtain ⟨y, hy, rfl⟩ := hc
    have hval : ∀ i ∈ L, y (L.erase i) ∈ M := by
      intro i _
      have h2 : y (L.erase i) ∈ (if ((L.erase i).card : ℤ) = n - 1 then M else ⊥ : Submodule ℂ E) :=
        hy (L.erase i) (Set.mem_univ _)
      split_ifs at h2 with h
      · exact h2
      · rw [Submodule.mem_bot] at h2
        rw [h2]
        exact M.zero_mem
    have hexp : (kos act M r).D y L
        = ∑ i ∈ L, (GlobalTheory.cubeSign L i : ℤ) • act (r i) (y (L.erase i)) := by
      simp [kos, acx, wd]
    rw [hexp]
    refine Submodule.sum_mem _ fun i hi => ?_
    refine Submodule.smul_of_tower_mem _ _ ?_
    have h3 : act (r i) (y (L.erase i)) ∈ M.map (act (r i)) := ⟨_, hval i hi, rfl⟩
    exact (le_iSup₂_of_le (r i) (Set.mem_range_self i) le_rfl : M.map (act (r i)) ≤ sm act M (Set.range r)) h3
