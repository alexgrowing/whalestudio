import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasString
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeSpehOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotientsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockIsTheRun
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GalDef.RunPart

open GlobalTheory.DefiniteBC

theorem map_le_spehInf (d k : ℕ) (hk : k < d) (m : Multiset ℂ) :
    m.map (· + (((d : ℂ) - 1) / 2 - k)) ≤ spehInf d m := by
  unfold spehInf
  exact List.le_sum_of_mem (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩)

theorem mem_infOfWeight {n : ℕ} (lam : DomWeight n) (x : ℂ) (hx : x ∈ infOfWeight lam) :
    ∃ j < n, x = (wAt lam j : ℂ) + (((n : ℂ) - 1) / 2 - (j : ℕ)) := by
  unfold infOfWeight at hx
  obtain ⟨k, -, rfl⟩ := Multiset.mem_map.1 hx
  refine ⟨k, k.2, ?_⟩
  simp [wAt, k.2]

theorem entry_of_run {n t : ℕ} (lam : DomWeight n) (p : ℕ) (hn : n < 2 * t) (hrun : IsRunAt lam p t)
    (d : ℕ) (m : Multiset ℂ) (hle : spehInf d m ≤ infOfWeight lam) (htd : t ≤ d) (z : ℂ) (hz : z ∈ m) :
    d = t ∧ z = (wAt lam p : ℂ) + ((n : ℂ) - 1) / 2 - (p : ℕ) - ((t : ℂ) - 1) / 2 := by
  obtain ⟨hpt, hconst, hleft, hright⟩ := hrun
  have hval : ∀ k < d, ∃ j < n,
      z + (((d : ℂ) - 1) / 2 - k) = (wAt lam j : ℂ) + (((n : ℂ) - 1) / 2 - (j : ℕ)) := fun k hk =>
    mem_infOfWeight lam _ (Multiset.mem_of_le hle
      (Multiset.mem_of_le (map_le_spehInf d k hk m) (Multiset.mem_map_of_mem _ hz)))
  have ht0 : 0 < t := by omega
  obtain ⟨j0, hj0, e0⟩ := hval 0 (by omega)
  set c : ℤ := wAt lam j0 - j0 with hc
  have hvalc : ∀ k < d, ∃ j < n, wAt lam j - (j : ℤ) = c - k := by
    intro k hk
    obtain ⟨j, hj, e⟩ := hval k hk
    refine ⟨j, hj, ?_⟩
    have : ((wAt lam j - (j : ℤ) : ℤ) : ℂ) = ((c - k : ℤ) : ℂ) := by
      rw [hc]; push_cast
      push_cast at e0 e
      linear_combination e0 - e
    exact_mod_cast this
  have hmono : ∀ i j, i ≤ j → j < n → wAt lam j ≤ wAt lam i := by
    intro i j hij hj
    simp only [wAt, hj, dif_pos, show i < n by omega]
    exact lam.anti (Fin.mk_le_mk.2 hij)
  have hB := fun (c' : ℤ) (h : ∀ i < t, ∃ j < n, wAt lam j - j = c' - i) =>
    GlobalTheory.block_is_the_run n p t (wAt lam) c' hmono hpt (by omega) (by omega) hconst hleft hright h
  have hcp : c = wAt lam p - p := hB c fun i hi => hvalc i (by omega)
  have hdt : d = t := by
    by_contra hne
    have := hB (c - 1) fun i hi => by
      obtain ⟨j, hj, e⟩ := hvalc (i + 1) (by omega)
      exact ⟨j, hj, by push_cast at e; linarith⟩
    omega
  refine ⟨hdt, ?_⟩
  have hc' : (c : ℂ) = (wAt lam p : ℂ) - (p : ℕ) := by rw [hcp]; push_cast; ring
  have : (c : ℂ) = (wAt lam j0 : ℂ) - (j0 : ℕ) := by rw [hc]; push_cast; ring
  subst hdt
  push_cast at e0
  linear_combination e0 - this + hc'

end GlobalTheory.GalDef.RunPart

open GlobalTheory.GalDef.RunPart in

theorem GlobalTheory.GalDef.spehPart_is_run : ∀ (n t : ℕ) (lam : DomWeight n) (p : ℕ), n < 2 * t → GlobalTheory.GalDef.IsRunAt lam p t →
  ∀ (c : ℕ) (d : Fin c → ℕ) (M : Fin c → Multiset ℂ), (∀ i, 1 ≤ d i) → (∀ i, M i ≠ 0) →
    ∑ i, spehInf (d i) (M i) = infOfWeight lam →
    ∀ i, t ≤ d i → d i = t ∧
      M i = {(GlobalTheory.GalDef.wAt lam p : ℂ) + ((n : ℂ) - 1) / 2 - (p : ℕ) - ((t : ℂ) - 1) / 2} ∧ ∀ j, j ≠ i → d j < t := by
  intro n t lam p hn hrun c d M hd hM hsum i hti
  have hle : ∀ j, spehInf (d j) (M j) ≤ infOfWeight lam := fun j => by
    rw [← hsum]
    exact Finset.single_le_sum (f := fun j => spehInf (d j) (M j)) (fun _ _ => Multiset.zero_le _) (Finset.mem_univ j)
  obtain ⟨z, hz⟩ := Multiset.exists_mem_of_ne_zero (hM i)
  obtain ⟨hdi, hzv⟩ := entry_of_run lam p hn hrun (d i) (M i) (hle i) hti z hz
  set v : ℂ := (wAt lam p : ℂ) + ((n : ℂ) - 1) / 2 - (p : ℕ) - ((t : ℂ) - 1) / 2 with hv
  have hall : ∀ z' ∈ M i, z' = v := fun z' hz' => (entry_of_run lam p hn hrun (d i) (M i) (hle i) hti z' hz').2
  have hnd : ∀ j, (spehInf (d j) (M j)).Nodup := fun j =>
    Multiset.nodup_of_le (hle j) (nodup_infOfWeight lam)
  refine ⟨hdi, ?_, ?_⟩
  · have hnodup : (M i).Nodup :=
      (Multiset.nodup_of_le (map_le_spehInf (d i) 0 (by omega) (M i)) (hnd i)).of_map _
    rw [Multiset.eq_replicate.2 ⟨rfl, hall⟩] at hnodup ⊢
    have hc1 : Multiset.card (M i) ≤ 1 := by
      by_contra h
      push_neg at h
      obtain ⟨k, hk⟩ : ∃ k, Multiset.card (M i) = k + 2 := ⟨Multiset.card (M i) - 2, by omega⟩
      rw [hk, Multiset.replicate_succ, Multiset.replicate_succ, Multiset.nodup_cons] at hnodup
      exact hnodup.1 (Multiset.mem_cons_self _ _)
    have hc0 : Multiset.card (M i) ≠ 0 := fun h => hM i (Multiset.card_eq_zero.1 h)
    rw [show Multiset.card (M i) = 1 by omega, Multiset.replicate_one]
  · intro j hji
    by_contra hlt
    push_neg at hlt
    obtain ⟨z', hz'⟩ := Multiset.exists_mem_of_ne_zero (hM j)
    obtain ⟨hdj, hz'v⟩ := entry_of_run lam p hn hrun (d j) (M j) (hle j) hlt z' hz'
    have ht0 : 0 < t := by omega
    have hmem : ∀ k, 0 < d k → ∀ w ∈ M k, w + (((d k : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ)) ∈ spehInf (d k) (M k) :=
      fun k hk w hw => Multiset.mem_of_le (map_le_spehInf (d k) 0 hk (M k)) (Multiset.mem_map_of_mem _ hw)
    have hpair : spehInf (d i) (M i) + spehInf (d j) (M j) ≤ infOfWeight lam := by
      rw [← hsum]
      calc spehInf (d i) (M i) + spehInf (d j) (M j) = ∑ k ∈ {i, j}, spehInf (d k) (M k) :=
            (Finset.sum_pair (f := fun k => spehInf (d k) (M k)) hji.symm).symm
        _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have hdis := (Multiset.nodup_add.1 (Multiset.nodup_of_le hpair (nodup_infOfWeight lam))).2.2
    have h1 := hmem i (by omega) z hz
    have h2 := hmem j (by omega) z' hz'
    rw [hdi, hzv] at h1
    rw [hdj, hz'v] at h2
    rw [hdi, hdj] at hdis
    exact Multiset.disjoint_left.1 hdis h1 h2
