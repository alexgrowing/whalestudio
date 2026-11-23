import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictHomApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPurePairIffMonodromyFiltration

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.PrimDecomp
  GlobalTheory.LocLanglands Module

namespace GlobalTheory.WeilDeligne.PrimDecomp

theorem isCompl_strand_lowPart (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (U : ℤ → Submodule ℂ V) (N : Module.End ℂ V) (m : ℕ) (hi : iSupIndep U)
    (ht : ⨆ i, U i = ⊤) (hN : ∀ d, ∀ v ∈ U d, N v ∈ U (d + 2))
    (hb : ∀ i : ℕ, Set.BijOn (N ^ i) (U (-(i : ℤ))) (U i))
    (hm : ∀ k : ℤ, (m : ℤ) < k → U k = ⊥) :
    IsCompl (strand N (U (-(m : ℤ))) m) (lowPart U N m) := by
  obtain ⟨p, h1, h2, h3, h4⟩ := exists_proj_of_iSupIndep hi ht
  have hhigh : ∀ d : ℤ, (m : ℤ) < d → ∀ v ∈ U d, v = 0 := fun d hd v hv => by
    rw [hm d hd] at hv; exact (Submodule.mem_bot ℂ).mp hv
  have hlow : ∀ d : ℤ, d < -(m : ℤ) → ∀ v ∈ U d, v = 0 := by
    intro d hd v hv
    refine eq_zero_of_pow_eq_zero hb (m := (-d).toNat) (by omega) hv ?_
    exact hhigh (-d) (by omega) _ (pow_mem_of_degree_two hN (-d).toNat (by omega) hv)
  have fC : ∀ x ∈ lowPart U N m, ∀ d, (N ^ (((m : ℤ) - d + 1) / 2).toNat) (p d x) = 0 := by
    intro x hx d
    unfold lowPart at hx
    induction hx using Submodule.iSup_induction' with
    | mem k y hy =>
      by_cases hk : k = d
      · subst hk; rw [h2 k y hy.1]; exact hy.2
      · rw [h3 d k hk y hy.1, map_zero]
    | zero => simp
    | add y z _ _ hy hz => rw [map_add, map_add, hy, hz, add_zero]
  have fB : ∀ x ∈ strand N (U (-(m : ℤ))) m, ∀ d, ∃ u ∈ U (-(m : ℤ)),
      p d x = (N ^ ((d + m) / 2).toNat) u ∧ (d = -m + 2 * (((d + m) / 2).toNat : ℤ) ∨ u = 0) := by
    intro x hx d
    unfold strand at hx
    induction hx using Submodule.iSup_induction' with
    | mem j y hy =>
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hy
      have hjw := pow_mem_of_degree_two hN (j : ℕ) rfl hw
      by_cases hd : d = -(m : ℤ) + 2 * ((j : ℕ) : ℤ)
      · refine ⟨w, hw, ?_, Or.inl (by omega)⟩
        rw [h2 d _ (hd ▸ hjw)]
        have : ((d + m) / 2).toNat = (j : ℕ) := by omega
        rw [this]
      · refine ⟨0, zero_mem _, ?_, Or.inr rfl⟩
        rw [h3 d _ (fun h => hd h.symm) _ hjw, map_zero]
    | zero => exact ⟨0, zero_mem _, by simp, Or.inr rfl⟩
    | add y z _ _ hy hz =>
      obtain ⟨u1, hu1, e1, o1⟩ := hy
      obtain ⟨u2, hu2, e2, o2⟩ := hz
      refine ⟨u1 + u2, add_mem hu1 hu2, by rw [map_add, e1, e2, map_add], ?_⟩
      rcases o1 with o1 | o1
      · exact Or.inl o1
      · rcases o2 with o2 | o2
        · exact Or.inl o2
        · right; rw [o1, o2, add_zero]
  constructor
  · rw [Submodule.disjoint_def]
    intro x hB hC
    refine h4 ⊥ x fun d => ?_
    rw [Submodule.mem_bot]
    by_cases hdm : (m : ℤ) < d
    · exact hhigh d hdm _ (h1 d x)
    obtain ⟨u, hu, e, o⟩ := fB x hB d
    rcases o with o | o
    · have h5 := fC x hC d
      rw [e, ← End.mul_apply, ← pow_add] at h5
      have hs : (((m : ℤ) - d + 1) / 2).toNat + ((d + m) / 2).toNat = m := by omega
      rw [hs] at h5
      rw [e, eq_zero_of_pow_eq_zero hb (d := -(m : ℤ)) (m := m) (by omega) hu h5, map_zero]
    · rw [e, o, map_zero]
  · rw [codisjoint_iff, eq_top_iff, ← ht]
    refine iSup_le fun d v hv => ?_
    by_cases hdm : (m : ℤ) < d
    · rw [hhigh d hdm v hv]; exact zero_mem _
    by_cases hdl : d < -(m : ℤ)
    · rw [hlow d hdl v hv]; exact zero_mem _
    set e := (((m : ℤ) - d + 1) / 2).toNat with he
    have hC : ∀ w ∈ U d, (N ^ e) w = 0 → w ∈ lowPart U N m := fun w hw h0 => by
      unfold lowPart
      exact Submodule.mem_iSup_of_mem d ⟨hw, h0⟩
    by_cases hpar : d + 2 * (e : ℤ) = m + 1
    · apply Submodule.mem_sup_right
      refine hC v hv (hhigh _ (by omega : (m : ℤ) < m + 1) _ ?_)
      exact pow_mem_of_degree_two hN e hpar.symm hv
    · have hw : (N ^ e) v ∈ U m := pow_mem_of_degree_two hN e (by omega) hv
      obtain ⟨u, hu, hu'⟩ := exists_pow_eq hN hb (m := m) (d := m) (e := -(m : ℤ)) le_rfl
        (by ring) hw
      set j := ((d + m) / 2).toNat with hjdef
      have hjm : j < m + 1 := by omega
      have hNj : (N ^ j) u ∈ strand N (U (-(m : ℤ))) m := by
        unfold strand
        exact Submodule.mem_iSup_of_mem (⟨j, hjm⟩ : Fin (m + 1)) ⟨u, hu, rfl⟩
      have hv' : v = (N ^ j) u + (v - (N ^ j) u) := by abel
      rw [hv']
      refine Submodule.add_mem_sup hNj (hC _ (sub_mem hv (pow_mem_of_degree_two hN j (by omega) hu)) ?_)
      rw [map_sub, ← End.mul_apply, ← pow_add, show e + j = m by omega, hu', sub_self]

end GlobalTheory.WeilDeligne.PrimDecomp
