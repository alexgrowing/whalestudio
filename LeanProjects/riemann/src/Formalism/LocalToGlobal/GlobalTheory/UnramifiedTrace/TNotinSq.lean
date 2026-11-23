import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.MulLatSupSpan
import Formalism.LocalToGlobal.GlobalTheory.GL6.BwAValIntegralNonneg
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CrossDiagonalMatching.DnkLkLocP

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

variable {D : D7} {u : D.what₂.Word}

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem t_notin_sq (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) :
    (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ T.atT.Pv v ^ 2 := by
  intro hT
  obtain ⟨x0, hx0⟩ : ∃ x0, (D.fm u).fv 0 v c x0 ≠ 0 := by
    by_contra h
    apply (D.fm u).fv_ne 0 v c
    ext x0
    by_contra hx
    exact h ⟨x0, by rwa [LinearMap.zero_apply] at hx⟩
  obtain ⟨z, hz⟩ := T.lv0.pr_surj v c (((D.fm u).fv 0 v c x0)⁻¹ • x0)
  have hx : (D.fm u).fv 0 v c (T.lv0.pr v c z) = 1 := by
    rw [hz, map_smul, smul_eq_mul, inv_mul_cancel₀ hx0]
  have hTz : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c :=
    Submodule.mem_sup_left (CrossDiaZero.dnk_tld T c z.1 z.2)
  have hte := T.lv0.te v c z hx hTz
  have hsq : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z.1 ∈ T.atT.Pv v • Lk T.atT 0 (Nat.zero_le _) v c := by
    have h1 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z.1 ∈ (T.atT.Pv v ^ 2) • Ld D u 0 (Nat.zero_le _) c :=
      Submodule.smul_mem_smul hT z.2
    rw [pow_two, Submodule.mul_smul] at h1
    exact Submodule.smul_mono le_rfl le_sup_right h1
  have h0 := (T.lv0.prk_ker v c ⟨_, hTz⟩).2 hsq
  rw [hte] at h0
  exact (D.fm u).te_ne 0 v c h0

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem exists_not_mem_Pv_mul_mem_span_T (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) :
    ∃ s : 𝓞 D.host.E, s ∉ T.atT.Pv v ∧ ∀ p ∈ T.atT.Pv v, ∃ e : 𝓞 D.host.E,
      s * p = e * (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) := by
  have hle : Ideal.span {(((D.mem u).A.T : ℕ) : 𝓞 D.host.E)} ≤ T.atT.Pv v :=
    (Ideal.span_singleton_le_iff_mem _).2 (bwA_T_mem_Pv (D := D) (u := u) (A := T.atT) (v := v))
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle
  have hJP : ¬ J ≤ T.atT.Pv v := by
    intro h
    apply t_notin_sq T v c
    have h2 : Ideal.span {(((D.mem u).A.T : ℕ) : 𝓞 D.host.E)} ≤ T.atT.Pv v ^ 2 := by
      rw [hJ, pow_two]; exact Ideal.mul_mono_right h
    exact h2 (Ideal.subset_span rfl)
  obtain ⟨s, hsJ, hsP⟩ := Set.not_subset.1 hJP
  refine ⟨s, hsP, fun p hp => ?_⟩
  have hm : s * p ∈ Ideal.span {(((D.mem u).A.T : ℕ) : 𝓞 D.host.E)} := by
    rw [hJ, mul_comm s p]; exact Ideal.mul_mem_mul hp hsJ
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 hm
  exact ⟨e, he.symm⟩

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end
