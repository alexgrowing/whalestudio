import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsClaimSeq
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PClaimVanishCech
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section ClaimLemmas

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem coordGraded_tilde_mem_chartRing {I : Chart x} {y : Ω}
    (hy : y ∈ (coordGraded k x).tilde 0 I) : y ∈ chartRing k x I := by
  refine Submodule.span_induction (p := fun y _ => y ∈ chartRing k x I) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
    have hm' : m ∈ Submodule.span k {z | ∃ (f : Poly k N) (e' : ℕ), f.IsHomogeneous e' ∧
        (e' : ℤ) = a ∧ z = aeval x f} := hm
    refine Submodule.span_induction (p := fun m _ => (aeval x s)⁻¹ • m ∈ chartRing k x I)
      ?_ ?_ ?_ ?_ hm'
    · rintro _ ⟨f, e', hf, he', rfl⟩
      have hee : e' = e := by omega
      subst hee
      exact ⟨f, s, e', hs, hf, hse, by rw [smul_eq_mul, div_eq_inv_mul]⟩
    · rw [smul_zero]; exact (chartRing k x I).zero_mem
    · intro a b _ _ ha hb; rw [smul_add]; exact (chartRing k x I).add_mem ha hb
    · intro r a _ ha; rw [smul_comm]; exact (chartRing k x I).smul_mem ha r
  · exact (chartRing k x I).zero_mem
  · intro a b _ _ ha hb; exact (chartRing k x I).add_mem ha hb
  · intro a y _ hy; rw [chartRing_smul_def]; exact (chartRing k x I).mul_mem a.2 hy

theorem coordGraded_tildeSys_twist (X : SubSystem k x Ω) :
    ((coordGraded k x).tildeSys 0).twist X = X := by
  refine SubSystem.ext_sub fun I => le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    have hyA := coordGraded_tilde_mem_chartRing hy
    have hqy : q • y = (⟨y, hyA⟩ : chartRing k x I) • q := by
      rw [smul_eq_mul, chartRing_smul_def, mul_comm]
    rw [SetLike.mem_coe, hqy]
    exact (X.sub I).smul_mem _ hq
  · intro q hq
    refine Submodule.subset_span ⟨q, hq, 1, ?_, by rw [smul_eq_mul, mul_one]⟩
    exact Submodule.subset_span ⟨1, 1, 0, 0, one_mem _, isHomogeneous_one _ _,
      Submodule.subset_span ⟨1, 0, isHomogeneous_one _ _, by simp, by simp⟩, by simp, by simp⟩

theorem twist_tildeSys_mono {M₁ M₂ : FinGradedSub (S := k) (x := x) Ω}
    (h : ∀ c, M₂.piece c ≤ M₁.piece c) (X : SubSystem k x Ω) (I : Chart x) :
    ∀ y ∈ ((M₂.tildeSys 0).twist X).sub I, y ∈ ((M₁.tildeSys 0).twist X).sub I := by
  intro y hy
  refine Submodule.span_mono ?_ hy
  rintro _ ⟨q, hq, z, hz, rfl⟩
  refine ⟨q, hq, z, Submodule.span_mono ?_ hz, rfl⟩
  rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
  exact ⟨m, s, a, e, hs, hse, h a hm, hae, rfl⟩

variable (T : StepData k x) (Jg : FinGradedSub (S := k) (x := x) Ω)
  (hJg : ∀ c : ℤ, Jg.piece c = Submodule.span k {z | ∃ (f : Poly k N) (e : ℕ), f ∈ T.J ∧
    f.IsHomogeneous e ∧ (e : ℤ) = c ∧ z = aeval x f})

include hJg in

theorem claim_le : ∀ c, Jg.piece c ≤ (coordGraded k x).piece c := by
  intro c
  rw [hJg]
  refine Submodule.span_mono ?_
  rintro _ ⟨f, e, -, hf, he, rfl⟩
  exact ⟨f, e, hf, he, rfl⟩

include hJg in

theorem claim_kill : ∀ (f : Poly k N) (e : ℕ), f ∈ T.J → f.IsHomogeneous e → ∀ (a : ℤ),
    ∀ z ∈ (coordGraded k x).piece a, aeval x f • z ∈ Jg.piece (a + e) := by
  intro f e hf hfe a z hz
  have hz' : z ∈ Submodule.span k {z | ∃ (g : Poly k N) (e' : ℕ), g.IsHomogeneous e' ∧
      (e' : ℤ) = a ∧ z = aeval x g} := hz
  refine Submodule.span_induction (p := fun z _ => aeval x f • z ∈ Jg.piece (a + e)) ?_ ?_ ?_ ?_ hz'
  · rintro _ ⟨g, e', hg, he', rfl⟩
    rw [hJg]
    exact Submodule.subset_span ⟨f * g, e + e', T.J.mul_mem_right g hf, hfe.mul hg,
      by push_cast; omega, by rw [map_mul, smul_eq_mul]⟩
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
  · intro r a _ ha; rw [smul_comm]; exact Submodule.smul_mem _ r ha

end ClaimLemmas

theorem ClaimVanish.proof (h₁ : StepTwo.Statement.{u, w, w}) (h₂ : TwistVanish.Statement.{u, w})
    (h₃ : ClaimSeq.Statement.{u, w}) : ClaimVanish.Statement.{u, w} := by
  intro k _ Ω _ _ N x T hK
  obtain ⟨Jg, hJg, hseq⟩ := h₃ k Ω N x T
  obtain ⟨cS, hS⟩ := h₁ k Ω N x T hK Ω (coordGraded k x) Jg (claim_le T Jg hJg)
    (claim_kill T Jg hJg)
  obtain ⟨cB, hB⟩ := h₂ k Ω N x (twistBundle k x 0) (twistBundle k x 1) N x (twist_hyps k N x).1
    (twist_hyps k N x).2
  refine ⟨max cS cB, fun b => ?_⟩
  induction b with
  | zero =>
    intro c hc
    have h0 := hB 0 c (le_trans (le_max_right _ _) hc)
    have e : ((twistBundle k x 0).twist ((twistBundle k x 1).pow 0)).twist (twistSys k x c) =
        (T.L.pow 0).twist (twistSys k x c) := by
      show ((twistSys k x 0).twist (twistSys k x 0)).twist (twistSys k x c) =
        (twistSys k x 0).twist (twistSys k x c)
      rw [twistSys_zero_twist]
    rw [e] at h0
    exact h0
  | succ b ih =>
    intro c hc
    have hq := hS (b + 1) c (le_trans (le_max_left _ _) hc)
    rw [coordGraded_tildeSys_twist] at hq
    refine SubSystem.subsingleton_H_one_of_quot _
      ((Jg.tildeSys 0).twist ((T.L.pow (b + 1)).twist (twistSys k x c))) ?_ ?_ hq
    · intro I y hy
      have hy' := twist_tildeSys_mono (claim_le T Jg hJg) _ I y hy
      rwa [coordGraded_tildeSys_twist] at hy'
    · exact SubSystem.subsingleton_H_one_of_smul _ _ T.si T.si_ne (hseq b c)
        (ih (c + T.c₁) (le_trans hc (by linarith [T.c₁_pos])))

end

end GroundTheory.Heights₂.Heights.Kleiman
