import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionMulInjSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepThreeAway
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepThreeOnWGen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace SectionMulInj

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem exists_of_mem_idealMod (J : Ideal (Poly S N)) (I : Chart x) {z : Ω} (hz : z ∈ idealMod (x := x) J I) :
    ∃ (G m : Poly S N) (e : ℕ), G ∈ J ∧ m ∈ monos I.1 ∧ G.IsHomogeneous e ∧ m.IsHomogeneous e ∧
      z = aeval x G / aeval x m := by
  induction hz using Submodule.span_induction with
  | mem z hz => exact hz
  | zero => exact ⟨0, 1, 0, J.zero_mem, one_mem _, isHomogeneous_zero _ _ _, isHomogeneous_one _ _, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨G, m, e, hG, hm, hGe, hme, rfl⟩ := ha
    obtain ⟨G', m', e', hG', hm', hGe', hme', rfl⟩ := hb
    refine ⟨G * m' + m * G', m * m', e + e', J.add_mem (J.mul_mem_right _ hG) (J.mul_mem_left _ hG'),
      mul_mem hm hm', (hGe.mul hme').add (hme.mul hGe'), hme.mul hme', ?_⟩
    rw [div_add_div _ _ (eval_ne_zero_of_mem_monos I hm) (eval_ne_zero_of_mem_monos I hm')]
    simp only [map_add, map_mul]
  | smul r a _ ha =>
    obtain ⟨F, m₀, e₀, hm₀, hF, hm₀e, hr⟩ := r.2
    obtain ⟨G, m, e, hG, hm, hGe, hme, rfl⟩ := ha
    refine ⟨F * G, m₀ * m, e₀ + e, J.mul_mem_left _ hG, mul_mem hm₀ hm, hF.mul hGe, hm₀e.mul hme, ?_⟩
    rw [chartRing_smul_def, hr, map_mul, map_mul, div_mul_div_comm]

omit [Algebra S Ω] in

theorem not_mem_of_mem_monos {pp : Ideal (Poly S N)} (hpp : pp.IsPrime) {I : Chart x}
    (hX : ∀ j ∈ I.1, (X j : Poly S N) ∉ pp) {m : Poly S N} (hm : m ∈ monos I.1) : m ∉ pp := by
  induction hm using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨j, hj, rfl⟩ := ha
    exact hX j (by exact_mod_cast hj)
  | one => exact fun h => hpp.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  | mul a b _ _ ha hb => exact fun h => (hpp.mem_or_mem h).elim ha hb

theorem mem_of_div_mem_idealMod {pp : Ideal (Poly S N)} (hpp : pp.IsPrime) (hZ : primeOf (S := S) x ≤ pp)
    {I : Chart x} (hX : ∀ j ∈ I.1, (X j : Poly S N) ∉ pp) {F m : Poly S N} {e : ℕ} (hm : m ∈ monos I.1)
    (hF : F.IsHomogeneous e) (hme : m.IsHomogeneous e) (h : aeval x F / aeval x m ∈ idealMod (x := x) pp I) :
    F ∈ pp := by
  obtain ⟨G, m', e', hG, hm', hGe, hme', heq⟩ := exists_of_mem_idealMod pp I h
  have h0 := eval_ne_zero_of_mem_monos I hm
  have h0' := eval_ne_zero_of_mem_monos I hm'
  have hdiff : F * m' - m * G ∈ primeOf (S := S) x := by
    have hhom : (F * m' - m * G).IsHomogeneous (e + e') := (hF.mul hme').sub (hme.mul hGe)
    rw [mem_primeOf_of_isHomogeneous x hhom, map_sub, map_mul, map_mul, sub_eq_zero]
    rw [div_eq_div_iff h0 h0'] at heq
    rw [heq, mul_comm]
  have hFm : F * m' ∈ pp := by
    have := pp.add_mem (hZ hdiff) (pp.mul_mem_left m hG)
    rwa [sub_add_cancel] at this
  exact (hpp.mem_or_mem hFm).resolve_right (not_mem_of_mem_monos hpp hX hm')

theorem mem_or_mem {pp : Ideal (Poly S N)} (hpp : pp.IsPrime) (hZ : primeOf (S := S) x ≤ pp)
    {I : Chart x} (hX : ∀ j ∈ I.1, (X j : Poly S N) ∉ pp) (a b : chartRing S x I)
    (h : (a : Ω) * b ∈ idealMod (x := x) pp I) :
    (a : Ω) ∈ idealMod (x := x) pp I ∨ (b : Ω) ∈ idealMod (x := x) pp I := by
  obtain ⟨F, m, e, hm, hF, hme, ha⟩ := a.2
  obtain ⟨F', m', e', hm', hF', hme', hb⟩ := b.2
  rw [ha, hb, div_mul_div_comm, ← map_mul, ← map_mul] at h
  have := mem_of_div_mem_idealMod hpp hZ hX (mul_mem hm hm') (hF.mul hF') (hme.mul hme') h
  refine (hpp.mem_or_mem this).imp (fun hF0 => ?_) (fun hF0 => ?_)
  · rw [ha]; exact Submodule.subset_span ⟨F, m, e, hF0, hm, hF, hme, rfl⟩
  · rw [hb]; exact Submodule.subset_span ⟨F', m', e', hF0, hm', hF', hme', rfl⟩

end SectionMulInj

open SectionMulInj in

theorem SectionMulInj.proof : SectionMulInj.Statement.{u, w} := by
  intro k _ Ω _ _ N x pp hpp hhom hZ D M s ⟨f, hf, hfp⟩ I y hy hsy
  rw [SubSystem.twist_sub_eq_mul_of_line]
  change y ∈ idealMod (x := x) pp I * M.sub I
  by_cases hX : ∃ j ∈ I.1, (X j : Poly k N) ∈ pp
  · obtain ⟨j, hj, hXj⟩ := hX
    have := StepThree.OnW.Gen.sub_le_twist_idealSys_of_mem M.toSubSystem I hj hXj hy
    rwa [SubSystem.twist_sub_eq_mul_of_line] at this
  push Not at hX
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)

  obtain ⟨e, he⟩ : ∃ e, homogeneousComponent e f ∉ pp := by
    by_contra hall
    push Not at hall
    exact hfp (by rw [← sum_homogeneousComponent f]; exact pp.sum_mem fun d _ => hall d)
  set g : chartRing k x I := ⟨_, StepThree.Away.div_pow_mem_chartRing I hi
    (homogeneousComponent_isHomogeneous e f)⟩ with hg
  have hgI : (g : Ω) ∉ idealMod (x := x) pp I := fun h => he <| by
    refine mem_of_div_mem_idealMod hpp hZ hX (pow_mem (X_mem_monos hi) e)
      (homogeneousComponent_isHomogeneous e f) (isHomogeneous_X_pow i e) ?_
    rw [map_pow, aeval_X]; exact h

  have hgD : Submodule.span (chartRing k x I) {(g : Ω)} * D.sub I ≤ Submodule.span _ {s} := by
    rw [Submodule.mul_le]
    intro a ha δ hδ
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp ha
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp
      (StepThree.Away.homogeneousComponent_mul_mem D.toSubSystem s I hi hf e δ hδ)
    rw [Submodule.mem_span_singleton]
    refine ⟨r * t, ?_⟩
    have hpow : x i ^ e ≠ 0 := pow_ne_zero _ hxi
    rw [chartRing_smul_def] at ht
    change ((r * t : chartRing k x I) : Ω) * s = ((r : Ω) * (g : Ω)) * δ
    rw [Subalgebra.coe_mul, hg]
    change (r : Ω) * t * s = (r : Ω) * (aeval x (homogeneousComponent e f) / x i ^ e) * δ
    rw [mul_assoc (r : Ω), mul_assoc (r : Ω)]
    congr 1
    rw [div_mul_eq_mul_div, eq_div_iff hpow, ← ht]
    ring
  obtain ⟨D', hD'⟩ := D.invertible I
  obtain ⟨M', hM'⟩ := M.invertible I
  have h1D : (1 : Ω) ∈ D.sub I * D' := by rw [hD']; exact Submodule.mem_one.mpr ⟨1, map_one _⟩

  have hgs : (g : Ω) ∈ Submodule.span (chartRing k x I) {s} * D' := by
    have := Submodule.mul_mem_mul (Submodule.mem_span_singleton_self (g : Ω)) h1D
    rw [mul_one, ← mul_assoc] at this
    exact mul_le_mul' hgD le_rfl this
  have hsy' : s * y ∈ idealMod (x := x) pp I * (D.sub I * M.sub I) := by
    rw [SubSystem.twist_sub_eq_mul_of_line, SubSystem.twist_sub_eq_mul_of_line] at hsy
    exact hsy
  have hgy : Submodule.span (chartRing k x I) {(g : Ω) * y} ≤ idealMod (x := x) pp I * M.sub I := by
    calc Submodule.span (chartRing k x I) {(g : Ω) * y}
        ≤ Submodule.span (chartRing k x I) {s} * D' * Submodule.span _ {y} := by
          rw [Submodule.span_le, Set.singleton_subset_iff]
          exact Submodule.mul_mem_mul hgs (Submodule.mem_span_singleton_self y)
      _ = D' * Submodule.span _ {s * y} := by
          rw [← Set.singleton_mul_singleton, ← Submodule.span_mul_span]; ring
      _ ≤ D' * (idealMod (x := x) pp I * (D.sub I * M.sub I)) := by
          gcongr
          rw [Submodule.span_le, Set.singleton_subset_iff]; exact hsy'
      _ = idealMod (x := x) pp I * M.sub I * (D.sub I * D') := by ring
      _ = idealMod (x := x) pp I * M.sub I := by rw [hD', mul_one]

  have hyM : Submodule.span (chartRing k x I) {y} * M' ≤ idealMod (x := x) pp I := by
    intro z hz
    have hz1 : z ∈ (1 : Submodule (chartRing k x I) Ω) := by
      rw [← hM']
      refine (mul_le_mul' ?_ le_rfl : _ ≤ M.sub I * M') hz
      rw [Submodule.span_le, Set.singleton_subset_iff]; exact hy
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hz1
    have hgz : (g : Ω) * algebraMap (chartRing k x I) Ω r ∈ idealMod (x := x) pp I := by
      have hle : Submodule.span (chartRing k x I) {(g : Ω)} * (Submodule.span _ {y} * M') ≤
          idealMod (x := x) pp I := by
        calc Submodule.span (chartRing k x I) {(g : Ω)} * (Submodule.span _ {y} * M')
            = Submodule.span _ {(g : Ω) * y} * M' := by
              rw [← Set.singleton_mul_singleton, ← Submodule.span_mul_span]; ring
          _ ≤ idealMod (x := x) pp I * M.sub I * M' := by gcongr
          _ = idealMod (x := x) pp I := by rw [mul_assoc, hM', mul_one]
      exact hle (Submodule.mul_mem_mul (Submodule.mem_span_singleton_self _) hz)
    exact ((mem_or_mem hpp hZ hX g r hgz).resolve_left hgI)
  have hle : Submodule.span (chartRing k x I) {y} ≤ idealMod (x := x) pp I * M.sub I :=
    calc Submodule.span (chartRing k x I) {y}
        = Submodule.span (chartRing k x I) {y} * M' * M.sub I := by
          rw [mul_assoc, mul_comm M', hM', mul_one]
      _ ≤ idealMod (x := x) pp I * M.sub I := by gcongr
  exact hle (Submodule.mem_span_singleton_self y)

end

end GroundTheory.Heights₂.Heights.Kleiman
