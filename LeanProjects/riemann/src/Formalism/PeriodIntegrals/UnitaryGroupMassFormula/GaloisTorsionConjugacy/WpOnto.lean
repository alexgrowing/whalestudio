import Mathlib
import Formalism.PeriodIntegrals.GalTorsConj
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.WpBridge
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole

noncomputable section

namespace PI.GalTorsConj.W

open PI.GalTorsConj Filter Topology

theorem wp_onto (L : PeriodPair) (x : ℂ) : ∃ z, z ∉ L.lattice ∧ L.weierstrassP z = x := by
  classical
  by_contra hne
  push Not at hne
  set f : ℂ → ℂ := fun z => (L.weierstrassP z - x)⁻¹ with hf
  have hmer : ∀ z, MeromorphicAt f z := by
    intro z
    have h := L.meromorphic_weierstrassP z
    fun_prop
  have hper : Formalism.L2.Th1.F.IsPeriodic L f := by
    intro ω hω z
    show (L.weierstrassP (z + ω) - x)⁻¹ = (L.weierstrassP z - x)⁻¹
    rw [show L.weierstrassP (z + ω) = L.weierstrassP z from L.weierstrassP_add_coe z ⟨ω, hω⟩]
  have han : ∀ z, z ∉ L.lattice → AnalyticAt ℂ f z := by
    intro z hz
    have h1 : AnalyticAt ℂ L.weierstrassP z := L.analyticOnNhd_weierstrassP z hz
    have h2 : L.weierstrassP z - x ≠ 0 := sub_ne_zero.mpr (hne z hz)
    exact (h1.sub analyticAt_const).inv h2
  have hord : ∀ z, 0 ≤ meromorphicOrderAt f z := by
    intro z
    by_cases hz : z ∈ L.lattice
    · have h1 : meromorphicOrderAt (fun w => L.weierstrassP w - x) z = -2 := by
        have e : (fun w => L.weierstrassP w - x) = L.weierstrassP + (fun _ => -x) := by
          ext w
          simp [sub_eq_add_neg]
        rw [e, meromorphicOrderAt_add_eq_left_of_lt (MeromorphicAt.const (-x) z)]
        · exact L.order_weierstrassP z hz
        · rw [L.order_weierstrassP z hz, meromorphicOrderAt_const]
          split_ifs
          · exact WithTop.coe_lt_top _
          · decide
      have e2 : f = (fun w => L.weierstrassP w - x)⁻¹ := rfl
      rw [e2, meromorphicOrderAt_inv, h1]
      decide
    · exact (han z hz).meromorphicOrderAt_nonneg
  obtain ⟨c, hc⟩ := Formalism.L2.Th1.F.ellipticNoPole L f hmer hper hord
  have hev : L.weierstrassP =ᶠ[𝓝[≠] 0] fun _ => x + c⁻¹ := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0)] with z hz0 hz
    have hzl : z ∉ L.lattice := fun h => hz ⟨h, hz0⟩
    have h1 : f z = c := hc z (han z hzl).continuousAt
    have h1' : (L.weierstrassP z - x)⁻¹ = c := h1
    rw [← h1', inv_inv]
    ring
  have h3 := meromorphicOrderAt_congr hev
  rw [L.order_weierstrassP 0 L.lattice.zero_mem, meromorphicOrderAt_const] at h3
  split_ifs at h3
  · exact absurd h3 (WithTop.coe_ne_top)
  · exact absurd h3 (by decide)

theorem pOnto : POnto := by
  intro L x y hxy
  obtain ⟨z, hz, hzx⟩ := wp_onto L x
  have hsq := L.derivWeierstrassP_sq z hz
  rw [hzx, ← hxy] at hsq
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
  · exact ⟨z, hz, hzx, h⟩
  · refine ⟨-z, ?_, by rw [L.weierstrassP_neg, hzx], by rw [L.derivWeierstrassP_neg, h, neg_neg]⟩
    intro hm
    exact hz (by simpa using L.lattice.neg_mem hm)

end PI.GalTorsConj.W

end
