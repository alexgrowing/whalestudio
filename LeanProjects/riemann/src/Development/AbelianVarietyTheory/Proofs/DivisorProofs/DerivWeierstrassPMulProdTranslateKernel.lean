import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoCubeMulDerivWeierstrassPNegTwoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfOddEllipticOfTendstoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdKernelMultiplierTranslateNegStatement

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem derivWeierstrassP_mul_prod_translate_kernel :
    ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), α ≠ 0 → Formalism.L2.Th1.F.MulStable L α → IsKerReps L α S →
      Even S.card → ∀ z, α * z ∉ L.lattice →
      L.derivWeierstrassP z * ∏ t ∈ S, L.derivWeierstrassP (z + t)
        = (∏ t ∈ S, L.derivWeierstrassP t) * α ^ 3 * L.derivWeierstrassP (α * z) := by
  intro L α S hα hst hS hev z hz
  have hper : ∀ z l, l ∈ L.lattice → L.derivWeierstrassP (z + l) = L.derivWeierstrassP z :=
    fun z l hl => L.derivWeierstrassP_add_coe z ⟨l, hl⟩
  obtain ⟨k1, k2⟩ := GlobalTheory.T.prod_kernel_multiplier_translate_neg L α S L.derivWeierstrassP hS hst hper
  have hdiff : ∀ w, w ∉ L.lattice → DifferentiableAt ℂ L.derivWeierstrassP w := fun w hw =>
    (L.analyticOnNhd_derivWeierstrassP w hw).differentiableAt
  have hcancel : ∀ w : ℂ, α * (w / α) = w := fun w => mul_div_cancel₀ w hα
  have h1 : ∀ w, w ∉ L.lattice → w / α ∉ L.lattice := fun w hw h => by
    have := hst _ h
    rw [hcancel] at this
    exact hw this
  have h2 : ∀ w, w ∉ L.lattice → ∀ t ∈ S, w / α + t ∉ L.lattice := fun w hw t ht h => by
    have h3 := hst _ h
    rw [mul_add, hcancel] at h3
    have h4 := L.lattice.sub_mem h3 (hS.1 t ht).1
    rw [add_sub_cancel_right] at h4
    exact hw h4
  set c : ℂ := ∏ t ∈ S, L.derivWeierstrassP t with hc
  have key := GlobalTheory.T.eq_zero_of_odd_elliptic_of_tendsto' L
    (fun w => L.derivWeierstrassP (w / α) * ∏ t ∈ S, L.derivWeierstrassP (w / α + t)
      - c * α ^ 3 * L.derivWeierstrassP w) ?_ ?_ ?_ ?_ (α * z) hz
  · have e : α * z / α = z := mul_div_cancel_left₀ z hα
    simp only [e] at key
    exact sub_eq_zero.mp key
  · intro w hw
    have d0 : DifferentiableAt ℂ (fun w : ℂ => w / α) w := differentiableAt_id.div_const α
    refine DifferentiableAt.sub (DifferentiableAt.mul ?_ ?_) ((hdiff w hw).const_mul _)
    · exact DifferentiableAt.comp w (g := L.derivWeierstrassP) (hdiff _ (h1 w hw)) d0
    · refine DifferentiableAt.fun_finsetProd fun t ht => ?_
      exact DifferentiableAt.comp w (g := L.derivWeierstrassP) (f := fun w : ℂ => w / α + t)
        (hdiff _ (h2 w hw t ht)) (d0.add_const t)
  · intro w l _ hl
    have := k1 (w / α) (l / α) (by rw [hcancel]; exact hl)
    simp only [add_div, this, hper w l hl]
  · intro w _
    have e1 : ∏ t ∈ S, L.derivWeierstrassP (-w / α + t) = ∏ t ∈ S, L.derivWeierstrassP (w / α + t) := by
      rw [← k2 (w / α)]
      have : ∀ t ∈ S, L.derivWeierstrassP (-w / α + t) = (-1) * L.derivWeierstrassP (w / α - t) := by
        intro t _
        rw [neg_one_mul, ← L.derivWeierstrassP_neg]
        congr 1
        ring
      rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, Finset.prod_const, hev.neg_one_pow, one_mul]
    simp only [e1]
    rw [neg_div, L.derivWeierstrassP_neg, L.derivWeierstrassP_neg]
    ring
  · have c0 := GlobalTheory.T.tendsto_cube_mul_derivWeierstrassP_neg_two L
    have tdiv : Filter.Tendsto (fun w : ℂ => w / α) (𝓝 0) (𝓝 0) := by
      have : Continuous (fun w : ℂ => w / α) := continuous_id.div_const α
      simpa using this.tendsto 0
    have tdiv' : Filter.Tendsto (fun w : ℂ => w / α) (𝓝[≠] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨tdiv.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact div_ne_zero hw hα
    have t1 := c0.comp tdiv'
    have t2 : Filter.Tendsto (fun w : ℂ => ∏ t ∈ S, L.derivWeierstrassP (w / α + t)) (𝓝[≠] 0) (𝓝 c) := by
      refine tendsto_finsetProd S fun t ht => ?_
      have ht' := (hdiff t (hS.1 t ht).2).continuousAt.tendsto
      have : Filter.Tendsto (fun w : ℂ => w / α + t) (𝓝[≠] 0) (𝓝 t) := by
        simpa using (tdiv.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))).add_const t
      exact ht'.comp this
    have t3 := ((t1.const_mul (α ^ 3)).mul t2).sub (c0.const_mul (c * α ^ 3))
    have e : α ^ 3 * (-2) * c - c * α ^ 3 * (-2) = 0 := by ring
    rw [e] at t3
    refine t3.congr fun w => ?_
    simp only [Function.comp]
    field_simp

end GlobalTheory.CMModel
