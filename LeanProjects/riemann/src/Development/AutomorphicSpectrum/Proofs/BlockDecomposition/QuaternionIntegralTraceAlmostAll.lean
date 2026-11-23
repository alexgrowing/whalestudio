import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitNormFormAtOddPlace

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA

theorem eventually_valued_eq_one {F : Type} [Field F] [NumberField F] {x : F} (hx : x ≠ 0) :
    ∀ᶠ v in Filter.cofinite (α := HeightOneSpectrum (𝓞 F)),
      Valued.v (algebraMap F (v.adicCompletion F) x) = 1 := by
  refine Filter.eventually_cofinite.2 (((HeightOneSpectrum.Support.finite (𝓞 F) x).union
    (HeightOneSpectrum.Support.finite (𝓞 F) x⁻¹)).subset fun v hv => ?_)
  by_contra hc
  simp only [HeightOneSpectrum.Support, Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt, map_inv₀] at hc
  have h0 : 0 < v.valuation F x := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx)
  have h1 : v.valuation F x = 1 := le_antisymm hc.1 ((inv_le_one₀ h0).1 hc.2)
  exact hv ((HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x).trans h1)

theorem norm_one_coords {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {d β x y : K} (hd : d ≠ 0) (hβ : β ≠ 0)
    (hxy : β = x ^ 2 - d * y ^ 2) (t : K) :
    let m := ((t * 2⁻¹) ^ 2 - 1) * d⁻¹
    let r := (1 + m) * 2⁻¹
    let c := (m - 1) * 2⁻¹
    (t * 2⁻¹) ^ 2 - d * r ^ 2 - β * (-(c * y * d * β⁻¹)) ^ 2 + d * β * (c * x * β⁻¹) ^ 2 = 1 := by
  intro m r c
  have hm : d * m = (t * 2⁻¹) ^ 2 - 1 := by simp only [m]; field_simp
  have e : - β * (-(c * y * d * β⁻¹)) ^ 2 + d * β * (c * x * β⁻¹) ^ 2 = c ^ 2 * d := by
    have : - β * (-(c * y * d * β⁻¹)) ^ 2 + d * β * (c * x * β⁻¹) ^ 2
        = c ^ 2 * d * (x ^ 2 - d * y ^ 2) * β⁻¹ := by field_simp; ring
    rw [this, ← hxy]; field_simp
  have e2 : d * r ^ 2 - c ^ 2 * d = d * m := by
    simp only [r, c]; field_simp; ring
  linear_combination e - e2 - hm

theorem exists_integral_coords {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    {D B t : v.adicCompletion F} (h2 : Valued.v (2 : v.adicCompletion F) = 1) (hD : Valued.v D = 1)
    (hB : Valued.v B = 1) (ht : t ∈ v.adicCompletionIntegers F) :
    ∃ a₀ ∈ v.adicCompletionIntegers F, ∃ a₁ ∈ v.adicCompletionIntegers F,
      ∃ a₂ ∈ v.adicCompletionIntegers F, ∃ a₃ ∈ v.adicCompletionIntegers F,
        2 * a₀ = t ∧ a₀ ^ 2 - D * a₁ ^ 2 - B * a₂ ^ 2 + D * B * a₃ ^ 2 = 1 := by
  obtain ⟨x, hx, y, hy, hxy⟩ := GlobalTheory.QNorm.exists_integral_sq_sub_mul_sq_of_unit F v D B h2 hD hB
  have ne0 : ∀ {z : v.adicCompletion F}, Valued.v z = 1 → z ≠ 0 := fun hz h0 => by
    rw [h0, map_zero] at hz; exact zero_ne_one hz
  have inv_mem : ∀ {z : v.adicCompletion F}, Valued.v z = 1 → z⁻¹ ∈ v.adicCompletionIntegers F :=
    fun hz => by rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hz, inv_one]
  have hDm : D ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hD]
  have hi2 := inv_mem h2
  have hk := norm_one_coords (ne0 h2) (ne0 hD) (ne0 hB) hxy t
  have h0 : t * 2⁻¹ ∈ v.adicCompletionIntegers F := mul_mem ht hi2
  have hm : ((t * 2⁻¹) ^ 2 - 1) * D⁻¹ ∈ v.adicCompletionIntegers F :=
    mul_mem (sub_mem (pow_mem h0 2) (one_mem _)) (inv_mem hD)
  have hc := mul_mem (sub_mem hm (one_mem _)) hi2
  exact ⟨_, h0, _, mul_mem (add_mem (one_mem _) hm) hi2, _,
    neg_mem (mul_mem (mul_mem (mul_mem hc hy) hDm) (inv_mem hB)), _,
    mul_mem (mul_mem hc hx) (inv_mem hB), by rw [mul_comm t, ← mul_assoc,
      mul_inv_cancel₀ (ne0 h2), one_mul], hk⟩

theorem exists_integral_norm_one_trace :
    ∀ {F : Type} [Field F] [NumberField F] (d β : F), d ≠ 0 → β ≠ 0 →
      ∀ᶠ v in Filter.cofinite (α := HeightOneSpectrum (𝓞 F)), ∀ t ∈ Ov v,
        ∃ b : Q d β (Kp (Sum.inr v : Pl F)), qn b = 1 ∧ 2 * b.re = t ∧ IntQ v b := by
  intro F _ _ d β hd hβ
  filter_upwards [eventually_valued_eq_one hd, eventually_valued_eq_one hβ,
    eventually_valued_eq_one (two_ne_zero : (2 : F) ≠ 0)] with v hdv hβv h2v t ht
  rw [map_ofNat] at h2v
  obtain ⟨a₀, h₀, a₁, h₁, a₂, h₂, a₃, h₃, htr, hn⟩ := exists_integral_coords v h2v hdv hβv ht
  exact ⟨⟨a₀, a₁, a₂, a₃⟩, hn, htr, h₀, h₁, h₂, h₃⟩

end GlobalTheory.CompanionTheory.PlaneSA
