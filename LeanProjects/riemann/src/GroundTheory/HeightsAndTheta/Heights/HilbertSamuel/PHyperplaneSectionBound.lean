import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHyperplaneSectionBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHyperplaneQuotientBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

section Mul

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
  {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k}

omit [∀ k, Fintype (ι k)] in

theorem mul_mem_chartLatQ (b : K → ℤ) {t : Ω} (ht : t ∈ chartLatQ y (b - 1) 1) :
    (∏ k, y ⟨k, c k⟩) * t ∈ chartLatQ y b 1 := by
  intro c' hc'
  have h := ht c' hc'
  have hk : ∀ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * b k)) =
      y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * (b - 1) k)) / y ⟨k, c' k⟩ := by
    intro k
    rw [eq_div_iff (hc' k), ← zpow_add_one₀ (hc' k)]
    congr 1
    simp only [Pi.sub_apply, Pi.one_apply]
    ring
  have heq : (∏ k, y ⟨k, c k⟩) * t * ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * b k)) =
      (t * ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) * (b - 1) k))) * ∏ k, (y ⟨k, c k⟩ / y ⟨k, c' k⟩) := by
    simp only [hk, Finset.prod_div_distrib]
    ring
  rw [heq]
  refine Subalgebra.mul_mem _ h (Subalgebra.prod_mem _ fun k _ => ?_)
  exact Algebra.subset_adjoin ⟨⟨k, c k⟩, rfl⟩

theorem finrank_chartLatQ_le (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (b : K → ℤ) :
    Module.finrank ℚ (chartLatQ y b 1) ≤
      Module.finrank ℚ (chartLatQ y (b - 1) 1) + Module.finrank ℚ (chartLatQ y b 1 ⧸ chartDivSec y c b) := by
  by_cases hfin : FiniteDimensional ℚ (chartLatQ y b 1)
  swap
  · rw [Module.finrank_of_not_finite hfin]; exact Nat.zero_le _
  have hm0 : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  let φ : chartLatQ y (b - 1) 1 →ₗ[ℚ] chartDivSec y c b :=
    { toFun := fun t => ⟨⟨(∏ k, y ⟨k, c k⟩) * t, mul_mem_chartLatQ b t.2⟩,
        Submodule.mem_comap.mpr (Submodule.mem_map.mpr ⟨t, t.2, rfl⟩)⟩
      map_add' := fun s t => by
        apply Subtype.ext; apply Subtype.ext
        simp only [Submodule.coe_add, mul_add]
      map_smul' := fun r t => by
        apply Subtype.ext; apply Subtype.ext
        simp only [Submodule.coe_smul, RingHom.id_apply, mul_smul_comm] }
  have hinj : Function.Injective φ := fun s t h => by
    have h' := congrArg (fun x : chartDivSec y c b => ((x : chartLatQ y b 1) : Ω)) h
    exact Subtype.ext (mul_left_cancel₀ hm0 h')
  have hsurj : Function.Surjective φ := by
    rintro ⟨⟨s, hsV⟩, hs⟩
    obtain ⟨t, ht, hts⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp hs)
    exact ⟨⟨t, ht⟩, Subtype.ext (Subtype.ext hts)⟩
  have hφ := (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).finrank_eq
  rw [← Submodule.finrank_quotient_add_finrank (chartDivSec y c b), ← hφ, add_comm]

end Mul

theorem HyperplaneSectionBound.proof (hQ : HyperplaneQuotientBound.Statement) :
    HyperplaneSectionBound.Statement := by
  intro K _ ι _ Ω _ _ y D a hD hV hB
  have hc : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hV.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    rw [mCoordIdeal, RingHom.mem_ker]
    simp [mConeMap, h0]
  choose c hc using hc
  obtain ⟨C, hC⟩ := hQ K ι Ω y D a c hD hV hB hc
  refine ⟨C, hC.mono fun n hn => ?_⟩
  have h := finrank_chartLatQ_le hc ((n : ℤ) • a)
  have h' : (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a) 1) : ℝ) ≤
      (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a - 1) 1) : ℝ) +
        (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a) 1 ⧸ chartDivSec y c ((n : ℤ) • a)) : ℝ) := by
    exact_mod_cast h
  linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
