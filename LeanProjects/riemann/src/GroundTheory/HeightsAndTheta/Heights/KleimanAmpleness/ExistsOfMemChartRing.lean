import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisMore
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsHomogOfMemQuotPart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cellMon cellRes locPart mIdealOver mConeMapOver chartRingOver quotPart)

noncomputable section

namespace CechPointEval

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)] {Ω : Type} [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω)

def chart (c : ∀ k, ι k) : ∀ k, Finset (ι k) := fun k => {c k}

theorem prod_X_mem (c : ∀ k, ι k) (e : K → ℕ) :
    ∏ k, (X ⟨k, c k⟩ : MRingOver F ι) ^ e k ∈ cellMon F (chart c) :=
  Submonoid.prod_mem _ fun k _ =>
    Submonoid.pow_mem _ (Submonoid.subset_closure (show (X ⟨k, c k⟩ : MRingOver F ι) ∈
      {f | ∃ k, ∃ i ∈ chart c k, f = X ⟨k, i⟩} from ⟨k, c k, Finset.mem_singleton_self _, rfl⟩)) _

theorem aeval_prod_X (c : ∀ k, ι k) (e : K → ℕ) :
    aeval y (∏ k, (X ⟨k, c k⟩ : MRingOver F ι) ^ e k) = ∏ k, y ⟨k, c k⟩ ^ e k := by
  simp [map_prod]

theorem prod_pow_add (c : ∀ k, ι k) (b b' : K → ℕ) :
    ∏ k, y ⟨k, c k⟩ ^ (b + b') k = (∏ k, y ⟨k, c k⟩ ^ b k) * ∏ k, y ⟨k, c k⟩ ^ b' k := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => pow_add _ _ _

theorem aeval_div_mem_chartRing (c : ∀ k, ι k) {p : MRingOver F ι} {d : K → ℕ} (hp : IsMultiHomog p d) :
    aeval y p / ∏ k, y ⟨k, c k⟩ ^ d k ∈ chartRingOver F y c := by
  classical
  rw [p.as_sum, map_sum, Finset.sum_div]
  refine Subalgebra.sum_mem _ fun μ hμ => ?_
  have hdeg := hp μ hμ
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  have key : (∏ q : Σ k, ι k, y q ^ μ q) / ∏ k, y ⟨k, c k⟩ ^ d k =
      ∏ q : Σ k, ι k, (y q / y ⟨q.1, c q.1⟩) ^ μ q := by
    rw [Finset.prod_congr rfl fun q _ => div_pow (y q) _ (μ q), Finset.prod_div_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show _ = ∏ i, y ⟨k, c k⟩ ^ μ ⟨k, i⟩
    rw [Finset.prod_pow_eq_pow_sum, hdeg k]
  rw [mul_div_assoc, key, ← Algebra.smul_def]
  exact Subalgebra.smul_mem _ (Subalgebra.prod_mem _ fun q _ => Subalgebra.pow_mem _
    (Algebra.subset_adjoin (Set.mem_range_self (f := fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) q)) _) _

theorem exists_of_mem_chartRing (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {w : Ω}
    (hw : w ∈ chartRingOver F y c) :
    ∃ (b : K → ℕ) (h : MRingOver F ι), IsMultiHomog h b ∧ w = aeval y h / ∏ k, y ⟨k, c k⟩ ^ b k := by
  classical
  have hP : ∀ b : K → ℕ, ∏ k, y ⟨k, c k⟩ ^ b k ≠ 0 :=
    fun b => Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  induction hw using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨q, rfl⟩ := hx
    refine ⟨Pi.single q.1 1, X q, by simpa using isMultiHomog_X_pow (F := F) q.1 q.2 1, ?_⟩
    rw [aeval_X, Finset.prod_eq_single q.1]
    · simp
    · intro k _ hk
      rw [Pi.single_eq_of_ne hk, pow_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  | algebraMap r =>
    exact ⟨0, C r, isMultiHomog_C r, by simp⟩
  | add x x' _ _ h h' =>
    obtain ⟨b, p, hp, rfl⟩ := h
    obtain ⟨b', p', hp', rfl⟩ := h'
    refine ⟨b + b', p * ∏ k, X ⟨k, c k⟩ ^ b' k + p' * ∏ k, X ⟨k, c k⟩ ^ b k, ?_, ?_⟩
    · refine isMultiHomog_add (isMultiHomog_mul hp (isMultiHomog_prod_X c b')) ?_
      rw [add_comm b b']
      exact isMultiHomog_mul hp' (isMultiHomog_prod_X c b)
    · rw [map_add, map_mul, map_mul, aeval_prod_X, aeval_prod_X, prod_pow_add]
      field_simp [hP b, hP b']
  | mul x x' _ _ h h' =>
    obtain ⟨b, p, hp, rfl⟩ := h
    obtain ⟨b', p', hp', rfl⟩ := h'
    refine ⟨b + b', p * p', isMultiHomog_mul hp hp', ?_⟩
    rw [map_mul, prod_pow_add, div_mul_div_comm]

theorem image_eq_chart (hfield : ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → IsField (chartRingOver F y c))
    {I : ∀ k, Finset (ι k)} (hI : Good y I) {c : ∀ k, ι k} (hcI : ∀ k, c k ∈ I k) (β : K → ℤ) :
    (locPart ι (quotPart F (mIdealOver F y)) (cellMon F I) β).map (evMap y I) =
      (locPart ι (quotPart F (mIdealOver F y)) (cellMon F (chart c)) β).map (evMap y (chart c)) := by
  classical
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => hI k (c k) (hcI k)
  have hcg : Good y (chart c) := fun k i hi => by rw [Finset.mem_singleton.mp hi]; exact hc k
  have hsub : ∀ k, chart c k ⊆ I k := fun k => Finset.singleton_subset_iff.mpr (hcI k)
  have hP : ∀ b : K → ℕ, ∏ k, y ⟨k, c k⟩ ^ b k ≠ 0 :=
    fun b => Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  have hres : ∀ x, evMap y I (cellRes F _ (chart c) I x) = evMap y (chart c) x := by
    intro x
    induction x using LocalizedModule.induction_on with
    | h m t =>
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective m
      rw [CechPointVanish.cellRes_mk (CechPointVanish.cellMon_mono hsub), evMap_mk y hI, evMap_mk y hcg]
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨g, t, a, ht, hg, hd, rfl⟩ := exists_rep hx
    rcases hd with hd | rfl
    swap
    · rw [map_zero, LocalizedModule.zero_mk, map_zero]
      exact Submodule.zero_mem _
    have ht0 := aeval_ne_zero_of_mem hI t.2
    have hu := aeval_div_mem_chartRing y c ht
    have hu0 : (⟨_, hu⟩ : chartRingOver F y c) ≠ 0 :=
      fun h => div_ne_zero ht0 (hP a) (congrArg Subtype.val h)
    obtain ⟨v, hv⟩ := (hfield c hc).mul_inv_cancel hu0
    obtain ⟨b, h, hh, hvh⟩ := exists_of_mem_chartRing y c hc v.2
    have hprod : aeval y (t : MRingOver F ι) * aeval y h =
        (∏ k, y ⟨k, c k⟩ ^ a k) * ∏ k, y ⟨k, c k⟩ ^ b k := by
      have e := congrArg Subtype.val hv
      simp only [Subalgebra.coe_mul, Subalgebra.coe_one] at e
      rw [hvh] at e
      field_simp [hP a, hP b] at e
      linear_combination e
    have hh0 : aeval y h ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hprod
      exact mul_ne_zero (hP a) (hP b) hprod.symm
    refine ⟨LocalizedModule.mk (Ideal.Quotient.mk _ (g * h)) ⟨_, prod_X_mem c (a + b)⟩, ?_, ?_⟩
    · refine Submodule.subset_span ⟨_, ⟨_, prod_X_mem c (a + b)⟩, a + b, isMultiHomog_prod_X c (a + b),
        Submodule.subset_span ⟨g * h, ⟨?_, ?_⟩, rfl⟩, rfl⟩
      · intro k
        have := hd k
        simp only [Pi.add_apply, Nat.cast_add]
        omega
      · have e : (fun k => ((β + fun k => ((a + b) k : ℤ)) k).toNat) = (fun k => (β k + a k).toNat) + b := by
          funext k
          have := hd k
          simp only [Pi.add_apply, Nat.cast_add]
          omega
        rw [e]
        exact isMultiHomog_mul hg hh
    · rw [evMap_mk y hcg, evMap_mk y hI, map_mul, aeval_prod_X, prod_pow_add, ← hprod]
      exact mul_div_mul_right _ _ hh0
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨cellRes F _ (chart c) I x,
      CechPointVanish.cellRes_mem_locPart (CechPointVanish.cellMon_mono hsub) β hx, hres x⟩

end CechPointEval

theorem CechPointEval.full : CechPointEval.Statement := by
  intro F _ K _ _ ι _ _ Ω _ _ y hfield β
  classical
  by_cases h0 : ∃ c₀ : ∀ k, ι k, ∀ k, y ⟨k, c₀ k⟩ ≠ 0
  · obtain ⟨c₀, hc₀⟩ := h0
    refine ⟨(locPart ι (quotPart F (mIdealOver F y)) (cellMon F (CechPointEval.chart c₀)) β).map
      (CechPointEval.evMap y (CechPointEval.chart c₀)), CechPointEval.evMap y,
      fun I hIne hI => ⟨fun g t => CechPointEval.evMap_mk y hI g t, CechPointEval.evMap_injOn y hI β, ?_⟩⟩
    choose c hc using hIne
    let U : ∀ k, Finset (ι k) := fun k => {c k, c₀ k}
    have hU : CechPointEval.Good y U := by
      intro k i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hI k _ (hc k)
      · rw [Finset.mem_singleton.mp hi]
        exact hc₀ k
    rw [CechPointEval.image_eq_chart y hfield hI hc,
      ← CechPointEval.image_eq_chart y hfield hU (c := c) (fun k => by simp [U]),
      CechPointEval.image_eq_chart y hfield hU (c := c₀) (fun k => by simp [U])]
  · refine ⟨⊥, CechPointEval.evMap y, fun I hIne hI => absurd ?_ h0⟩
    choose c hc using hIne
    exact ⟨c, fun k => hI k (c k) (hc k)⟩

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
