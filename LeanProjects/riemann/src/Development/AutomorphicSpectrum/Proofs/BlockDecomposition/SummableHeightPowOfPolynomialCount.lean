import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EmbBar
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

namespace GlobalTheory.CompanionTheory.GodementH

theorem summable_rpow_neg_of_polynomial_count :
    ∀ (Q : Type) (h : Q → ℝ), (∀ q, 1 ≤ h q) → ∀ (C : ℝ) (c : ℕ),
    (∀ T : ℝ, 1 ≤ T → {q | h q ≤ T}.Finite ∧ (Set.ncard {q | h q ≤ T} : ℝ) ≤ C * T ^ c) → ∀ s : ℝ, (c : ℝ) < s →
    Summable fun q => h q ^ (-s) := by
  intro Q h h1 C c hc s hs
  classical
  have hC : 0 ≤ C := by
    have h2 := (hc 1 le_rfl).2
    have h3 : (0:ℝ) ≤ (Set.ncard {q | h q ≤ 1} : ℝ) := Nat.cast_nonneg _
    simp only [one_pow, mul_one] at h2
    linarith
  set r : ℝ := (2:ℝ) ^ ((c:ℝ) - s) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hg : Summable fun k : ℕ => C * 2 ^ c * r ^ k :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hg0 : ∀ k : ℕ, 0 ≤ C * 2 ^ c * r ^ k := fun k => by positivity
  set K : Q → ℕ := fun q => ⌊Real.logb 2 (h q)⌋₊ with hK
  have hlog0 : ∀ q, 0 ≤ Real.logb 2 (h q) := fun q =>
    Real.logb_nonneg (by norm_num) (h1 q)
  have hlow : ∀ q, (2:ℝ) ^ (K q : ℝ) ≤ h q := fun q => by
    have hq : (0:ℝ) < h q := lt_of_lt_of_le one_pos (h1 q)
    have : (K q : ℝ) ≤ Real.logb 2 (h q) := Nat.floor_le (hlog0 q)
    calc (2:ℝ) ^ (K q : ℝ) ≤ (2:ℝ) ^ (Real.logb 2 (h q)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) this
      _ = h q := Real.rpow_logb (by norm_num) (by norm_num) hq
  have hupp : ∀ q, h q ≤ (2:ℝ) ^ (K q + 1) := fun q => by
    have hq : (0:ℝ) < h q := lt_of_lt_of_le one_pos (h1 q)
    have : Real.logb 2 (h q) ≤ ((K q + 1 : ℕ) : ℝ) := by
      push_cast
      exact (Nat.lt_floor_add_one _).le
    calc h q = (2:ℝ) ^ (Real.logb 2 (h q)) :=
          (Real.rpow_logb (by norm_num) (by norm_num) hq).symm
      _ ≤ (2:ℝ) ^ (((K q + 1 : ℕ)) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) this
      _ = (2:ℝ) ^ (K q + 1) := Real.rpow_natCast _ _
  have hterm : ∀ q, h q ^ (-s) ≤ ((2:ℝ) ^ (K q : ℝ)) ^ (-s) := fun q =>
    Real.rpow_le_rpow_of_nonpos (by positivity) (hlow q) (by linarith [(Nat.cast_nonneg c : (0:ℝ) ≤ c)])
  have hfib : ∀ (u : Finset Q) (k : ℕ),
      ∑ q ∈ u with K q = k, h q ^ (-s) ≤ C * 2 ^ c * r ^ k := by
    intro u k
    have hT : (1:ℝ) ≤ (2:ℝ) ^ (k + 1) := one_le_pow₀ (by norm_num)
    obtain ⟨hfin, hcard⟩ := hc _ hT
    have hsub : ((u.filter fun q => K q = k : Finset Q) : Set Q) ⊆ {q | h q ≤ (2:ℝ) ^ (k + 1)} := by
      intro q hq
      have hq' : K q = k := (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2
      have := hupp q
      rw [hq'] at this
      exact this
    have hcard2 : ((u.filter fun q => K q = k : Finset Q).card : ℝ) ≤ C * ((2:ℝ) ^ (k + 1)) ^ c := by
      refine le_trans ?_ hcard
      have := Set.ncard_le_ncard hsub hfin
      rw [Set.ncard_coe_finset] at this
      exact_mod_cast this
    have hb : ∀ q ∈ u.filter (fun q => K q = k), h q ^ (-s) ≤ ((2:ℝ) ^ (k : ℝ)) ^ (-s) := by
      intro q hq
      have hq' : K q = k := (Finset.mem_filter.mp hq).2
      have := hterm q
      rw [hq'] at this
      exact this
    have hb0 : (0:ℝ) ≤ ((2:ℝ) ^ (k : ℝ)) ^ (-s) := by positivity
    calc ∑ q ∈ u with K q = k, h q ^ (-s)
        ≤ ((u.filter fun q => K q = k : Finset Q).card : ℝ) * ((2:ℝ) ^ (k : ℝ)) ^ (-s) := by
          simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul _ _ _ hb
      _ ≤ (C * ((2:ℝ) ^ (k + 1)) ^ c) * ((2:ℝ) ^ (k : ℝ)) ^ (-s) :=
          mul_le_mul_of_nonneg_right hcard2 hb0
      _ = C * 2 ^ c * r ^ k := by
          have e1 : ((2:ℝ) ^ (k + 1)) ^ c = 2 ^ c * ((2:ℝ) ^ (k : ℝ)) ^ (c : ℝ) := by
            rw [Real.rpow_natCast, Real.rpow_natCast, pow_succ, mul_pow, mul_comm]
          have e2 : r ^ k = ((2:ℝ) ^ (k : ℝ)) ^ (c : ℝ) * ((2:ℝ) ^ (k : ℝ)) ^ (-s) := by
            rw [← Real.rpow_add (by positivity), hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
              ← Real.rpow_mul (by norm_num)]
            congr 1
            ring
          rw [e1, e2]
          ring
  refine summable_of_sum_le (c := ∑' k : ℕ, C * 2 ^ c * r ^ k) (fun q => Real.rpow_nonneg (by linarith [h1 q]) _) ?_
  intro u
  calc ∑ q ∈ u, h q ^ (-s)
      = ∑ k ∈ u.image K, ∑ q ∈ u with K q = k, h q ^ (-s) :=
        (Finset.sum_fiberwise_of_maps_to (fun q hq => Finset.mem_image_of_mem K hq) _).symm
    _ ≤ ∑ k ∈ u.image K, C * 2 ^ c * r ^ k := Finset.sum_le_sum fun k _ => hfib u k
    _ ≤ ∑' k : ℕ, C * 2 ^ c * r ^ k := hg.sum_le_tsum _ fun k _ => hg0 k

end GlobalTheory.CompanionTheory.GodementH
