import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelSummationByPartsWeights
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SummationOperatorsBoundedGood
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SummationOperatorsPreserveOtherIndex
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDifferenceSummable

set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.OneVar

theorem goodAt_smul {r l : ℕ} {k : Fin r} {v : (Fin r → ℕ) → ℚ} (s : ℚ) (h : GoodAt l k v) :
    GoodAt l k (fun m => s * v m) := by
  refine ⟨fun m => by simp only [h.1 m], fun m => ?_⟩
  rw [← Finset.mul_sum, h.2 m, mul_zero]

theorem bddW_sign {r : ℕ} {v : (Fin r → ℕ) → ℚ} (c : ℕ) (h : BddW v) :
    BddW (fun m => (-1 : ℚ) ^ c * v m) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun m => ?_⟩
  have : |(((-1 : ℚ) ^ c * v m : ℚ) : ℝ)| = |(v m : ℝ)| := by
    push_cast
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [this]
  exact hC m

theorem iterate_good_bdd {r l : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (hl : 0 < l)
    (hg : GoodAt l i v) (hb : BddW v) (c : ℕ) :
    GoodAt l i ((Aop l i)^[c] v) ∧ BddW ((Aop l i)^[c] v) := by
  induction c with
  | zero => exact ⟨hg, hb⟩
  | succ c ih =>
    rw [Function.iterate_succ_apply']
    have := @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.aop_props r l i _ hl ih.1 ih.2
    exact ⟨this.2.2, this.1⟩

theorem iterate_good_other {r l : ℕ} {i k : Fin r} {v : (Fin r → ℕ) → ℚ} (hk : k ≠ i)
    (hg : GoodAt l k v) (c : ℕ) : GoodAt l k ((Aop l i)^[c] v) := by
  induction c with
  | zero => exact hg
  | succ c ih =>
    rw [Function.iterate_succ_apply']
    exact (((@GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.OtherVar.otherVar_main r l i k _ hk).1 ih).1)

theorem iterate_supp_other {r l : ℕ} {i k : Fin r} {v : (Fin r → ℕ) → ℚ} (hk : k ≠ i)
    (hs : ∀ m, m k ≠ 0 → v m = 0) (c : ℕ) : ∀ m, m k ≠ 0 → (Aop l i)^[c] v m = 0 := by
  induction c with
  | zero => exact hs
  | succ c ih =>
    rw [Function.iterate_succ_apply']
    exact (((@GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.OtherVar.otherVar_main r l i k _ hk).2 ih).1)

theorem DL_replicate_succ {r : ℕ} (i : Fin r) (c : ℕ) (g : (Fin r → ℕ) → ℂ) :
    DL (List.replicate (c + 1) i) g = fd i (DL (List.replicate c i) g) := by
  simp [DL, List.replicate_succ]

theorem tsum_iterate {r l : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (hl : 0 < l)
    (hg : GoodAt l i v) (hb : BddW v) {g : (Fin r → ℕ) → ℂ} (hs : Summable g) (N : ℕ) :
    ∑' m, (v m : ℂ) * g m =
      ∑ c ∈ Finset.range N, (-1 : ℂ) ^ c *
          ∑' m, (Bop l i ((Aop l i)^[c] v) m : ℂ) * DL (List.replicate c i) g m +
        (-1 : ℂ) ^ N * ∑' m, ((Aop l i)^[N] v m : ℂ) * DL (List.replicate N i) g m := by
  induction N with
  | zero => simp [DL]
  | succ N ih =>
    have hN := iterate_good_bdd hl hg hb N
    have key := @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.StepIdentity.stepIdentity r l i ((Aop l i)^[N] v) (DL (List.replicate N i) g) hl hN.1 hN.2
      (@GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.summable_DL r _ g hs)
    rw [ih, key, Finset.sum_range_succ, Function.iterate_succ_apply', DL_replicate_succ, pow_succ]
    ring

def uW {r : ℕ} (l N : ℕ) (i : Fin r) (v : (Fin r → ℕ) → ℚ) (c : ℕ) : (Fin r → ℕ) → ℚ :=
  if c < N then fun m => (-1 : ℚ) ^ c * Bop l i ((Aop l i)^[c] v) m
  else fun m => (-1 : ℚ) ^ N * (Aop l i)^[N] v m

theorem abel_oneVar : ∀ (r l N : ℕ) (i : Fin r) (v : (Fin r → ℕ) → ℚ), 0 < l → GoodAt l i v → BddW v →
  ∃ u : Fin (N + 1) → (Fin r → ℕ) → ℚ, (∀ c, BddW (u c)) ∧
    (∀ c : Fin (N + 1), (c : ℕ) = N ∨ ∀ m, m i ≠ 0 → u c m = 0) ∧
    (∀ c k, k ≠ i → GoodAt l k v → GoodAt l k (u c)) ∧
    (∀ c k, k ≠ i → (∀ m, m k ≠ 0 → v m = 0) → ∀ m, m k ≠ 0 → u c m = 0) ∧
    ∀ g : (Fin r → ℕ) → ℂ, Summable g →
      ∑' m, (v m : ℂ) * g m = ∑ c, ∑' m, (u c m : ℂ) * DL (List.replicate (c : ℕ) i) g m := by
  intro r l N i v hl hg hb
  refine ⟨fun c => uW l N i v c, fun c => ?_, fun c => ?_, fun c k hk hgk => ?_,
    fun c k hk hsk => ?_, fun g hs => ?_⟩
  · unfold uW
    beta_reduce
    split_ifs with h
    · have hc := iterate_good_bdd hl hg hb c
      exact bddW_sign _ (@GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.aop_props r l i _ hl hc.1 hc.2).2.1
    · exact bddW_sign _ (iterate_good_bdd hl hg hb N).2
  · by_cases h : (c : ℕ) < N
    · refine Or.inr fun m hm => ?_
      simp [uW, h, Bop, hm]
    · exact Or.inl (by have := c.isLt; omega)
  · unfold uW
    beta_reduce
    split_ifs with h
    · exact goodAt_smul _ ((@GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.OtherVar.otherVar_main r l i k _ hk).1 (iterate_good_other hk hgk c)).2
    · exact goodAt_smul _ (iterate_good_other hk hgk N)
  · intro m hm
    unfold uW
    beta_reduce
    split_ifs with h
    · simp [((@GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.OtherVar.otherVar_main r l i k _ hk).2 (iterate_supp_other hk hsk c)).2 m hm]
    · simp [iterate_supp_other hk hsk N m hm]
  · rw [tsum_iterate hl hg hb hs N, Fin.sum_univ_castSucc, Finset.sum_range]
    congr 1
    · refine Finset.sum_congr rfl fun c _ => ?_
      have hc : (c : ℕ) < N := c.isLt
      rw [← tsum_mul_left]
      refine tsum_congr fun m => ?_
      simp [uW, hc, mul_assoc]
    · rw [← tsum_mul_left]
      refine tsum_congr fun m => ?_
      simp [uW, mul_assoc]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.OneVar
