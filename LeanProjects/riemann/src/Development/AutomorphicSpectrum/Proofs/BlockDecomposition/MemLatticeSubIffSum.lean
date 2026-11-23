import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatSpan

variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B]

theorem dpE_mul (f : W →+* B) (ξ : W) (l M i j : ℕ) :
    Lat.dpE f ξ l M i * Lat.dpE f ξ l M j =
      ((i + j).choose i : B) * Lat.dpE f ξ l M (i + j) := by
  have hc : (((i + j).choose i : ℕ) : ℚ) * ((i + j).factorial : ℚ)⁻¹ =
      ((i.factorial : ℚ))⁻¹ * ((j.factorial : ℚ))⁻¹ := by
    have h := Nat.add_choose_mul_factorial_mul_factorial i j
    rw [← Nat.choose_symm_add] at h
    have h' : (((i + j).choose i : ℕ) : ℚ) * (i.factorial : ℚ) * (j.factorial : ℚ) =
        ((i + j).factorial : ℚ) := by exact_mod_cast h
    have hi : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
    have hj : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
    rw [← h']
    have hcne : (((i + j).choose i : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (Nat.le_add_right i j)).ne'
    field_simp
  unfold Lat.dpE
  rw [smul_mul_smul_comm, ← pow_add, ← hc, ← smul_smul, ← nsmul_eq_mul,
    Nat.cast_smul_eq_nsmul ℚ]

theorem mem_span_of_mem_sub (f : W →+* B) (ξ : W) (l M : ℕ) (x : B) (hx : x ∈ Lat.sub f ξ l M) :
    letI : Algebra W B := f.toAlgebra
    x ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) := by
  letI : Algebra W B := f.toAlgebra
  have hsm : ∀ (w : W) (b : B), w • b = f w * b := fun w b => Algebra.smul_def w b
  have h0 : Lat.dpE f ξ l M 0 = 1 := by simp [Lat.dpE]
  have hgen : ∀ i, Lat.dpE f ξ l M i ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) :=
    fun i => Submodule.subset_span ⟨i, rfl⟩
  have hW : ∀ w : W, f w ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) := by
    intro w
    have h := Submodule.smul_mem _ w (hgen 0)
    rwa [hsm, h0, mul_one] at h
  have hnat : ∀ (n : ℕ) (y : B), y ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) →
      (n : B) * y ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) := by
    intro n y hy
    have h := Submodule.smul_mem _ (n : W) hy
    rwa [hsm, map_natCast] at h
  have hmul : ∀ a b : B, a ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) →
      b ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) →
      a * b ∈ Submodule.span W (Set.range (Lat.dpE f ξ l M)) := by
    intro a b ha hb
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨i, rfl⟩ := ha
      induction hb using Submodule.span_induction with
      | mem b hb =>
        obtain ⟨j, rfl⟩ := hb
        rw [dpE_mul]
        exact hnat _ _ (hgen _)
      | zero => simp
      | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
      | smul w y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ w hy
    | zero => simp
    | add y z _ _ hy hz => rw [add_mul]; exact Submodule.add_mem _ hy hz
    | smul w y _ hy => rw [smul_mul_assoc]; exact Submodule.smul_mem _ w hy
  unfold Lat.sub at hx
  induction hx using Subring.closure_induction with
  | mem y hy =>
    rcases hy with ⟨w, rfl⟩ | ⟨i, rfl⟩
    · exact hW w
    · exact hgen i
  | zero => exact Submodule.zero_mem _
  | one => rw [← h0]; exact hgen 0
  | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
  | neg y _ hy => exact Submodule.neg_mem _ hy
  | mul y z _ _ hy hz => exact hmul y z hy hz

theorem mem_sub_iff : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W)
    (l M : ℕ) (x : B), x ∈ Lat.sub f ξ l M ↔
      ∃ (n : ℕ) (c : Fin n → W), x = ∑ i, f (c i) * Lat.dpE f ξ l M i := by
  intro W B _ _ _ f ξ l M x
  constructor
  · intro hx
    letI : Algebra W B := f.toAlgebra
    have hsm : ∀ (w : W) (b : B), w • b = f w * b := fun w b => Algebra.smul_def w b
    obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (mem_span_of_mem_sub f ξ l M x hx)
    refine ⟨c.support.sup id + 1, fun i => c i, ?_⟩
    rw [Fin.sum_univ_eq_sum_range (fun i => f (c i) * Lat.dpE f ξ l M i), Finsupp.sum]
    have hsub : c.support ⊆ Finset.range (c.support.sup id + 1) := by
      intro i hi
      exact Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
    rw [Finset.sum_congr rfl (fun i _ => hsm (c i) (Lat.dpE f ξ l M i))]
    refine Finset.sum_subset hsub fun i _ hi => ?_
    rw [Finsupp.notMem_support_iff.1 hi, map_zero, zero_mul]
  · rintro ⟨n, c, rfl⟩
    refine Subring.sum_mem _ fun i _ => Subring.mul_mem _ ?_ ?_
    · exact Subring.subset_closure (Or.inl ⟨c i, rfl⟩)
    · exact Subring.subset_closure (Or.inr ⟨i, rfl⟩)

end GlobalTheory.CompanionTheory.LatSpan
