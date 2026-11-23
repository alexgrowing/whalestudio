import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.FourierProjections.PaPolyTranslate

namespace ReciprocityTheory.ChartRestriction.G.I2.FPw

open MeasureTheory Complex

noncomputable section

variable {ι : Type} [Fintype ι]

open Classical

theorem paD_add (α : ι →₀ ℕ) {H1 H2 : EuclideanSpace ℂ ι → ℂ} (h1 : ContDiff ℂ (⊤ : ℕ∞) H1)
    (h2 : ContDiff ℂ (⊤ : ℕ∞) H2) : paD α (H1 + H2) = paD α H1 + paD α H2 := by
  unfold paD polyDeriv
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [iteratedFDeriv_add_apply (h1.contDiffAt.of_le (by exact_mod_cast le_top))
    (h2.contDiffAt.of_le (by exact_mod_cast le_top))]
  simp [mul_add]

theorem paD_smul (α : ι →₀ ℕ) (a : ℂ) {H : EuclideanSpace ℂ ι → ℂ}
    (h : ContDiff ℂ (⊤ : ℕ∞) H) : paD α (a • H) = a * paD α H := by
  unfold paD polyDeriv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [iteratedFDeriv_const_smul_apply (h.contDiffAt.of_le (by exact_mod_cast le_top))]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

theorem paD_zero (α : ι →₀ ℕ) : paD α (0 : EuclideanSpace ℂ ι → ℂ) = 0 := by
  simp [paD, polyDeriv, iteratedFDeriv_zero_fun]

theorem paFact_ne (α : ι →₀ ℕ) : (paFact α : ℂ) ≠ 0 := by
  unfold paFact
  exact Nat.cast_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => Nat.factorial_ne_zero _)

theorem paJet_add (c : ℕ) {H1 H2 : EuclideanSpace ℂ ι → ℂ} (h1 : ContDiff ℂ (⊤ : ℕ∞) H1)
    (h2 : ContDiff ℂ (⊤ : ℕ∞) H2) : paJet c (H1 + H2) = paJet c H1 + paJet c H2 := by
  unfold paJet
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [paD_add α h1 h2, add_div, add_smul]

theorem paJet_smul (c : ℕ) (r : ℂ) {H : EuclideanSpace ℂ ι → ℂ} (h : ContDiff ℂ (⊤ : ℕ∞) H) :
    paJet c (r • H) = r • paJet c H := by
  unfold paJet
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [paD_smul α r h, mul_div_assoc, smul_smul]

theorem paJet_zero (c : ℕ) : paJet c (0 : EuclideanSpace ℂ ι → ℂ) = 0 := by
  unfold paJet
  simp [paD_zero]

theorem paJet_mono (c : ℕ) (m : ι →₀ ℕ) :
    paJet c (paMono m) = if m ∈ paS c then paMono m else 0 := by
  unfold paJet
  simp only [paD_mono]
  have e : ∀ α, ((if α = m then (paFact α : ℂ) else 0) / paFact α) • paMono α =
      if α = m then paMono m else 0 := fun α => by
    split_ifs with h
    · subst h
      rw [div_self (paFact_ne α), one_smul]
    · rw [zero_div, zero_smul]
  simp only [e]
  rw [Finset.sum_ite_eq']

theorem gaussianInner_zero_left (q : ℕ) (G : EuclideanSpace ℂ ι → ℂ) : paIP q 0 G = 0 := by
  simp [paIP]

theorem gaussianInner_zero_right (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) : paIP q F 0 = 0 := by
  simp [paIP]

theorem gaussianInner_monomial_high {q c : ℕ} (hq : 1 ≤ q) {m : ι →₀ ℕ} (hm : m ∉ paS c)
    {G : EuclideanSpace ℂ ι → ℂ} (hG : G ∈ paPoly c) : paIP q (paMono m) G = 0 := by
  have hmm : paMono m ∈ paPoly (ι := ι) (max c m.degree) :=
    paMono_mem (mem_paS.2 (le_max_right _ _))
  have hup : paPoly (ι := ι) c ≤ paPoly (max c m.degree) := paPoly_mono (le_max_left _ _)
  induction hG using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨β, hβ, rfl⟩ := hx
    exact gaussianInner_monomial_orthogonal q (by rintro rfl; exact hm hβ)
  | zero => exact gaussianInner_zero_right q _
  | add x y hx hy ihx ihy =>
    rw [gaussianInner_conj_symm q (x + y) (paMono m), gaussianInner_add_left hq (hup hx) (hup hy) hmm, map_add,
      ← gaussianInner_conj_symm, ← gaussianInner_conj_symm, ihx, ihy, add_zero]
  | smul r x hx ihx =>
    rw [gaussianInner_conj_symm q (r • x) (paMono m), gaussianInner_smul_left, map_mul, ← gaussianInner_conj_symm, ihx, mul_zero]

theorem gaussianInner_polynomial_jet {q c d : ℕ} (hq : 1 ≤ q) {S G : EuclideanSpace ℂ ι → ℂ} (hS : S ∈ paPoly d)
    (hG : G ∈ paPoly c) : paIP q S G = paIP q (paJet c S) G := by
  have hupd : paPoly (ι := ι) d ≤ paPoly (max d c) := paPoly_mono (le_max_left _ _)
  have hupc : paPoly (ι := ι) c ≤ paPoly (max d c) := paPoly_mono (le_max_right _ _)
  induction hS using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    rw [paJet_mono]
    split_ifs with h
    · rfl
    · rw [gaussianInner_monomial_high hq h hG, gaussianInner_zero_left]
  | zero => rw [paJet_zero]
  | add x y hx hy ihx ihy =>
    rw [paJet_add c (paPoly_contDiff hx) (paPoly_contDiff hy),
      gaussianInner_add_left hq (hupd hx) (hupd hy) (hupc hG),
      gaussianInner_add_left hq (hupc (paJet_mem c x)) (hupc (paJet_mem c y)) (hupc hG), ihx, ihy]
  | smul r x hx ihx =>
    rw [paJet_smul c r (paPoly_contDiff hx), gaussianInner_smul_left, gaussianInner_smul_left, ihx]

end

end ReciprocityTheory.ChartRestriction.G.I2.FPw
