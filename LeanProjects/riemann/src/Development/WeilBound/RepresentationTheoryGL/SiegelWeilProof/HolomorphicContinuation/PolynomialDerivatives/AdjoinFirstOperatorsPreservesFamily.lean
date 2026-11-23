import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.FformSmulRight

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.Core

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

theorem pderiv_eq_zero_of_supported {S : Set (Fin m × Fin n × Bool)} {g : PX m n} (hg : g ∈ supported ℂ S)
    {k : Fin m × Fin n × Bool} (hk : k ∉ S) : pderiv k g = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro h
  exact hk ((mem_supported.mp hg) h)

theorem pderiv_mem_supported {S : Set (Fin m × Fin n × Bool)} {g : PX m n} (hg : g ∈ supported ℂ S)
    (k : Fin m × Fin n × Bool) : pderiv k g ∈ supported ℂ S := by
  rw [supported_eq_adjoin_X] at hg
  induction hg using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, -, rfl⟩ := hx
    rw [pderiv_X]
    rcases eq_or_ne i k with rfl | h
    · simp only [Pi.single_eq_same]; exact Subalgebra.one_mem _
    · rw [Pi.single_eq_of_ne h]; exact Subalgebra.zero_mem _
  | algebraMap r => simp [Subalgebra.zero_mem]
  | add x y _ _ hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
  | mul x y hx' hy' hx hy =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    have hx'' : x ∈ supported ℂ S := by rw [supported_eq_adjoin_X]; exact hx'
    have hy'' : y ∈ supported ℂ S := by rw [supported_eq_adjoin_X]; exact hy'
    exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ hx'' hy) (Subalgebra.mul_mem _ hy'' hx)

theorem mem_F1_iff_supported (ε : Fin m → Bool) (f : PX m n) : f ∈ F1 ε ↔ f ∈ supported ℂ {k | inF1 ε k} := Iff.rfl

theorem variable_mem_first_family (ε : Fin m → Bool) {k : Fin m × Fin n × Bool} (hk : inF1 ε k) : (X k : PX m n) ∈ F1 ε :=
  (mem_F1_iff_supported ε _).2 (X_mem_supported.2 hk)

theorem compact_operator_mul_second_family (ε : Fin m → Bool) (i j : Fin n) (f g : PX m n) (hg : g ∈ F2 ε) :
    KopL ε i j (f * g) = KopL ε i j f * g := by
  have h0 : ∀ k : Fin m × Fin n × Bool, inF1 ε k → pderiv k g = 0 := fun k hk =>
    pderiv_eq_zero_of_supported hg (by simpa using hk)
  have hK : ∀ h : PX m n, KopL ε i j h = ∑ a ∈ Finset.univ.filter (fun a => ε a = true), X (a, i, false) * pderiv (a, j, false) h -
      ∑ a ∈ Finset.univ.filter (fun a => ε a = false), X (a, j, true) * pderiv (a, i, true) h := by
    intro h; simp [KopL, LinearMap.sum_apply]
  rw [hK, hK]
  simp only [Derivation.leibniz, smul_eq_mul]
  have e1 : ∀ a ∈ Finset.univ.filter (fun a => ε a = true),
      X (a, i, false) * (f * pderiv (a, j, false) g + g * pderiv (a, j, false) f) =
        X (a, i, false) * pderiv (a, j, false) f * g := by
    intro a ha
    rw [h0 (a, j, false) (by simp [inF1, (Finset.mem_filter.mp ha).2])]; ring
  have e2 : ∀ a ∈ Finset.univ.filter (fun a => ε a = false),
      X (a, j, true) * (f * pderiv (a, i, true) g + g * pderiv (a, i, true) f) =
        X (a, j, true) * pderiv (a, i, true) f * g := by
    intro a ha
    rw [h0 (a, i, true) (by simp [inF1, (Finset.mem_filter.mp ha).2])]; ring
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, ← Finset.sum_mul, ← Finset.sum_mul, sub_mul]

theorem compact_algebra_mul_second_family (ε : Fin m → Bool) (w : Module.End ℂ (PX m n)) (hw : w ∈ kAlg ε) (f g : PX m n) (hg : g ∈ F2 ε) :
    w (f * g) = w f * g := by
  induction hw using Algebra.adjoin_induction generalizing f with
  | mem x hx =>
    obtain ⟨ij, rfl⟩ := hx
    exact compact_operator_mul_second_family ε ij.1 ij.2 f g hg
  | algebraMap r => simp [Algebra.algebraMap_eq_smul_one, smul_mul_assoc]
  | add x y _ _ hx hy => simp [hx, hy, add_mul]
  | mul x y _ _ hx hy => simp only [Module.End.mul_apply, hy, hx]

theorem first_operator_preserves_first_family (ε : Fin m → Bool) (c : ℝ) (a b : Fin m) (f : PX m n) (hf : f ∈ F1 ε) : D1 ε c a b f ∈ F1 ε := by
  have hp : ∀ k (g : PX m n), g ∈ F1 ε → pderiv k g ∈ F1 ε := fun k g hg => pderiv_mem_supported hg k
  have hm : ∀ g h : PX m n, g ∈ F1 ε → h ∈ F1 ε → g * h ∈ F1 ε := fun g h hg hh => Subalgebra.mul_mem _ hg hh
  unfold D1
  split_ifs with h1 h2 h2
  · refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ => hm _ _ (variable_mem_first_family ε ?_) (hp _ _ hf))
    simp [inF1, h2]
  · refine Submodule.sum_mem _ fun i _ => hm _ _ (variable_mem_first_family ε ?_) (hp _ _ hf)
    simp [inF1, ← h1]; simpa using h2
  · refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
      hm _ _ (hm _ _ (variable_mem_first_family ε ?_) (variable_mem_first_family ε ?_)) hf)
    · simp [inF1, h2]
    · simp [inF1]; cases hb : ε b <;> simp_all
  · refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => hp _ _ (hp _ _ hf))

theorem adjoin_first_operators_preserves_family (ε : Fin m → Bool) (c : ℝ) (B : Module.End ℂ (PX m n)) (hBF : ∀ f ∈ F1 ε, B f ∈ F1 ε)
    (hB : ∀ a b, ∀ f ∈ F1 ε, B (D1 ε c a b f) = D1 ε c a b (B f)) (w : Module.End ℂ (PX m n))
    (hw : w ∈ Algebra.adjoin ℂ (Set.range fun ab : Fin m × Fin m => firstFamilyOperatorEnd (n := n) ε c ab.1 ab.2)) :
    (∀ f ∈ F1 ε, w f ∈ F1 ε) ∧ ∀ f ∈ F1 ε, B (w f) = w (B f) := by
  induction hw using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨ab, rfl⟩ := hx
    exact ⟨fun f hf => first_operator_preserves_first_family ε c ab.1 ab.2 f hf, fun f hf => hB ab.1 ab.2 f hf⟩
  | algebraMap r =>
    refine ⟨fun f hf => by simpa [Algebra.algebraMap_eq_smul_one] using Submodule.smul_mem _ r hf, fun f _ => ?_⟩
    simp [Algebra.algebraMap_eq_smul_one]
  | add x y _ _ hx hy =>
    exact ⟨fun f hf => by simpa using Submodule.add_mem _ (hx.1 f hf) (hy.1 f hf),
      fun f hf => by simp [hx.2 f hf, hy.2 f hf]⟩
  | mul x y _ _ hx hy =>
    exact ⟨fun f hf => hx.1 _ (hy.1 f hf), fun f hf => by
      simp only [Module.End.mul_apply]; rw [hx.2 _ (hy.1 f hf), hy.2 f hf]⟩

end PositivityTheory.Rg.Sw.LC.Core
