import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelLinearOperationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelMulOfPosLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastAtEmbeddingRingOpsStatement

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)

namespace GlobalTheory.QFam.QSz

section

variable {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]} {N : ℕ}

theorem qAll_const {r : ℝ} {c : ℂ} (hc : Sz l lam r c) : QAll (Sz l lam r) N fun _ => c := by
  refine ⟨_, (GlobalTheory.T.hasQExpansionOfLevel_linear_operations N).2.2.2.1 c, fun n => ?_⟩
  by_cases h : n = 0
  · simpa only [h, if_true] using hc
  · simpa only [h, if_false] using (GlobalTheory.T.algebraicValuationAtLeastAtEmbedding_ring_ops l lam).1 r

theorem qAll_mono {r s : ℝ} {f : ℍ → ℂ} (h : r ≤ s) (hf : QAll (Sz l lam r) N f) : QAll (Sz l lam s) N f := by
  obtain ⟨a, ha, hs⟩ := hf
  exact ⟨a, ha, fun n => (GlobalTheory.T.algebraicValuationAtLeastAtEmbedding_ring_ops l lam).2.2.2.1 r s _ h (hs n)⟩

theorem qAll_add {r : ℝ} {f g : ℍ → ℂ} (hf : QAll (Sz l lam r) N f) (hg : QAll (Sz l lam r) N g) :
    QAll (Sz l lam r) N fun τ => f τ + g τ := by
  obtain ⟨a, ha, hs⟩ := hf
  obtain ⟨b, hb, ht⟩ := hg
  exact ⟨_, (GlobalTheory.T.hasQExpansionOfLevel_linear_operations N).1 f g a b ha hb, fun n => ((GlobalTheory.T.algebraicValuationAtLeastAtEmbedding_ring_ops l lam).2.1 r _ _ (hs n) (ht n)).1⟩

theorem qAll_sub {r : ℝ} {f g : ℍ → ℂ} (hf : QAll (Sz l lam r) N f) (hg : QAll (Sz l lam r) N g) :
    QAll (Sz l lam r) N fun τ => f τ - g τ := by
  obtain ⟨a, ha, hs⟩ := hf
  obtain ⟨b, hb, ht⟩ := hg
  exact ⟨_, (GlobalTheory.T.hasQExpansionOfLevel_linear_operations N).2.1 f g a b ha hb, fun n => ((GlobalTheory.T.algebraicValuationAtLeastAtEmbedding_ring_ops l lam).2.1 r _ _ (hs n) (ht n)).2⟩

theorem qAll_mul (hN : 0 < N) {r s : ℝ} {f g : ℍ → ℂ} (hf : QAll (Sz l lam r) N f) (hg : QAll (Sz l lam s) N g) :
    QAll (Sz l lam (r + s)) N fun τ => f τ * g τ := by
  obtain ⟨a, ha, hs⟩ := hf
  obtain ⟨b, hb, ht⟩ := hg
  refine ⟨_, GlobalTheory.T.hasQExpansionOfLevel_mul_of_pos_level N f g a b hN ha hb, fun n => ?_⟩
  exact (GlobalTheory.T.algebraicValuationAtLeastAtEmbedding_ring_ops l lam).2.2.2.2.2 _ _ _ (fun p : ℕ × ℕ => a p.1 * b p.2)
    fun p _ => (GlobalTheory.T.algebraicValuationAtLeastAtEmbedding_ring_ops l lam).2.2.1 r s _ _ (hs _) (ht _)

theorem qAll_one : QAll (Sz l lam 0) N fun _ => 1 :=
  qAll_const (by simpa using (GlobalTheory.T.algebraicValuationAtLeastAtEmbedding_ring_ops l lam).2.2.2.2.1 1)

theorem qAll_pow (hN : 0 < N) {r : ℝ} {f : ℍ → ℂ} (k : ℕ) (hf : QAll (Sz l lam r) N f) :
    QAll (Sz l lam (k * r)) N fun τ => f τ ^ k := by
  induction k with
  | zero => simpa using (qAll_one : QAll (Sz l lam 0) N fun _ => 1)
  | succ k ih =>
    have h := qAll_mul hN ih hf
    have e : ((k + 1 : ℕ) : ℝ) * r = k * r + r := by push_cast; ring
    rw [e]
    simpa only [pow_succ] using h

theorem qAll_sum {κ : Type} (t : Finset κ) {r : ℝ} {f : κ → ℍ → ℂ} (hf : ∀ k ∈ t, QAll (Sz l lam r) N (f k)) :
    QAll (Sz l lam r) N fun τ => ∑ k ∈ t, f k τ := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (qAll_const ((GlobalTheory.T.algebraicValuationAtLeastAtEmbedding_ring_ops l lam).1 r) : QAll (Sz l lam r) N fun _ => 0)
  | insert k t hk ih =>
    simp only [Finset.sum_insert hk]
    exact qAll_add (hf k (Finset.mem_insert_self k t)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem qAll_prod (hN : 0 < N) {κ : Type} (t : Finset κ) {r : κ → ℝ} {f : κ → ℍ → ℂ}
    (hf : ∀ k ∈ t, QAll (Sz l lam (r k)) N (f k)) :
    QAll (Sz l lam (∑ k ∈ t, r k)) N fun τ => ∏ k ∈ t, f k τ := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (qAll_one : QAll (Sz l lam 0) N fun _ => 1)
  | insert k t hk ih =>
    simp only [Finset.sum_insert hk, Finset.prod_insert hk]
    exact qAll_mul hN (hf k (Finset.mem_insert_self k t)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

end

theorem qAll_sz_ring : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), ∀ (N : ℕ), 0 < N → (∀ (r : ℝ) (c : ℂ), Sz l lam r c → QAll (Sz l lam r) N fun _ => c) ∧ (∀ (r s : ℝ) f, r ≤ s → QAll (Sz l lam r) N f → QAll (Sz l lam s) N f) ∧ (∀ (r : ℝ) f g, QAll (Sz l lam r) N f → QAll (Sz l lam r) N g → (QAll (Sz l lam r) N fun τ => f τ + g τ) ∧ QAll (Sz l lam r) N fun τ => f τ - g τ) ∧ (∀ (r s : ℝ) f g, QAll (Sz l lam r) N f → QAll (Sz l lam s) N g → QAll (Sz l lam (r + s)) N fun τ => f τ * g τ) ∧ (∀ (r : ℝ) f (k : ℕ), QAll (Sz l lam r) N f → QAll (Sz l lam (k * r)) N fun τ => f τ ^ k) ∧ (∀ (κ : Type) (t : Finset κ) (r : ℝ) (f : κ → ℍ → ℂ), (∀ k ∈ t, QAll (Sz l lam r) N (f k)) → QAll (Sz l lam r) N fun τ => ∑ k ∈ t, f k τ) ∧ (∀ (κ : Type) (t : Finset κ) (r : κ → ℝ) (f : κ → ℍ → ℂ), (∀ k ∈ t, QAll (Sz l lam (r k)) N (f k)) → QAll (Sz l lam (∑ k ∈ t, r k)) N fun τ => ∏ k ∈ t, f k τ) :=
  fun _ _ _ _ hN => ⟨fun _ _ h => qAll_const h, fun _ _ _ h hf => qAll_mono h hf,
    fun _ _ _ hf hg => ⟨qAll_add hf hg, qAll_sub hf hg⟩, fun _ _ _ _ hf hg => qAll_mul hN hf hg,
    fun _ _ k hf => qAll_pow hN k hf, fun _ t _ _ hf => qAll_sum t hf, fun _ t _ _ hf => qAll_prod hN t hf⟩

end GlobalTheory.QFam.QSz
