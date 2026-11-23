import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntBilinFormToRealMemBalancedPsdCone
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory

theorem lt_of_notMem_ratSpan_of_mem_ratSpan (X : Type) [AddCommGroup X] (m m' : ℕ)
    (δ : Fin m → LinearMap.BilinForm ℤ X) (ε : Fin m' → LinearMap.BilinForm ℤ X)
    (w : LinearMap.BilinForm ℤ X) (hδ : LinearIndependent ℤ δ)
    (hw : ¬ ∃ (M : ℕ) (a : Fin m → ℤ), 0 < M ∧ (M : ℤ) • w = ∑ i, a i • δ i)
    (hδε : ∀ j, ∃ (k : ℕ) (c : Fin m' → ℤ), 0 < k ∧ (k : ℤ) • δ j = ∑ i, c i • ε i)
    (hwε : ∃ (k : ℕ) (c : Fin m' → ℤ), 0 < k ∧ (k : ℤ) • w = ∑ i, c i • ε i) : m < m' := by
  classical
  have hind : LinearIndependent ℤ (Fin.cons w δ : Fin (m + 1) → LinearMap.BilinForm ℤ X) := by
    refine LinearIndependent.fin_cons' w δ hδ ?_
    intro c y hy' hy
    obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hy'
    by_contra hc
    apply hw
    have h1 : c • w = - ∑ i, b i • δ i := eq_neg_of_add_eq_zero_left hy
    rcases lt_or_gt_of_ne hc with h | h
    · refine ⟨c.natAbs, b, Int.natAbs_pos.2 hc, ?_⟩
      rw [Int.natCast_natAbs, abs_of_neg h, neg_smul, h1, neg_neg]
    · refine ⟨c.natAbs, fun i => - b i, Int.natAbs_pos.2 hc, ?_⟩
      rw [Int.natCast_natAbs, abs_of_pos h, h1, ← Finset.sum_neg_distrib]
      simp only [neg_smul]
  have hall : ∀ i : Fin (m + 1), ∃ k : ℤ, k ≠ 0 ∧
      k • (Fin.cons w δ : Fin (m + 1) → LinearMap.BilinForm ℤ X) i ∈
        Submodule.span ℤ (Set.range ε) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · obtain ⟨k, c, hk, h⟩ := hwε
      refine ⟨k, by exact_mod_cast hk.ne', ?_⟩
      exact (Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨c, by simpa using h.symm⟩
    · obtain ⟨k, c, hk, h⟩ := hδε j
      refine ⟨k, by exact_mod_cast hk.ne', ?_⟩
      exact (Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨c, by simpa using h.symm⟩
  choose k hk0 hk using hall
  have hind2 : LinearIndependent ℤ
      (fun i => k i • (Fin.cons w δ : Fin (m + 1) → LinearMap.BilinForm ℤ X) i) := by
    rw [Fintype.linearIndependent_iff] at hind ⊢
    intro g hg i
    have := hind (fun i => g i * k i) (by simpa only [mul_smul] using hg) i
    exact (mul_eq_zero.1 this).resolve_right (hk0 i)
  have hle := linearIndependent_le_span' _ hind2 (Set.range ε) (by
    rintro _ ⟨i, rfl⟩
    exact hk i)
  have h2 : Fintype.card (Set.range ε) ≤ m' := by
    simpa using Fintype.card_range_le ε
  rw [Cardinal.mk_fin] at hle
  have h3 : m + 1 ≤ Fintype.card (Set.range ε) := by exact_mod_cast hle
  omega

end GlobalTheory
