import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.AlternatingProductIntegral
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem pow_smul_mem_forms_powMul {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]
    (p : ℕ) (A B : Set K) (L : Set V) (q : ℕ) (b : K) (hb : b ∈ B) (y : ExteriorAlgebra K V)
    (hy : y ∈ forms A L q) : b ^ p • y ∈ forms {z | ∃ c ∈ B, ∃ a ∈ A, z = c ^ p * a} L q := by
  unfold forms at hy ⊢
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a', ha', v, hv, rfl⟩ := hx
    apply AddSubgroup.subset_closure
    exact ⟨b ^ p * a', ⟨b, hb, a', ha', rfl⟩, v, hv, by rw [smul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem phi_mem_forms : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) (f : ι → V →+ V) (h : ι → ι → V →+ K) (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)) (A : Subring K) (B : Set K) (L : Set V) (s : Finset ι), IsPhi p f h Φ → (∀ i ∈ s, ∀ v ∈ L, ExteriorAlgebra.ι K (f i v) ∈ forms (A : Set K) L 1) → (∀ i ∈ s, ∀ j ∈ s, ∀ v ∈ L, h i j v ∈ A) → ∀ (a q : ℕ) (t : Finset ι), t ⊆ s → q + t.card = a + 1 → ∀ x ∈ forms B L a, Φ x t ∈ forms {z | ∃ c ∈ B, ∃ b ∈ A, z = c ^ p * b} L q := by
  intro K _ V _ _ ι _ p f h Φ A B L s hΦ hf hh a q t hts hq x hx
  unfold forms at hx
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, v, hv, rfl⟩ := hx
    rw [show Φ (c • ExteriorAlgebra.ιMulti K a v) = c ^ p • alt f h a v from hΦ c a v, Pi.smul_apply]
    exact pow_smul_mem_forms_powMul p (A : Set K) B L q c hc _
      (GlobalTheory.T.alternating_product_integral f h A L s hf hh a v t hv hts q hq)
  | zero =>
    rw [map_zero, Pi.zero_apply]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add, Pi.add_apply]
    exact add_mem hx hy
  | neg x _ hx =>
    rw [map_neg, Pi.neg_apply]
    exact neg_mem hx

end GlobalTheory.DI
