import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

namespace GlobalTheory.OrbFinAf

theorem ratCast_mem_intV_eventually (p : ℕ) [Fact p.Prime] (q : ℚ) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
      algebraMap ℚ (Qv v) q ∈ v.1.adicCompletionIntegers ℚ := by
  have h : ∀ᶠ w in (Filter.cofinite : Filter (HeightOneSpectrum ℤ)),
      algebraMap ℚ (w.adicCompletion ℚ) q ∈ w.adicCompletionIntegers ℚ :=
    (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q).2.mono fun _ hv => hv
  exact (Subtype.val_injective.tendsto_cofinite).eventually h

variable {p : ℕ} [Fact p.Prime]

theorem basV_repr_tmul (G : HTGroup p) (v : AwayP p) (r : Qv v) (c : G.C) (k : Fin (Module.finrank ℚ G.C)) :
    (basV G v).repr (r ⊗ₜ c) k = r * algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr c k) := by
  simp [basV, Algebra.TensorProduct.basis_repr_tmul]

theorem eq_sum_tmul (G : HTGroup p) (v : AwayP p) (y : Qv v ⊗[ℚ] G.C) :
    y = ∑ i, (basV G v).repr y i ⊗ₜ (Module.finBasis ℚ G.C i) := by
  conv_lhs => rw [← (basV G v).sum_repr y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [basV, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem isIntV_of_eq_sum (G : HTGroup p) (v : AwayP p) {ι : Type*} (s : Finset ι) (r : ι → Qv v) (c : ι → G.C)
    (hr : ∀ i ∈ s, r i ∈ v.1.adicCompletionIntegers ℚ)
    (hc : ∀ i ∈ s, ∀ k, algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr (c i) k) ∈ v.1.adicCompletionIntegers ℚ) :
    IsIntV G v (∑ i ∈ s, r i ⊗ₜ c i) := by
  intro k
  rw [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
  exact sum_mem fun i hi => by rw [basV_repr_tmul]; exact mul_mem (hr i hi) (hc i hi k)

theorem intV_order_eventually : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), IsIntV G v 1 ∧ (∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) ∧ (∀ y : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v (starT G.star (Qv v) y).unop) := by
  intro p _ G
  set b := Module.finBasis ℚ G.C
  have H := ((Filter.eventually_all.2 fun k => ratCast_mem_intV_eventually p (b.repr 1 k)).and
    (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => Filter.eventually_all.2 fun k =>
      ratCast_mem_intV_eventually p (b.repr (b i * b j) k))).and
    (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun k =>
      ratCast_mem_intV_eventually p (b.repr (G.star (b i)).unop k))
  refine H.mono fun v ⟨⟨h1, hm⟩, hs⟩ => ⟨?_, ?_, ?_⟩
  · intro k
    rw [Algebra.TensorProduct.one_def, basV_repr_tmul, one_mul]
    exact h1 k
  · intro y z hy hz
    have e : y * z = ∑ ij : Fin (Module.finrank ℚ G.C) × Fin (Module.finrank ℚ G.C),
        ((basV G v).repr y ij.1 * (basV G v).repr z ij.2) ⊗ₜ (b ij.1 * b ij.2) := by
      conv_lhs => rw [eq_sum_tmul G v y, eq_sum_tmul G v z]
      rw [Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product]
      simp only [Algebra.TensorProduct.tmul_mul_tmul]
      rfl
    rw [e]
    exact isIntV_of_eq_sum G v _ _ _ (fun ij _ => mul_mem (hy ij.1) (hz ij.2)) (fun ij _ k => hm ij.1 ij.2 k)
  · intro y hy
    have e : (starT G.star (Qv v) y).unop = ∑ i, (basV G v).repr y i ⊗ₜ (G.star (b i)).unop := by
      conv_lhs => rw [eq_sum_tmul G v y]
      rw [map_sum, ← MulOpposite.opAddEquiv_symm_apply, map_sum]
      exact Finset.sum_congr rfl fun i _ => starT_tmul G.star (Qv v) _ _
    rw [e]
    exact isIntV_of_eq_sum G v _ _ _ (fun i _ => hy i) (fun i _ k => hs i k)

end GlobalTheory.OrbFinAf
