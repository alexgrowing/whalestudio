import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.OrbFinAf

variable {p : ℕ} [Fact p.Prime]

theorem basV_repr_mul (G : HTGroup p) (v : AwayP p) (a b : Qv v ⊗[ℚ] G.C) (k : Fin (Module.finrank ℚ G.C)) :
    (basV G v).repr (a * b) k = ∑ i, ∑ j, (basV G v).repr a i * (basV G v).repr b j *
      algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr
        (Module.finBasis ℚ G.C i * Module.finBasis ℚ G.C j) k) := by
  conv_lhs => rw [← (basV G v).sum_repr a, ← (basV G v).sum_repr b]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul, map_sum, map_smul, Finset.sum_apply',
    Finsupp.smul_apply, smul_eq_mul, basV, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.basis_repr_tmul,
    Finsupp.mapRange_apply]
  rw [Finset.sum_comm]

omit [Fact p.Prime] in

theorem eventually_rat_mem_integers (q : ℚ) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
      algebraMap ℚ (Qv v) q ∈ v.1.adicCompletionIntegers ℚ := by
  have h : ∀ᶠ w in (Filter.cofinite : Filter (HeightOneSpectrum ℤ)),
      algebraMap ℚ (w.adicCompletion ℚ) q ∈ w.adicCompletionIntegers ℚ :=
    (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q).2
  exact Subtype.val_injective.tendsto_cofinite.eventually h

theorem isIntV_mul_eventually (G : HTGroup p) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a b : Qv v ⊗[ℚ] G.C,
      IsIntV G v a → IsIntV G v b → IsIntV G v (a * b) := by
  have h : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ i j k : Fin (Module.finrank ℚ G.C),
      algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr
        (Module.finBasis ℚ G.C i * Module.finBasis ℚ G.C j) k) ∈ v.1.adicCompletionIntegers ℚ := by
    simp only [Filter.eventually_all]
    intro i j k
    exact eventually_rat_mem_integers _
  filter_upwards [h] with v hv a b ha hb k
  rw [basV_repr_mul]
  exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ =>
    Subring.mul_mem _ (Subring.mul_mem _ (ha i) (hb j)) (hv i j k)

theorem isIntV_mul_eventually' : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p),
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a b : Qv v ⊗[ℚ] G.C,
      IsIntV G v a → IsIntV G v b → IsIntV G v (a * b) :=
  fun _ _ G => isIntV_mul_eventually G

end GlobalTheory.OrbFinAf
