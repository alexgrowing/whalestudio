import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

namespace GlobalTheory.OrbFinAfFixed

theorem rat_eventually_int (p : ℕ) (q : ℚ) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
      algebraMap ℚ (Qv v) q ∈ v.1.adicCompletionIntegers ℚ := by
  have h : ∀ᶠ w in (Filter.cofinite : Filter (HeightOneSpectrum ℤ)),
      algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q w ∈ w.adicCompletionIntegers ℚ :=
    (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q).2
  have h2 : ∀ᶠ w in (Filter.cofinite : Filter (HeightOneSpectrum ℤ)),
      algebraMap ℚ (w.adicCompletion ℚ) q ∈ w.adicCompletionIntegers ℚ :=
    h.mono fun w hw => by rwa [FiniteAdeleRing.algebraMap_apply] at hw
  exact (Subtype.val_injective.tendsto_cofinite).eventually h2

theorem basV_repr_one_tmul (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) (c : G.C) (i) :
    (basV G v).repr ((1 : Qv v) ⊗ₜ[ℚ] c) i = algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr c i) := by
  simp [basV, Algebra.TensorProduct.basis_repr_tmul]

theorem isIntV_one_tmul_eventually : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (c : G.C),
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), IsIntV G v ((1 : Qv v) ⊗ₜ[ℚ] c) := by
  intro p _ G c
  have h : ∀ i, ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
      algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr c i) ∈ v.1.adicCompletionIntegers ℚ :=
    fun i => rat_eventually_int p _
  refine (Filter.eventually_all.2 h).mono fun v hv i => ?_
  rw [basV_repr_one_tmul]
  exact hv i

end GlobalTheory.OrbFinAfFixed
