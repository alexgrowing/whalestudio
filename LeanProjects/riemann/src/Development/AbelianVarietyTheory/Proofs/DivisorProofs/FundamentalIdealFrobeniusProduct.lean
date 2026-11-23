import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactRationalBoundedDenominators

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.AfPVecDen

theorem main : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [AddCommGroup V] [Module ℚ V] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℚ V) (Ω : Set (AfP p ⊗[ℚ] V)),
    @IsCompact _ (moduleTopology (AfP p) (AfP p ⊗[ℚ] V)) Ω →
    ∃ M : ℕ, 0 < M ∧ ∀ c : V, (1 : AfP p) ⊗ₜ[ℚ] c ∈ Ω → ∀ i, ∃ (k : ℤ) (e : ℕ),
      b.repr c i * ((M : ℚ) * (p : ℚ) ^ e) = k := by
  intro p _ V _ _ ι _ b Ω hΩ
  letI : TopologicalSpace (AfP p ⊗[ℚ] V) := moduleTopology (AfP p) (AfP p ⊗[ℚ] V)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] V) := ⟨rfl⟩
  let b' := b.baseChange (AfP p)
  have hcont : ∀ i, Continuous (b'.coord i) := fun i =>
    IsModuleTopology.continuous_of_linearMap (b'.coord i)
  have hcpt : ∀ i, IsCompact ((b'.coord i) '' Ω) := fun i => hΩ.image (hcont i)
  choose m hm0 hm using fun i => GlobalTheory.T.compact_rational_bounded_denominators p _ (hcpt i)
  refine ⟨∏ i, m i, Finset.prod_pos (fun i _ => hm0 i), fun c hc i => ?_⟩
  have hval : b'.coord i ((1 : AfP p) ⊗ₜ[ℚ] c) = algebraMap ℚ (AfP p) (b.repr c i) := by
    simp only [b', Module.Basis.coord_apply, Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
  obtain ⟨k, e, hk⟩ := hm i (b.repr c i) (hval ▸ ⟨_, hc, rfl⟩)
  obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  refine ⟨k * r, e, ?_⟩
  rw [hr]
  push_cast
  rw [← hk]
  ring

end GlobalTheory.AfPVecDen
