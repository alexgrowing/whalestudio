import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcLead
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

namespace StackedExceptionalBaseBound

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F F' : HermLattice K i} {T : Type} [Fintype T]

theorem centre_mem {b : Module.Basis T ℤ (dualLattice F)} {b' : Module.Basis T ℤ (dualLattice F')} {a : T → ℤ}
    (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) {k : Type} [Field k] {α : T → k}
    {M : T → Fin i → k} (hres : IsExcResidueData b b' α M) (t : T) :
    C (a t) * graphFirst t ∈ linPrime α M := by
  obtain ⟨ρ, ρ', σ, -, -, -, hker, -, -, hα, -⟩ := hres
  have hmem : ((a t • b' t : dualLattice F') : Fin i → K) ∈ dualLattice F := by
    rw [Submodule.coe_smul_of_tower, ← hab t]
    exact (b t).2
  have h0 : ((a t : ℤ) : k) * α t = 0 := by
    rw [hα t, ← zsmul_eq_mul, ← map_zsmul]
    exact (hker _).mpr hmem
  have h1 : linPointMap α M (C (a t)) = C ((a t : k)) := by simp [linPointMap]
  rw [linPrime, RingHom.mem_ker, map_mul, h1, LinPrimeExample.linPointMap_first, ← mul_assoc, ← C_mul, h0, C_0,
    zero_mul]

end StackedExceptionalBaseBound

open StackedExceptionalBaseBound in

theorem DualStackedExcBaseLe.proof (hBihom : DualStackedGraphBihomog.Statement)
    (hLead : DualStackedExcLeadForm.Statement) : DualStackedExcBaseLe.Statement := by
  intro K _ _ i F F' T _ _ b b' a hi hlt hcov hab k _ α M hres
  refine sup_le ?_ ?_
  · intro f hf
    obtain ⟨s, g, rfl, hg⟩ := hBihom K i F F' T b b' a hab f hf
    rw [linPrime, RingHom.mem_ker, map_sum]
    exact Finset.sum_eq_zero fun p hp =>
      hLead K i F F' T b b' a hi hlt hcov hab k α M hres p.1 p.2 (g p) (hg p hp).1 (hg p hp).2
  · rw [Ideal.span_le, Set.range_subset_iff]
    exact centre_mem hab hres

end

end GroundTheory.Heights₂.Heights
