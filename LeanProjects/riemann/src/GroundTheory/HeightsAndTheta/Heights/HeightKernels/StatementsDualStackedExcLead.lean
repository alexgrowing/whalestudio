import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcResidue
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

def stackedFormEval {K : Type} [Field K] [NumberField K] {i : ℕ} {F F' : HermLattice K i} {T : Type}
    (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F')) :
    MRing (stackedBlocks T) →+* MvPolynomial (Fin i) K :=
  eval₂Hom (Int.castRingHom _) fun
    | ⟨.inl _, t⟩ => ∑ j, C ((b' t : Fin i → K) j) * X j
    | ⟨.inr _, t⟩ => ∑ j, C ((b t : Fin i → K) j) * X j

def bidegree (d e : ℕ) : Unit ⊕ Unit → ℕ := Sum.elim (fun _ => d) (fun _ => e)

def DualStackedGraphBihomog.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ f ∈ stackedGraph b' a, ∃ (s : Finset (ℕ × ℕ)) (g : ℕ × ℕ → MRing (stackedBlocks T)),
      f = ∑ p ∈ s, g p ∧ ∀ p ∈ s, IsMultiHomog (g p) (bidegree p.1 p.2) ∧ stackedFormEval b b' (g p) = 0

def DualStackedExcLeadForm.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ (k : Type) [Field k] (α : T → k) (M : T → Fin i → k), IsExcResidueData b b' α M →
      ∀ (d e : ℕ) (f : MRing (stackedBlocks T)), IsMultiHomog f (bidegree d e) →
        stackedFormEval b b' f = 0 → linPointMap α M f = 0

namespace DualStackedExcLeadExample

theorem stackedFormEval_first {K : Type} [Field K] [NumberField K] {i : ℕ} {F F' : HermLattice K i} {T : Type}
    (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F')) (t : T) :
    stackedFormEval b b' (graphFirst t) = ∑ j, C ((b' t : Fin i → K) j) * X j := by
  simp [stackedFormEval, graphFirst]

theorem stackedFormEval_second {K : Type} [Field K] [NumberField K] {i : ℕ} {F F' : HermLattice K i} {T : Type}
    (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F')) (t : T) :
    stackedFormEval b b' (graphSecond t) = ∑ j, C ((b t : Fin i → K) j) * X j := by
  simp [stackedFormEval, graphSecond]

theorem isMultiHomog_first {T : Type} [Fintype T] (t : T) :
    IsMultiHomog (graphFirst t : MRing (stackedBlocks T)) (bidegree 1 0) := by
  classical
  intro m hm κ
  rw [graphFirst, support_X, Finset.mem_singleton] at hm
  subst hm
  rcases κ with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  · have key : ∀ s : T, ((⟨Sum.inl (), t⟩ : Σ κ, stackedBlocks T κ) = ⟨Sum.inl (), s⟩ ↔ t = s) :=
      fun s => ⟨fun h => by cases h; rfl, fun h => by rw [h]⟩
    simp [bidegree, Finsupp.single_apply, key]
    exact Finset.mem_univ _
  · have key : ∀ s : T, (⟨Sum.inl (), t⟩ : Σ κ, stackedBlocks T κ) ≠ ⟨Sum.inr (), s⟩ :=
      fun s h => by cases h
    simp [bidegree, key]

theorem example_relation :
    stackedFormEval dualBasisStandard DualStackedExcResidueExample.halfBasis
      (graphSecond () - C 2 * graphFirst ()) = 0 := by
  rw [map_sub, map_mul, stackedFormEval_first, stackedFormEval_second, dualBasisStandard_apply,
    DualStackedExcResidueExample.halfBasis_apply]
  simp only [stackedFormEval, oneDual, DualStackedExcResidueExample.halfDual]
  simp
  rw [← mul_assoc, ← map_ofNat C 2, ← C_mul, mul_inv_cancel₀ two_ne_zero, C_1, one_mul, sub_self]

theorem example_first_ne :
    stackedFormEval dualBasisStandard DualStackedExcResidueExample.halfBasis (graphFirst ()) ≠ 0 := by
  rw [stackedFormEval_first, DualStackedExcResidueExample.halfBasis_apply]
  intro h
  have h2 := congrArg (MvPolynomial.eval fun _ : Fin 1 => (1 : ℚ)) h
  simp [DualStackedExcResidueExample.halfDual] at h2

end DualStackedExcLeadExample

end

end GroundTheory.Heights₂.Heights
