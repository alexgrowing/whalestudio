import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualTopSimpleStacked
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

def stackedDiag {T : Type} [DecidableEq T] (a : T → ℤ) : ∀ _ : Unit, T → T → ℤ :=
  fun _ t s => if t = s then a t else 0

abbrev stackedBlocks (T : Type) : Unit ⊕ Unit → Type := Sum.elim (dualBlocks T) (dualBlocks T)

def stackedGraph {K : Type} [Field K] [NumberField K] {i : ℕ} {F' : HermLattice K i} {T : Type} [Fintype T]
    [DecidableEq T] (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) : Ideal (MRing (stackedBlocks T)) :=
  graphIdeal (dualIdeal b') (linForm (stackedDiag a))

def graphFirst {T : Type} (t : T) : MRing (stackedBlocks T) := X ⟨Sum.inl (), t⟩

def graphSecond {T : Type} (t : T) : MRing (stackedBlocks T) := X ⟨Sum.inr (), t⟩

def degFirst : Unit ⊕ Unit → ℤ := pullDeg (Sum.inl : Unit → Unit ⊕ Unit) fun _ => 1

def degSecond : Unit ⊕ Unit → ℤ := pullDeg (Sum.inr : Unit → Unit ⊕ Unit) fun _ => 1

def DualStackedGraphImage.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    imageZ inrV (stackedGraph b' a) = dualIdeal b ∧
      ∀ (G : GenFibre inrV (stackedGraph b' a))
        (J : IFamily G.Φ (fibreIdx (stackedBlocks T) (Sum.inr : Unit → Unit ⊕ Unit))),
        IsFieldIntersection J → J (fibreIdeal Sum.inr G) 0 Fin.elim0 = 1

def DualStackedGraphHorizontal.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ (t : T) (W : Ideal (MRing (stackedBlocks T))), IsHorizontal W →
      (W ∈ divSupp (stackedGraph b' a) (graphSecond t) ↔
        W ∈ divSupp (stackedGraph b' a) (C (a t) * graphFirst t)) ∧
      (W ∈ divSupp (stackedGraph b' a) (graphSecond t) →
        multAt (stackedGraph b' a ⊔ Ideal.span {graphSecond t}) W =
          multAt (stackedGraph b' a ⊔ Ideal.span {C (a t) * graphFirst t}) W)

def DualStackedGraphFibre.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ (t : T) (L : Fin (i - 1) → HermLine (stackedBlocks T)),
      (∀ j, (L j).a = degFirst ∨ (L j).a = degSecond) →
      ((∀ j, (L j).a = degSecond) →
        vertR (stackedGraph b' a) L (graphSecond t) - vertR (stackedGraph b' a) L (C (a t) * graphFirst t) =
          -∑ s, Real.log |(a s : ℝ)|) ∧
      ((∃ j, (L j).a = degFirst) →
        vertR (stackedGraph b' a) L (graphSecond t) - vertR (stackedGraph b' a) L (C (a t) * graphFirst t) = 0)

example {T : Type} : ∀ j : Fin (1 - 1), ((Fin.elim0 j : HermLine (stackedBlocks T))).a = degFirst ∨
    ((Fin.elim0 j : HermLine (stackedBlocks T))).a = degSecond :=
  fun j => j.elim0

theorem degFirst_inr : degFirst (Sum.inr ()) = 0 := by
  rw [degFirst, pullDeg, Function.extend_apply' _ _ _ (by rintro ⟨u, hu⟩; exact Sum.inl_ne_inr hu)]
  rfl

theorem degSecond_inr : degSecond (Sum.inr ()) = 1 := by
  rw [degSecond, pullDeg, Sum.inr_injective.extend_apply]

end

end GroundTheory.Heights₂.Heights
