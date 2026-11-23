import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AdditionGraphThetaObjectCutOutBoundedDegree
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additionGraph_thetaObject_cutOut_bounded_degree : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)), ∃ (Q : Polynomial ℚ) (d : ℕ), ∀ (K : Type) [Field K] [IsAlgClosed K] (β : o →+* K) (t : TObj g ((n ^ j) ^ 2) J b (spMap β)) σ (p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → K) (M₂ : LB ((Over.mk (𝟙 (Sp K)) ⊗ t.A) ⊗ (Over.mk (𝟙 (Sp K)) ⊗ t.A)).left) (th₂ : Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2) → M₂.Sec), M₂.IsLB → t.Emb (n ^ 2) (Over.mk (𝟙 _)) σ → (∀ (T : Type) [CommRing T] (x : Sp T ⟶ ((Over.mk (𝟙 (Sp K)) ⊗ t.A) ⊗ (Over.mk (𝟙 (Sp K)) ⊗ t.A)).left) (v₁ v₂ : _ → T), SecCoord _ σ (x ≫ (fst (Over.mk (𝟙 (Sp K)) ⊗ t.A) (Over.mk (𝟙 (Sp K)) ⊗ t.A)).left) v₁ → SecCoord _ σ (x ≫ (snd (Over.mk (𝟙 (Sp K)) ⊗ t.A) (Over.mk (𝟙 (Sp K)) ⊗ t.A)).left) v₂ → SecCoord M₂ th₂ x (fun i => v₁ i.1 * v₂ i.2)) → (∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j)).left (p h)) → CutBy (graphIdeal ((Over.mk (𝟙 (Sp K)) ⊗ t.A) ⊗ (Over.mk (𝟙 (Sp K)) ⊗ t.A)).hom M₂ th₂ (𝟙 _) _ σ (lift (toUnit _ ≫ (Over.homMk (𝟙 _) (by simp) : 𝟙_ (Over (Sp K)) ⟶ Over.mk (𝟙 (Sp K)))) ((fst (Over.mk (𝟙 (Sp K)) ⊗ t.A) (Over.mk (𝟙 (Sp K)) ⊗ t.A) ≫ snd _ t.A) * (snd (Over.mk (𝟙 (Sp K)) ⊗ t.A) (Over.mk (𝟙 (Sp K)) ⊗ t.A) ≫ snd _ t.A))).left) Q d (fun (h : Ix g ((n ^ j) ^ 2) × Ix g ((n ^ j) ^ 2)) i => p h.1 i.1.1 * p h.2 i.1.2 * p (h.1 + h.2) i.2) := by
  first | exact @GlobalTheory.cutBy_graph_addition | exact GlobalTheory.cutBy_graph_addition | (intros; apply GlobalTheory.cutBy_graph_addition <;> assumption)
