import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivativeCechCocycleInvariantVectorFieldIsCobou
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivative_cechCocycle_invariantVectorField_isCoboundary : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (J : Type) (V : J → A.left.Opens), ⨆ a, V a = ⊤ → ∀ φ : ∀ a b, Γ(A.left, V a ⊓ V b), (∀ (a b c : J) (P : GPt A), P.In (V a) → P.In (V b) → P.In (V c) → valR P.x _ (φ a b) + valR P.x _ (φ b c) = valR P.x _ (φ a c)) → ∀ v : epsR K ⟶ A, IsTangent v → ∃ ψ : J → PtFn (A.hom ≫ 𝟙 (Sp K)), (∀ a, IsNat (V a) (ψ a)) ∧ ∀ (a b : J) (P : GPt A), P.In (V a) → P.In (V b) → (valR (P.trx v) _ (φ a b)).snd = ψ a P - ψ b P := by
  first | exact @GlobalTheory.CechInv.deriv_cocycle_isCoboundary | exact GlobalTheory.CechInv.deriv_cocycle_isCoboundary | (intros; apply GlobalTheory.CechInv.deriv_cocycle_isCoboundary <;> assumption)
