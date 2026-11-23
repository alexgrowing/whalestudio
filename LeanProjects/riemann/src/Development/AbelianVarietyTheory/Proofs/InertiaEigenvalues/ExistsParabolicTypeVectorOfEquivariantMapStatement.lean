import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsParabolicTypeVectorOfEquivariantMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_parabolicTypeVector_of_equivariantMap : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] (α n : Type) [Fintype α] [LinearOrder α] [Fintype n] [DecidableEq n] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ n) (X : α → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (s : ∀ a, Representation ℂ (GL (m a) F) (X a)) (a : α) (θ : (ZMod p)ˣ →* ℂˣ) (χ : Fˣ →* ℂˣ) (U : Type) [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ (GL n (ZMod p)) U) (φ : U →ₗ[ℂ] IndSp e (piTensor s)), resCard F = p → CharLift θ χ → (∀ g ∈ KO F (m a), ∀ v, s a g v = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v) → φ ≠ 0 → (∀ (g : GL n (ZMod p)) (h : GL n F), IsLift g h → ∀ w, multiProd e s h (φ w) = φ (ρ g w)) → ∃ v : U, v ≠ 0 ∧ ParVec ρ e a θ v := by
  first | exact @GlobalTheory.LevelType.exists_parVec_of_map | exact GlobalTheory.LevelType.exists_parVec_of_map | (intros; apply GlobalTheory.LevelType.exists_parVec_of_map <;> assumption)
