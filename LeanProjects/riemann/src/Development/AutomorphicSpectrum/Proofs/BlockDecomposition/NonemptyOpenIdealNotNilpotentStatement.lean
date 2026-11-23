import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonemptyOpenIdealNotNilpotent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowIdeal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_open_ideal_not_nilpotent : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) (W : J.subscheme.Opens), (W : Set J.subscheme).Nonempty → ∃ J₀ : X.IdealSheafData, (∀ (V : X.affineOpens) (f : Γ(X, V)), f ∈ J₀.ideal V → J.subschemeι ⁻¹ᵁ X.basicOpen f ≤ W) ∧ ∀ m, ¬ powIdeal J₀ m ≤ J := by
  first | exact @GlobalTheory.CompanionTheory.GE.NonIso.exists_ideal_not_pow_le | exact GlobalTheory.CompanionTheory.GE.NonIso.exists_ideal_not_pow_le | (intros; apply GlobalTheory.CompanionTheory.GE.NonIso.exists_ideal_not_pow_le <;> assumption)
