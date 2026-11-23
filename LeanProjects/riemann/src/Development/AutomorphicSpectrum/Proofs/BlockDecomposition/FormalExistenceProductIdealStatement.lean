import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalExistenceProductIdeal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_existence_product_ideal : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))] [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] (J J₁ J₂ : X.IdealSheafData), (∀ (U : X.affineOpens) (a b : Γ(X, U)), a ∈ J₁.ideal U → b ∈ J₂.ideal U → a * b ∈ J.ideal U) → Statement I J₁ → Statement I J₂ → Statement I J := by
  first | exact @GlobalTheory.CompanionTheory.GE.NonPrime.statement_of_mul_mem | exact GlobalTheory.CompanionTheory.GE.NonPrime.statement_of_mul_mem | (intros; apply GlobalTheory.CompanionTheory.GE.NonPrime.statement_of_mul_mem <;> assumption)
