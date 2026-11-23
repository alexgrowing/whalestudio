import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedSectionsUniformGenerators
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_sections_uniform_generators : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsNoetherian X] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ S : ℕ → Subobject P, ClosedSys I P S → ∀ (n₁ : ℤ) (W : ∀ n : ℤ, Set Γ(GlobalTheory.twistZ P H n, ⊤)), (∀ n e, W n ⊆ twSecs H n (S e)) → (∀ n, n₁ ≤ n → ∀ e, ∀ x ∈ twSecs H n (S e), ∃ b ∈ W n, x - b ∈ twPow I H n P (e + 1)) → ∃ B : Subobject P, (B : X.Modules).IsQuasicoherent ∧ ∀ e, B ⊔ powSub I P (e + 1) = S e := by
  first | exact @GlobalTheory.CompanionTheory.GE.TwGen.exists_alg_of_twSecs | exact GlobalTheory.CompanionTheory.GE.TwGen.exists_alg_of_twSecs | (intros; apply GlobalTheory.CompanionTheory.GE.TwGen.exists_alg_of_twSecs <;> assumption)
