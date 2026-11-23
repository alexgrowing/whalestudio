import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntegralGLAtPrimeOfCongruentOneModPow
import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_integralGLAtPrime_of_congruent_one_mod_pow : ∀ {E : Type} [Field E] [NumberField E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (d : ℕ) (g : Formalism.L2.Col.Sp E n ≃ₗ[E] Formalism.L2.Col.Sp E n),
  (∀ a b, Formalism.L2.Col.IntAt P (((Formalism.L2.Col.qOf P : E) ^ d)⁻¹ * (LinearMap.toMatrix' g.toLinearMap a b - (1 : Matrix (Fin n) (Fin n) E) a b))) →
  (∀ a b, Formalism.L2.Col.IntAt P (((Formalism.L2.Col.qOf P : E) ^ d)⁻¹ * (LinearMap.toMatrix' g.symm.toLinearMap a b - (1 : Matrix (Fin n) (Fin n) E) a b))) →
  g ∈ Formalism.L2.Col.GLint E n P ∧ ∀ w ∈ Formalism.L2.Col.stdAt E n P, ((Formalism.L2.Col.qOf P : E) ^ d)⁻¹ • (g w - w) ∈ Formalism.L2.Col.stdAt E n P := by
  first | exact @GlobalTheory.Proof.mem_integralGLAtPrime_of_congruent_one_mod_pow.glint_of_cong | exact GlobalTheory.Proof.mem_integralGLAtPrime_of_congruent_one_mod_pow.glint_of_cong | (intros; apply GlobalTheory.Proof.mem_integralGLAtPrime_of_congruent_one_mod_pow.glint_of_cong <;> assumption)
