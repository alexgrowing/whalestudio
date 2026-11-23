import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FieldIsoMatrixCongruenceAutomorphismCongruence
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TwU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fieldIso_matrixCongruence_automorphismCongruence : ∀ {D : D7} {X : Fields} (s : Seam D X) {N : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (n : ℕ) (g : Sp X.E N ≃ₗ[X.E] Sp X.E N), (∀ a b, IntAt (seamP s P) ((((qOf (seamP s P) : ℕ) : D.host.E) ^ n)⁻¹ * (((seamGL s g : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) - 1) a b)) → ∀ s' l, IntAt P (((qOf P : X.E) ^ n)⁻¹ * (g (Pi.single s' (1 : X.E)) l - (Pi.single s' (1 : X.E) : Sp X.E N) l)) := by
  first | exact @GlobalTheory.SeamCong.cong_seam | exact GlobalTheory.SeamCong.cong_seam | (intros; apply GlobalTheory.SeamCong.cong_seam <;> assumption)
