import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAbsMatrixProductLeHeights
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulIntSingle
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_abs_matrix_product_le_heights : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} (g : GL (Fin n) (AF F ⊗[F] E)) (X : Matrix (Fin n) (Fin d) (AF F ⊗[F] E)) (h : GL (Fin d) (AF F ⊗[F] E)) (v : HeightOneSpectrum (𝓞 F)) (i : Fin n) (j : Fin d), absFin F v (compFin F E v (((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * X * (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E))ᵀ) i j)) ≤ htFin F v (bc (compFin F E v) g) * (Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (X p.1 p.2))) * htFin F v (bc (compFin F E v) h) := by
  first | exact @GlobalTheory.absFin_mul_mul_transpose_le | exact GlobalTheory.absFin_mul_mul_transpose_le | (intros; apply GlobalTheory.absFin_mul_mul_transpose_le <;> assumption)
