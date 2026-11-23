import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviNormalisesUnip
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainClosure

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_normalizes_unipotent' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁) (t : (AE F E)ˣ) (m : UA σ Y.J), IsLevi (W₁ := Y₁) H t 1 m → ∀ u ∈ unip σ Y H, m * u * m⁻¹ ∈ unip σ Y H ∧ m⁻¹ * u * m ∈ unip σ Y H := by
  first | exact @GlobalTheory.LeviNormal.levi_normalises_unip | exact GlobalTheory.LeviNormal.levi_normalises_unip | (intros; apply GlobalTheory.LeviNormal.levi_normalises_unip <;> assumption)
