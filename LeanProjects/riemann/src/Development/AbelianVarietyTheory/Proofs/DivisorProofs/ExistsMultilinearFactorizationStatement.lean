import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMultilinearFactorization
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multilinear_factorization : open Classical in ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y W) (ψ : AddChar (AF F) ℂ), M.IsGood ψ → ∀ T : Finset (Pl F), ∃ Ψ : SInf F (Fin n × Fin d) →ₗ[ℂ] MultilinearMap ℂ (fun v : T => (Fin n × Fin d → Fv F v) → ℂ) ((Fin n × Fin d → AF F) → ℂ), ∀ f φ, Ψ f φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (fun v => if h : v ∈ T then φ ⟨v, h⟩ else M.vac v) := by
  first | exact @GlobalTheory.PureML.pure_multilinear | exact GlobalTheory.PureML.pure_multilinear | (intros; apply GlobalTheory.PureML.pure_multilinear <;> assumption)
