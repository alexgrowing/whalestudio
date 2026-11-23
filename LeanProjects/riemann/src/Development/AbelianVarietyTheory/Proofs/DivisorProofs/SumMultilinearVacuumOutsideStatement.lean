import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumMultilinearVacuumOutside
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_multilinear_vacuum_outside : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y W) (ψ : AddChar (AF F) ℂ), M.IsGood ψ → ∀ (T : Finset (Pl F)) (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ), (∀ j, ∀ v ∉ T, φ j v = M.vac v) → ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f j) (φ j) = 0 → ∀ (P₀ : Type) [AddCommGroup P₀] [Module ℂ P₀] (P : Pl F → Type) [∀ v, AddCommGroup (P v)] [∀ v, Module ℂ (P v)] (q₀ : SInf F (Fin n × Fin d) →ₗ[ℂ] P₀) (q : ∀ v, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] P v), ∑ j, q₀ (f j) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (fun v : T => q v (φ j v)) = 0 := by
  first | exact @GlobalTheory.PureTensor.pure_sum_tensor_eq_zero | exact GlobalTheory.PureTensor.pure_sum_tensor_eq_zero | (intros; apply GlobalTheory.PureTensor.pure_sum_tensor_eq_zero <;> assumption)
