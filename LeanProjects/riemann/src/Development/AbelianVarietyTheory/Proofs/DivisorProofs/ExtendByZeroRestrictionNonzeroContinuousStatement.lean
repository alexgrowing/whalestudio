import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroRestrictionNonzeroContinuous
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtendByZeroAdd
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.AdaptEv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extend_by_zero_restriction_nonzero_continuous : ∀ (F : Type) [Field F] [NumberField F] {κ ι κ₁ : Type} [Fintype κ] [Fintype ι] [Fintype κ₁] (eq : κ ≃ ι ⊕ κ₁),
    ∃ ei : SInf F κ →L[ℂ] SInf F κ₁, ei ≠ 0 ∧ ∀ f y, ei f y = f (ext0 eq y) := by
  first | exact @GlobalTheory.ThK.AdaptEv.exists_restr_schwartz | exact GlobalTheory.ThK.AdaptEv.exists_restr_schwartz | (intros; apply GlobalTheory.ThK.AdaptEv.exists_restr_schwartz <;> assumption)
