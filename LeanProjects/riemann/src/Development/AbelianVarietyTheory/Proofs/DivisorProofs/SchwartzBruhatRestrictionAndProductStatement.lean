import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatRestrictionAndProduct
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtendByZeroAdd
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.AdaptEv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bruhat_restriction_and_product : ∀ {R : Type} [TopologicalSpace R] [Zero R] [T1Space R] {κ ι κ₁ : Type} [Fintype κ] [Fintype ι] [Fintype κ₁] (eq : κ ≃ ι ⊕ κ₁),
    (∀ g ∈ SB (κ → R), restrL eq g ∈ SB (κ₁ → R)) ∧ ∀ A ∈ SB (ι → R), ∀ φ ∈ SB (κ₁ → R), prodVac eq A φ ∈ SB (κ → R) := by
  first | exact @GlobalTheory.ThK.AdaptEv.sb_restrL_prodVac | exact GlobalTheory.ThK.AdaptEv.sb_restrL_prodVac | (intros; apply GlobalTheory.ThK.AdaptEv.sb_restrL_prodVac <;> assumption)
