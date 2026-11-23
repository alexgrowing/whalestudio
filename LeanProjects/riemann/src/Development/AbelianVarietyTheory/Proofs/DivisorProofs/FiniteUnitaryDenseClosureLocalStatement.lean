import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnitaryDenseClosureLocal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainMulRight
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThetaCplV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_unitary_dense_closure_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (W : Spc F E d), IsCMExt F E σ → ∀ h ∈ finU σ W.J, ∀ U : Subgroup (UA σ W.J), IsOpen (U : Set (UA σ W.J)) → ∃ h' ∈ Subgroup.closure (⋃ v : Pl F, UAt σ W (evFin F v)), h'⁻¹ * h ∈ U ∧ h'⁻¹ * h ∈ finU σ W.J := by
  first | exact @GlobalTheory.FinPlaceDense.exists_closure_mod_open | exact GlobalTheory.FinPlaceDense.exists_closure_mod_open | (intros; apply GlobalTheory.FinPlaceDense.exists_closure_mod_open <;> assumption)
