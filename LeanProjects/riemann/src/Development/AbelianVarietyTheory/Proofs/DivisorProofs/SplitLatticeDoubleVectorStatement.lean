import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitLatticeDoubleVector
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_lattice_double_vector : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {d : ℕ} (V : Spc F E d) (v : Pl F) (e : AF F) (θ : AE F E),
    At (evFin F v) e → evFin F v e = 1 → e * e = e → θ * θ = θ → θ * cA σ θ = 0 →
    θ + cA σ θ = algebraMap (AF F) (AE F E) e →
    (∀ z ∈ GlobalTheory.InertSph.latAt V v, θ • z ∈ GlobalTheory.InertSph.latAt V v ∧ cA σ θ • z ∈ GlobalTheory.InertSph.latAt V v) →
    ∃ w₀ ∈ GlobalTheory.DblVac.KD σ V v, ∀ k ∈ GlobalTheory.InertSph.KAt σ V v, ∀ gd : GlobalTheory.DblVac.UD σ V,
      ((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) = Matrix.fromBlocks (mat k) 0 0 1 →
      gd ∈ GlobalTheory.DblVac.KD σ V v →
      w₀ * gd * w₀⁻¹ ∈ GlobalTheory.DblVac.KD σ V v ∧ w₀ * gd * w₀⁻¹ ∈ GlobalTheory.DblVac.PDiag σ V := by
  first | exact @GlobalTheory.DblVacSplitConj.exists_conj_diag | exact GlobalTheory.DblVacSplitConj.exists_conj_diag | (intros; apply GlobalTheory.DblVacSplitConj.exists_conj_diag <;> assumption)
