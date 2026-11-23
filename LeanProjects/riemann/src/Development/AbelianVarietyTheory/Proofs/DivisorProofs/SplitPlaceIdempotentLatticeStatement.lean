import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceIdempotentLattice
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_place_idempotent_lattice : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v →
    ∃ (e : AF F) (θ : AE F E), At (evFin F v) e ∧ evFin F v e = 1 ∧ e * e = e ∧ θ * θ = θ ∧ θ * cA σ θ = 0 ∧
      θ + cA σ θ = algebraMap (AF F) (AE F E) e ∧
      ∀ {d : ℕ} (W : Spc F E d), ∀ z ∈ GlobalTheory.InertSph.latAt W v, θ • z ∈ GlobalTheory.InertSph.latAt W v ∧ cA σ θ • z ∈ GlobalTheory.InertSph.latAt W v := by
  first | exact @GlobalTheory.SplitPlaceIdem.exists_split_idem | exact GlobalTheory.SplitPlaceIdem.exists_split_idem | (intros; apply GlobalTheory.SplitPlaceIdem.exists_split_idem <;> assumption)
