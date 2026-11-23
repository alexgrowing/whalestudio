import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergDerivativeZeroOrEmptyEqZero
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeisenbergDerivativeArchimedeanDirectionStatement
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergDerivative_zero_or_empty_eq_zero : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (g h : SInf F (Fin n × Fin d)) (u : Matrix (Fin n) (Fin d) (AE F E)),
    ActsD (evI F) (M.heisLine ψ u) g h → (g = 0 ∨ IsEmpty (Fin n × Fin d)) → h = 0 := by
  first | exact @GlobalTheory.HeisDerivZero.actsD_eq_zero | exact GlobalTheory.HeisDerivZero.actsD_eq_zero | (intros; apply GlobalTheory.HeisDerivZero.actsD_eq_zero <;> assumption)
