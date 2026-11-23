import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsMoreBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWittFrameInitCols
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
noncomputable section

namespace GlobalTheory.WittExt

open Matrix
open Formalism.UG (cT)

theorem exists_isWittFrame_initCols : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (C : Matrix (Fin n) (Fin (r + 1)) E),
      LinearIndependent E C.transpose → Formalism.UG.cT (σ : E →+* E) C * J * C = 0 →
        ∃ (m : ℕ) (hm : r < m) (X Y : Matrix (Fin n) (Fin m) E), IsWittFrame σ J X Y ∧ GlobalTheory.StdPar.initCols X ⟨r, hm⟩ = C := by
  first
  | exact @_root_.GlobalTheory.AdjugateAppendColumn.exists_wittFrame_initCols
  | exact _root_.GlobalTheory.AdjugateAppendColumn.exists_wittFrame_initCols
  | (apply _root_.GlobalTheory.AdjugateAppendColumn.exists_wittFrame_initCols <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdjugateAppendColumn.exists_wittFrame_initCols <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdjugateAppendColumn.exists_wittFrame_initCols <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdjugateAppendColumn.exists_wittFrame_initCols ..)

end GlobalTheory.WittExt
