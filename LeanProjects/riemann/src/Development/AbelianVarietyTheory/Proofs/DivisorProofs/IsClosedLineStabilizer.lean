import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLineStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinSeriesMeasurable
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open GlobalTheory.IwasawaKAvgInt

namespace GlobalTheory.IwasawaKAvgInt

theorem isClosed_lineStab_arch : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (X : Spc F E n) (x : Fin n → E), x ≠ 0 →
    IsClosed (lineStab σ X x : Set (UAtSub σ X (evI F))) := by
  intro F E _ _ _ _ _ σ n X x hx
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
  exact (GlobalTheory.ConeSmallMeas.isClosed_lineStab (σ := σ) (J := X.J) x hi).preimage continuous_subtype_val

end GlobalTheory.IwasawaKAvgInt
