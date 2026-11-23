import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfAdjointLevelMatrix
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarProd
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published GlobalTheory.TamUnf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_adjoint_level_matrix : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E),
    (∀ k : finSU (IsCMField.complexConj E).toAlgHom Gᵀ,
      IsSA G ((HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E)) (IsCMField.complexConj E).toAlgHom Gᵀ k.1 :
        GL (Fin r) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E) ⊗[maximalRealSubfield E] E)) :
        Matrix (Fin r) (Fin r) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E) ⊗[maximalRealSubfield E] E))) ∧
    ∀ g : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E), IsSA G g →
      ∃ k : finSU (IsCMField.complexConj E).toAlgHom Gᵀ,
        ((HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E)) (IsCMField.complexConj E).toAlgHom Gᵀ k.1 :
          GL (Fin r) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E) ⊗[maximalRealSubfield E] E)) :
          Matrix (Fin r) (Fin r) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E) ⊗[maximalRealSubfield E] E)) = g := by
  first | exact @GlobalTheory.TamUnf.finSU_mat_iff_isSA | exact GlobalTheory.TamUnf.finSU_mat_iff_isSA | (intros; apply GlobalTheory.TamUnf.finSU_mat_iff_isSA <;> assumption)
