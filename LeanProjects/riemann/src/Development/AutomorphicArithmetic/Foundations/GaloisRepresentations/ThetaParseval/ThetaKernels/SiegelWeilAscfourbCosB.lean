import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ParabolicBlockForms.BlockHForm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PadMatrixLowerBlockZero

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
set_option linter.unusedSimpArgs false
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
namespace Bq
theorem blockH_form_k {ε : ℤˣ} {M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E}
    (hM : Mᵀ * QE d.n ε * M.map σ = QE d.n ε)
    (hx : ∀ r, M r (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) r (Sum.inl L.i₀))
    (hy : ∀ c, c ≠ Sum.inr L.i₀ → M (Sum.inr L.i₀) c = 0) :
    (M.submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L))ᵀ * QE L.n ε * (M.submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L)).map σ = QE L.n ε := by
  have hQx : ∀ r, r ≠ Sum.inr L.i₀ → QE (E := E) d.n ε r (Sum.inl L.i₀) = 0 := by
    intro r hr
    rcases r with i | i
    · simp [QE]
    · have hi : i ≠ L.i₀ := fun h => hr (by rw [h])
      simp [QE, Matrix.one_apply, hi]
  have hQx' : ∀ a', QE (E := E) d.n ε (Sum.inl L.i₀) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a') = 0 := by
    intro a'
    rcases a' with k | k
    · simp [QE, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k]
    · simp [QE, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, Matrix.one_apply, Ne.symm (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L k)]
  have hne : ∀ a', _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a' ≠ Sum.inr L.i₀ := by
    intro a'
    rcases a' with k | k
    · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k]
    · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L k]
  have hQQ : ∀ a' c', QE (E := E) d.n ε (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a') (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L c') = QE L.n ε a' c' := by
    intro a' c'
    rcases a' with k | k <;> rcases c' with k' | k' <;> simp [QE, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, Matrix.one_apply, L.inj.eq_iff]
  refine Matrix.ext fun a c => ?_
  have h := congrFun (congrFun hM (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a)) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L c)
  rw [← hQQ, ← h]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply, Finset.sum_mul]
  symm
  rw [Bq.sum_emb (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L)]
  · refine Finset.sum_congr rfl fun c' _ => ?_
    rw [Bq.sum_emb (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L)]
    · exact Finset.sum_congr rfl fun a' _ => by rw [hQQ]
    · intro r hr
      have hm := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.mem_out_k L hr
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
      rcases hm with rfl | rfl
      · rw [hQx', mul_zero, zero_mul]
      · rw [hy _ (hne a), zero_mul, zero_mul]
  · intro s hs
    have hm := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.mem_out_k L hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with rfl | rfl
    · refine Finset.sum_eq_zero fun r _ => ?_
      by_cases hr : r = Sum.inr L.i₀
      · subst hr
        rw [hy _ (hne a), zero_mul, zero_mul]
      · rw [hQx r hr, mul_zero, zero_mul]
    · refine Finset.sum_eq_zero fun r _ => ?_
      rw [hy _ (hne c), map_zero, mul_zero]
end Bq
end PositivityTheory.SiegelWeilFormula.Act.C4
end
end
