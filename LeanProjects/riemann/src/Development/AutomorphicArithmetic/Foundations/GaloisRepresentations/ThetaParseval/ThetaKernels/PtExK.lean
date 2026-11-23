import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PtEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Act.CL
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem ptEx'_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    {X : Type} [TopologicalSpace X] (M M' : X → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))
    (hM : Continuous M) (hM' : Continuous M') (h : ∀ c, M c * M' c = 1)
    (hu : ∀ c, (M c)ᵀ * kunf.jw d.n (((ε : ℤ) : AE F E)) * (M c).map (cA σ) = kunf.jw d.n (((ε : ℤ) : AE F E))) :
    ∃ f : X → d.G, Continuous f ∧ ∀ c, inFrame d.b (f c) = M c := by
  set B0 := incM F d.b.1 with hB0
  set Bi := incM F (d.b⁻¹).1 with hBi
  have e1 : B0 * Bi = 1 := GlobalTheory.EisBL.DoubledParabolic.incM_mul_inv d.b
  have e2 : Bi * B0 = 1 := GlobalTheory.EisBL.DoubledParabolic.incM_inv_mul d.b
  have h' : ∀ c, M' c * M c = 1 := fun c => mul_eq_one_comm.1 (h c)
  let U : X → GL (Fin d.n ⊕ Fin d.n) (AE F E) := fun c => ⟨B0 * M c * Bi, B0 * M' c * Bi, by
      calc B0 * M c * Bi * (B0 * M' c * Bi) = B0 * (M c * (Bi * B0) * M' c) * Bi := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [e2, Matrix.mul_one, h, Matrix.mul_one, e1], by
      calc B0 * M' c * Bi * (B0 * M c * Bi) = B0 * (M' c * (Bi * B0) * M c) * Bi := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [e2, Matrix.mul_one, h', Matrix.mul_one, e1]⟩
  have hU : ∀ c, U c ∈ UG (cA σ) (dbl (incM F d.Y.J)) := by
    intro c
    obtain ⟨x, hx⟩ := kunf.exists_of_frame (Y := d.Y) hε (M c) (M' c) (h c) (hu c)
    have hx1 : x.1 = U c := by
      apply Units.ext
      show mat2 x = B0 * M c * Bi
      rw [← hx]
      show mat2 x = B0 * (Bi * mat2 x * B0) * Bi
      calc mat2 x = (B0 * Bi) * mat2 x * (B0 * Bi) := by rw [e1, Matrix.one_mul, Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]
    exact hx1 ▸ x.2
  refine ⟨fun c => ⟨U c, hU c⟩, ?_, fun c => ?_⟩
  · refine continuous_induced_rng.2 ?_
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact (continuous_const.matrix_mul hM).matrix_mul continuous_const
    · exact (continuous_const.matrix_mul hM').matrix_mul continuous_const
  · show Bi * (B0 * M c * Bi) * B0 = M c
    calc Bi * (B0 * M c * Bi) * B0 = (Bi * B0) * M c * (Bi * B0) := by simp only [Matrix.mul_assoc]
      _ = M c := by rw [e2, Matrix.one_mul, Matrix.mul_one]
end PositivityTheory.SiegelWeilFormula.Act.CL
end
end
