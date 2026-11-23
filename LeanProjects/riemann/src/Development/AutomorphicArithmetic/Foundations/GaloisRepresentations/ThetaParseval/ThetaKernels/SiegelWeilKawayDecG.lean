import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.IsUnitDetInFrame
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.KAway
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem inFrame_mul_k (x y : d.G) : inFrame d.b (x * y) = inFrame d.b x * inFrame d.b y :=
  GlobalTheory.EisBL.DoubledParabolic.inFrame_mul d.b x y
theorem inFrame_one_k : inFrame d.b (1 : d.G) = 1 :=
  GlobalTheory.EisBL.DoubledParabolic.inFrame_one d.b
theorem inFrame_inj_k {x y : d.G} (h : inFrame d.b x = inFrame d.b y) : x = y :=
  PositivityTheory.SiegelWeilFormula.kunf.inFrame_injective d.b h
theorem isUnit_det_inFrame_k (x : d.G) : IsUnit (inFrame d.b x).det :=
  Matrix.isUnit_det_of_left_inverse (GlobalTheory.EisBL.DoubledParabolic.inFrame_inv_mul d.b x)
variable {d} {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
include hε
theorem inU_inFrame_k (x : d.G) : (inFrame d.b x)ᵀ * jF d.n ε * (inFrame d.b x).map (cA σ) = jF d.n ε :=
  PositivityTheory.SiegelWeilFormula.kunf.frame_eq hε x
theorem exists_of_inU_k (M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))
    (hM : Mᵀ * jF d.n ε * M.map (cA σ) = jF d.n ε) : ∃ x : d.G, inFrame d.b x = M := by
  set J : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) := jF d.n ε with hJ
  have hεε : ((ε : ℤ) : AE F E) * ((ε : ℤ) : AE F E) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hJJ : J * (((ε : ℤ) : AE F E) • J) = 1 := by
    rw [Matrix.mul_smul, hJ, jF, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]
    congr 1 <;> simp [smul_smul, hεε]
  have hT : Mᵀ * (J * M.map (cA σ) * (((ε : ℤ) : AE F E) • J)) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hM, hJJ]
  have hu : IsUnit Mᵀ.det := Matrix.isUnit_det_of_right_inverse hT
  rw [Matrix.det_transpose] at hu
  exact PositivityTheory.SiegelWeilFormula.kunf.exists_of_frame hε M M⁻¹ (Matrix.mul_nonsing_inv M hu) hM
end
end PositivityTheory.SiegelWeilFormula.KAway
end
end
