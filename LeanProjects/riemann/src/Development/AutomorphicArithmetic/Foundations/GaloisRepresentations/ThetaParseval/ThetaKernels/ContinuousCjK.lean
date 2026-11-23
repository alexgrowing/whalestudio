import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ContinuousCj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.CAInjectiveK

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C1
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d} {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)}
  {𝓤 : Set (Fin L.n → AE F E)} {nb : nA σ d.Y d.b → d.G}
def Ap_k (hU : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) := (hU.1 u).choose
theorem inFrame_uM_k (hU : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) :
    inFrame d.b (uM u) = Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u) 0 0 (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u) := (hU.1 u).choose_spec
theorem uM_add_k (hU : L.UData uM ν 𝓤) (u v : Fin L.n → AE F E) : uM (u + v) = uM u * uM v := by
  refine _root_.PositivityTheory.SiegelWeilFormula.Act.C1.blk_unique_k d (A₂ := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU v) (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU (u + v)) ?_
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_mul_k]
theorem uM_zero_k (hU : L.UData uM ν 𝓤) : uM 0 = 1 := by
  refine _root_.PositivityTheory.SiegelWeilFormula.Act.C1.blk_unique_k d (A₂ := 1) (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU 0) ?_
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_one, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_zero_k, Matrix.fromBlocks_one]
theorem uM_neg_k (hU : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) : uM (-u) = (uM u)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← _root_.PositivityTheory.SiegelWeilFormula.Act.C1.uM_add_k hU, neg_add_cancel, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.uM_zero_k hU])
theorem Ap_neg_mul_k (hU : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU (-u) * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u = 1 := by
  have h := congrArg (inFrame d.b) (show uM (-u) * uM u = 1 by rw [← _root_.PositivityTheory.SiegelWeilFormula.Act.C1.uM_add_k hU, neg_add_cancel, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.uM_zero_k hU])
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU, Matrix.fromBlocks_multiply,
    GlobalTheory.EisBL.DoubledParabolic.inFrame_one, ← Matrix.fromBlocks_one] at h
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at h
  exact (Matrix.fromBlocks_inj.1 h).2.2.2
theorem frame_conj_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    inFrame d.b ((uM u)⁻¹ * nb β * uM u) = Matrix.fromBlocks 1 (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u) * β.1 * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u) 0 1 := by
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, ← _root_.PositivityTheory.SiegelWeilFormula.Act.C1.uM_neg_k hU, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU, hN β,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_mul_k, neg_add_cancel, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_zero_k,
    _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_neg_mul_k hU]
theorem cj_mem_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u) * β.1 * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u ∈ nA σ d.Y d.b :=
  AddSubgroup.subset_closure ⟨_, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.frame_conj_k hU hN u β⟩
def cj_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) : nA σ d.Y d.b →+ nA σ d.Y d.b where
  toFun β := ⟨_, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_mem_k hU hN u β⟩
  map_zero' := Subtype.ext (by simp)
  map_add' β β' := Subtype.ext (by simp [Matrix.mul_add, Matrix.add_mul])
theorem cj_val_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN u β).1 = _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u) * β.1 * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u := rfl
theorem nb_cj_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    nb (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN u β) = (uM u)⁻¹ * nb β * uM u := by
  apply kunf.inFrame_injective d.b
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.frame_conj_k hU hN, hN]
  rfl
theorem cj_inv_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN (-u) (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN u β) = β := by
  apply Subtype.ext
  have h1 : _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u) = 1 := by rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_mul_k, add_neg_cancel, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_zero_k]
  have h2 : _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU (-u) = 1 := by simpa using _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_neg_mul_k hU (-u)
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_val_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_val_k, neg_neg]
  calc _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u * (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u) * β.1 * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u) * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU (-u)
      = (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u)) * β.1 * (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU (-u)) := by simp only [Matrix.mul_assoc]
    _ = β.1 := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
theorem continuous_cj_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) :
    Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN u) :=
  ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const).subtype_mk _
def cjE_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) : nA σ d.Y d.b ≃ₜ+ nA σ d.Y d.b where
  toFun := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN u
  invFun := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN (-u)
  left_inv β := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_inv_k hU hN u β
  right_inv β := by simpa using _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_inv_k hU hN (-u) β
  map_add' := map_add _
  continuous_toFun := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.continuous_cj_k hU hN u
  continuous_invFun := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.continuous_cj_k hU hN (-u)
end PositivityTheory.SiegelWeilFormula.Act.C1
end
end
