import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.HomExtensionByZeroOrthDecompRational
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.UnipotentNilpotentMulEqZero
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.BlockDiagonalPreservesFormIff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.BMatK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisensteinSecondTerm

set_option synthInstance.maxHeartbeats 200000

section
set_option linter.unusedSectionVars false
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C5.JC
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
abbrev Mt_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Type := Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)
def extendByZeroColumns (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (x : Fin L.n → AE F E) (i : Fin d.n) : AE F E :=
  ∑ k, (if L.em k = i then (1 : AE F E) else 0) * x k
theorem extendZeroColumn_apply_embed (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (x : Fin L.n → AE F E) (k : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.extendByZeroColumns L x (L.em k) = x k := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.extendByZeroColumns, L.inj.eq_iff]
theorem extension_by_zero_at_base_index (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (x : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.extendByZeroColumns L x L.i₀ = 0 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.extendByZeroColumns, _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k]
def vV_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (u b : Fin L.n → AE F E) : Fin d.n ⊕ Fin d.n → AE F E := Sum.elim (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.extendByZeroColumns L u) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.extendByZeroColumns L b)
def IsPad_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (M : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.Mt_k d) : Prop :=
  ∀ u ∈ ({Sum.inl L.i₀, Sum.inr L.i₀} : Set (Fin d.n ⊕ Fin d.n)), ∀ v, M u v = (1 : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.Mt_k d) u v ∧ M v u = (1 : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.Mt_k d) v u
theorem isPad_j_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (g : G2 σ L.Y) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.IsPad_k L (inFrame d.b (L.j g)) := L.j_out g
variable {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
theorem pad_col_k {M : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.Mt_k d} (hM : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.IsPad_k L M) : M *ᵥ Pi.single (Sum.inl L.i₀) 1 = Pi.single (Sum.inl L.i₀) 1 := by
  funext r
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [(hM _ (by simp) r).2]
  simp [Matrix.one_apply]
theorem pad_row_k {M : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.Mt_k d} (hM : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.IsPad_k L M) : Pi.single (Sum.inr L.i₀) 1 ᵥ* M = Pi.single (Sum.inr L.i₀) 1 := by
  funext r
  simp only [Matrix.vecMul, dotProduct, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [(hM _ (by simp) r).1]
  simp [Matrix.one_apply, eq_comm]
theorem pad_vecMul_inl_k {M : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.Mt_k d} (hM : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.IsPad_k L M) (x : Fin d.n ⊕ Fin d.n → AE F E) :
    (x ᵥ* M) (Sum.inl L.i₀) = x (Sum.inl L.i₀) := by
  simp only [Matrix.vecMul, dotProduct]
  rw [Finset.sum_congr rfl fun r _ => by rw [(hM _ (by simp) r).2]]
  simp [Matrix.one_apply]
theorem pad_vecMul_inr_k {M : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.Mt_k d} (hM : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.IsPad_k L M) (x : Fin d.n ⊕ Fin d.n → AE F E) :
    (x ᵥ* M) (Sum.inr L.i₀) = x (Sum.inr L.i₀) := by
  simp only [Matrix.vecMul, dotProduct]
  rw [Finset.sum_congr rfl fun r _ => by rw [(hM _ (by simp) r).2]]
  simp [Matrix.one_apply]
theorem pad_single_vecMul_k {M : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.Mt_k d} (hM : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.IsPad_k L M) (a : AE F E) :
    Pi.single (Sum.inr L.i₀) a ᵥ* M = Pi.single (Sum.inr L.i₀) a := by
  rw [Matrix.single_vecMul]
  funext r
  simp only [Pi.smul_apply, Matrix.row_apply, smul_eq_mul]
  rw [(hM _ (by simp) r).1]
  by_cases h : r = Sum.inr L.i₀
  · subst h; simp [Matrix.one_apply]
  · simp [Matrix.one_apply, h, Pi.single_apply, Ne.symm h]
def hN_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (vf wf : Fin d.n ⊕ Fin d.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.Mt_k d :=
  1 + Matrix.vecMulVec (Pi.single (Sum.inl L.i₀) 1) vf + Matrix.vecMulVec wf (Pi.single (Sum.inr L.i₀) 1)
theorem conj_hN_k {J K : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.Mt_k d} (hKJ : K * J = 1) (hJ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.IsPad_k L J) (vf wf : Fin d.n ⊕ Fin d.n → AE F E) :
    J * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.hN_k L vf wf = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.hN_k L (vf ᵥ* K) (J *ᵥ wf) * J := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.hN_k, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.pad_col_k hJ, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.pad_row_k hJ, Matrix.vecMul_vecMul, hKJ, Matrix.vecMul_one]
def W_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.Mt_k d := kunf.jw d.n (((R.ε : ℤ) : AE F E))
theorem e_mul_e_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : (((R.ε : ℤ) : AE F E)) * ((R.ε : ℤ) : AE F E) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
theorem W_transpose_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R)ᵀ = (((R.ε : ℤ) : AE F E)) • _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R := by
  have he := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.e_mul_e_k R
  ext (i | i) (j | j) <;> simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k, kunf.jw, Matrix.one_apply] <;> split_ifs <;> simp_all [eq_comm]
theorem W_mul_W_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R = (((R.ε : ℤ) : AE F E)) • (1 : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.Mt_k d) := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k, kunf.jw, Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one,
    zero_add, add_zero]
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero]
theorem W_mulVec_inl_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (y : Fin d.n ⊕ Fin d.n → AE F E) (i : Fin d.n) :
    (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R *ᵥ y) (Sum.inl i) = y (Sum.inr i) := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k, kunf.jw, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]
theorem W_mulVec_inr_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (y : Fin d.n ⊕ Fin d.n → AE F E) (i : Fin d.n) :
    (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R *ᵥ y) (Sum.inr i) = ((R.ε : ℤ) : AE F E) * y (Sum.inl i) := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k, kunf.jw, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]
theorem JW_k {R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d} {J K : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.Mt_k d} (hKJ : K * J = 1) (hK : Kᵀ * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R * K.map (cA σ) = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R) :
    J * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R * (K.map (cA σ))ᵀ := by
  have he : ((R.ε : ℤ) : AE F E) * ((R.ε : ℤ) : AE F E) = 1 := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.e_mul_e_k R
  have hJt : Jᵀ * Kᵀ = 1 := by rw [← Matrix.transpose_mul, hKJ, Matrix.transpose_one]
  have h1 : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R * K.map (cA σ) = Jᵀ * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R := by
    calc _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R * K.map (cA σ) = (Jᵀ * Kᵀ) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R * K.map (cA σ) := by rw [hJt, Matrix.one_mul]
      _ = Jᵀ * (Kᵀ * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R * K.map (cA σ)) := by simp only [Matrix.mul_assoc]
      _ = Jᵀ * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R := by rw [hK]
  have h2 : (K.map (cA σ))ᵀ * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R * J := by
    have h3 := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_transpose_k, Matrix.mul_smul,
      Matrix.smul_mul] at h3
    have h4 := congrArg (fun M : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.Mt_k d => ((R.ε : ℤ) : AE F E) • M) h3
    simpa only [smul_smul, he, one_smul] using h4
  have hWW := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_mul_W_k R
  calc J * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R = ((R.ε : ℤ) : AE F E) • (((R.ε : ℤ) : AE F E) • (J * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R)) := by rw [smul_smul, he, one_smul]
    _ = ((R.ε : ℤ) : AE F E) • ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R) * J * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R) := by rw [hWW, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul]
    _ = ((R.ε : ℤ) : AE F E) • (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R * ((K.map (cA σ))ᵀ * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R) := by rw [h2]; simp only [Matrix.mul_assoc]
    _ = ((R.ε : ℤ) : AE F E) • (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R * (K.map (cA σ))ᵀ * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R)) := by simp only [Matrix.mul_assoc]
    _ = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R * (K.map (cA σ))ᵀ := by rw [hWW, Matrix.mul_smul, Matrix.mul_one, smul_smul, he, one_smul]
theorem cv_vecMul_k (x : Fin d.n ⊕ Fin d.n → AE F E) (K : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.Mt_k d) : cv σ (x ᵥ* K) = (K.map (cA σ))ᵀ *ᵥ cv σ x := by
  funext s
  simp [cv, Matrix.vecMul, Matrix.mulVec, dotProduct, map_sum, map_mul, mul_comm]
def qf_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (x : Fin d.n ⊕ Fin d.n → AE F E) : AE F E := x ⬝ᵥ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R *ᵥ cv σ x)
theorem qf_vecMul_k {R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d} {K : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.Mt_k d} (hKW : K * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R * (K.map (cA σ))ᵀ = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R) (x : Fin d.n ⊕ Fin d.n → AE F E) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.qf_k R (x ᵥ* K) = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.qf_k R x := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.qf_k
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cv_vecMul_k, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hKW]
def hh_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (u b : Fin L.n → AE F E) : AE F E := ∑ j, b j * cA σ (u j)
def wf_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (u b : Fin L.n → AE F E) : Fin d.n ⊕ Fin d.n → AE F E :=
  -(((R.ε : ℤ) : AE F E)) • (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R *ᵥ cv σ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_k L u b))
theorem jeA_eq_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eA_k R = ((R.ε : ℤ) : AE F E) := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.eA_k]
theorem uA_apply_k (u : Fin L.n → AE F E) (i k : Fin d.n) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u i k = (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) i k + if i = L.i₀ then _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.extendByZeroColumns L u k else 0 := by
  by_cases hi : i = L.i₀
  · subst hi
    simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.extendByZeroColumns, Matrix.sum_apply, Matrix.single_apply]
  · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, Matrix.sum_apply, Matrix.single_apply, Ne.symm hi, hi]
theorem D_apply_k (u : Fin L.n → AE F E) (l k : Fin d.n) :
    ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-u))ᵀ.map (cA σ)) l k = (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) l k +
      if k = L.i₀ then -cA σ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.extendByZeroColumns L u l) else 0 := by
  rw [Matrix.map_apply, Matrix.transpose_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.uA_apply_k]
  by_cases hk : k = L.i₀
  · subst hk
    simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.extendByZeroColumns, Matrix.one_apply, eq_comm, map_sum, Finset.sum_neg_distrib]
  · simp [Matrix.one_apply, hk, eq_comm]
theorem sB_apply_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (b : Fin L.n → AE F E) (i l : Fin d.n) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L b i l = (if i = L.i₀ then _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.extendByZeroColumns L b l else 0) +
      if l = L.i₀ then -(((R.ε : ℤ) : AE F E) * cA σ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.extendByZeroColumns L b i)) else 0 := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k
  simp only [Matrix.sum_apply, Matrix.add_apply, Matrix.single_apply, Finset.sum_add_distrib, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.jeA_eq_k]
  rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C5.idx_k L i with rfl | ⟨p, rfl⟩ <;> rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C5.idx_k L l with rfl | ⟨q, rfl⟩ <;>
    simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.extendByZeroColumns, _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k, (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L _).symm, L.inj.eq_iff, map_sum, apply_ite, eq_comm]
theorem aB_apply_k (δ : E) (a : AF F) (i k : Fin d.n) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ a i k = if i = L.i₀ ∧ k = L.i₀ then a • inclR (F := F) (AF F) δ else 0 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, Matrix.single_apply, eq_comm]
variable {R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
theorem frameN_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (u b : Fin L.n → AE F E) (a : AF F) :
    inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * cM (u, a)) =
      _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.hN_k L (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_k L u b + Pi.single (Sum.inr L.i₀) (a • inclR (F := F) (AF F) δ - _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.hh_k L u b)) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.wf_k R L u b) := by
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_sM'_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_cM_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.bMat_k, Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add]
  ext (i | i) (k | k)
  all_goals simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.hN_k, Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.one_apply, Pi.add_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.wf_k,
    Pi.smul_apply, smul_eq_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_mulVec_inl_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_mulVec_inr_k, cv, Sum.elim_inl, Sum.elim_inr]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.uA_apply_k]
    by_cases hi : i = L.i₀ <;> simp [hi, Pi.single_apply, Matrix.one_apply]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.aB_apply_k, Matrix.mul_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sum_split_k L]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.D_apply_k]
    rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C5.idx_k L i with rfl | ⟨p, rfl⟩ <;> rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C5.idx_k L k with rfl | ⟨q, rfl⟩ <;>
      simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.sB_apply_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.D_apply_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.extendZeroColumn_apply_embed, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.extension_by_zero_at_base_index, _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k, (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L _).symm, Pi.single_apply, Matrix.one_apply,
        L.inj.eq_iff, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.hh_k, Finset.sum_neg_distrib, sub_eq_add_neg]
  · simp [Pi.single_apply]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.D_apply_k]
    have he := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.e_mul_e_k R
    by_cases hk : k = L.i₀ <;> simp [hk, Pi.single_apply, Matrix.one_apply, ← mul_assoc, he]
def cmp_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (M : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.Mt_k d) (p : (Fin L.n → AE F E) × (Fin L.n → AE F E)) :
    (Fin L.n → AE F E) × (Fin L.n → AE F E) :=
  (fun k => (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_k L p.2 p.1 ᵥ* M) (Sum.inr (L.em k)), fun k => (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_k L p.2 p.1 ᵥ* M) (Sum.inl (L.em k)))
theorem vV_cmp_k {M : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.Mt_k d} (hM : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.IsPad_k L M) (p : (Fin L.n → AE F E) × (Fin L.n → AE F E)) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_k L p.2 p.1 ᵥ* M = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_k L (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k L M p).2 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k L M p).1 := by
  funext r
  rcases r with i | i <;> rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C5.idx_k L i with rfl | ⟨k, rfl⟩
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.pad_vecMul_inl_k hM]; simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.extension_by_zero_at_base_index]
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k, Sum.elim_inl, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.extendZeroColumn_apply_embed]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.pad_vecMul_inr_k hM]; simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.extension_by_zero_at_base_index]
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k, Sum.elim_inr, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.extendZeroColumn_apply_embed]
theorem cmp_cmp_k {J K : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.Mt_k d} (hK : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.IsPad_k L K) (hKJ : K * J = 1) (p : (Fin L.n → AE F E) × (Fin L.n → AE F E)) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k L J (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k L K p) = p := by
  have e := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_cmp_k hK p
  have e2 : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k L J (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k L K p) = (fun k => (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_k L (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k L K p).2 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k L K p).1 ᵥ* J) (Sum.inr (L.em k)),
      fun k => (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_k L (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k L K p).2 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k L K p).1 ᵥ* J) (Sum.inl (L.em k))) := rfl
  rw [e2, ← e, Matrix.vecMul_vecMul, hKJ, Matrix.vecMul_one]
  ext k <;> simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.extendZeroColumn_apply_embed]
theorem extension_by_zero_add (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (x y : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.extendByZeroColumns L (x + y) = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.extendByZeroColumns L x + _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.extendByZeroColumns L y := by
  funext i
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.extendByZeroColumns, mul_add, Finset.sum_add_distrib]
theorem vV_add_k (u b u' b' : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_k L (u + u') (b + b') = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_k L u b + _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_k L u' b' := by
  funext r
  rcases r with i | i <;> simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.extension_by_zero_add]
theorem cmp_add_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (M : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.Mt_k d) (p q : (Fin L.n → AE F E) × (Fin L.n → AE F E)) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k L M (p + q) = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k L M p + _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k L M q := by
  ext k <;> simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_add_k, Matrix.add_vecMul]
theorem continuous_extension_by_zero (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (i : Fin d.n) : Continuous fun x : Fin L.n → AE F E => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.extendByZeroColumns L x i := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.extendByZeroColumns
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_apply k)
theorem continuous_vV_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (r : Fin d.n ⊕ Fin d.n) :
    Continuous fun p : (Fin L.n → AE F E) × (Fin L.n → AE F E) => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_k L p.2 p.1 r := by
  rcases r with i | i
  · exact (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.continuous_extension_by_zero L i).comp continuous_snd
  · exact (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.continuous_extension_by_zero L i).comp continuous_fst
theorem continuous_vVM_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (M : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.Mt_k d) (s : Fin d.n ⊕ Fin d.n) :
    Continuous fun p : (Fin L.n → AE F E) × (Fin L.n → AE F E) => (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_k L p.2 p.1 ᵥ* M) s := by
  simp only [Matrix.vecMul, dotProduct]
  exact continuous_finsetSum _ fun r _ => (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.continuous_vV_k L r).mul continuous_const
theorem continuous_cmp_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (M : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.Mt_k d) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k L M) :=
  (continuous_pi fun _ => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.continuous_vVM_k L M _).prodMk (continuous_pi fun _ => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.continuous_vVM_k L M _)
def cmpEquiv_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {J K : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.Mt_k d} (hJ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.IsPad_k L J) (hK : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.IsPad_k L K) (hKJ : K * J = 1) (hJK : J * K = 1) :
    ((Fin L.n → AE F E) × (Fin L.n → AE F E)) ≃ₜ+ ((Fin L.n → AE F E) × (Fin L.n → AE F E)) where
  toFun := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k L K
  invFun := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k L J
  left_inv p := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_cmp_k hK hKJ p
  right_inv p := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_cmp_k hJ hJK p
  map_add' p q := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_add_k L K p q
  continuous_toFun := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.continuous_cmp_k L K
  continuous_invFun := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.continuous_cmp_k L J
theorem Kmul_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (γ' : G2 σ L.Y) : inFrame d.b (L.j γ')⁻¹ * inFrame d.b (L.j γ') = 1 := by
  rw [← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, inv_mul_cancel, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
theorem Jmul_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (γ' : G2 σ L.Y) : inFrame d.b (L.j γ') * inFrame d.b (L.j γ')⁻¹ = 1 := by
  rw [← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, mul_inv_cancel, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
theorem isPad_inv_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (γ' : G2 σ L.Y) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.IsPad_k L (inFrame d.b (L.j γ')⁻¹) := by
  rw [← map_inv]; exact _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.isPad_j_k L _
theorem K_law_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (γ' : G2 σ L.Y) :
    (inFrame d.b (L.j γ')⁻¹)ᵀ * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R * (inFrame d.b (L.j γ')⁻¹).map (cA σ) = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R :=
  kunf.frame_eq R.hε _
theorem KWK_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (γ' : G2 σ L.Y) :
    inFrame d.b (L.j γ')⁻¹ * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R * ((inFrame d.b (L.j γ')⁻¹).map (cA σ))ᵀ = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_k R := by
  rw [Matrix.mul_assoc, ← _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.JW_k (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.Kmul_k L γ') (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.K_law_k R L γ'), ← Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.Kmul_k, Matrix.one_mul]
theorem qf_vV_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (u b : Fin L.n → AE F E) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.qf_k R (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_k L u b) = cA σ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.hh_k L u b) + ((R.ε : ℤ) : AE F E) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.hh_k L u b := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.qf_k, dotProduct, Fintype.sum_sum_type, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_mulVec_inl_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.W_mulVec_inr_k, cv, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_k, Sum.elim_inl, Sum.elim_inr]
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sum_split_k L, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sum_split_k L]
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.extension_by_zero_at_base_index, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.extendZeroColumn_apply_embed, map_zero, zero_mul, mul_zero, zero_add, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.hh_k, map_sum, map_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cc_k d, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring
def QQ_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (δ : E) (M : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.Mt_k d) (p : (Fin L.n → AE F E) × (Fin L.n → AE F E)) : AF F :=
  ellA δ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.hh_k L (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k L M p).2 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k L M p).1 - _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.hh_k L p.2 p.1)
theorem continuous_hh_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) :
    Continuous fun p : (Fin L.n → AE F E) × (Fin L.n → AE F E) => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.hh_k L p.2 p.1 := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.hh_k
  exact continuous_finsetSum _ fun j _ => ((continuous_apply j).comp continuous_fst).mul
    ((GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ).comp ((continuous_apply j).comp continuous_snd))
theorem continuous_QQ_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (δ : E) (M : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.Mt_k d) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.QQ_k L δ M) := by
  have hl : Continuous (ellA (F := F) δ) := IsModuleTopology.continuous_of_linearMap _
  have h1 : Continuous fun p : (Fin L.n → AE F E) × (Fin L.n → AE F E) => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.hh_k L (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k L M p).2 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k L M p).1 :=
    (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.continuous_hh_k L).comp (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.continuous_cmp_k L M)
  exact hl.comp (h1.sub (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.continuous_hh_k L))
theorem conj_eq_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (γ' : G2 σ L.Y) (b u : Fin L.n → AE F E) (a : AF F) :
    L.j γ' * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * cM (u, a)) =
      _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k L (inFrame d.b (L.j γ')⁻¹) (b, u)).1 *
        cM ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k L (inFrame d.b (L.j γ')⁻¹) (b, u)).2, a + _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.QQ_k L δ (inFrame d.b (L.j γ')⁻¹) (b, u)) * L.j γ' := by
  have hK : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.IsPad_k L (inFrame d.b (L.j γ')⁻¹) := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.isPad_inv_k L γ'
  have hJ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.IsPad_k L (inFrame d.b (L.j γ')) := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.isPad_j_k L γ'
  have hKJ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.Kmul_k L γ'
  have eV : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_k L u b ᵥ* inFrame d.b (L.j γ')⁻¹ =
      _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_k L (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k L (inFrame d.b (L.j γ')⁻¹) (b, u)).2 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k L (inFrame d.b (L.j γ')⁻¹) (b, u)).1 := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_cmp_k hK (b, u)
  have hq : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.qf_k R (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_k L (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k L (inFrame d.b (L.j γ')⁻¹) (b, u)).2 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k L (inFrame d.b (L.j γ')⁻¹) (b, u)).1) =
      _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.qf_k R (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_k L u b) := by
    rw [← eV]; exact _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.qf_vecMul_k (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.KWK_k R L γ') _
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.qf_vV_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.qf_vV_k] at hq
  have hy : cA σ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.hh_k L (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k L (inFrame d.b (L.j γ')⁻¹) (b, u)).2 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k L (inFrame d.b (L.j γ')⁻¹) (b, u)).1 - _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.hh_k L u b) =
      -(((R.ε : ℤ) : AE F E)) *
        (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.hh_k L (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k L (inFrame d.b (L.j γ')⁻¹) (b, u)).2 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k L (inFrame d.b (L.j γ')⁻¹) (b, u)).1 - _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.hh_k L u b) := by
    rw [map_sub]; linear_combination hq
  have hQ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eig_k h _ hy
  apply kunf.inFrame_injective d.b
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul d.b (L.j γ') (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * cM (u, a)), GlobalTheory.EisBL.DoubledParabolic.inFrame_mul d.b _ (L.j γ'),
    _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.frameN_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.frameN_k h, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.conj_hN_k hKJ hJ]
  congr 2
  · rw [Matrix.add_vecMul, eV, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.pad_single_vecMul_k hK]
    congr 2
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.QQ_k, add_smul, hQ]
    ring
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.wf_k, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.JW_k hKJ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.K_law_k R L γ'), ← Matrix.mulVec_mulVec, ← _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cv_vecMul_k, eV]
theorem mem_ratV_iff_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (x : Fin L.n → AE F E) :
    x ∈ L.ratV ↔ ∀ k, x k ∈ (inclR (F := F) (E := E) (AF F)).range := by
  constructor
  · intro hx
    induction hx using AddSubgroup.closure_induction with
    | mem y hy => obtain ⟨z, rfl⟩ := hy; exact fun k => ⟨z k, rfl⟩
    | zero => exact fun k => zero_mem _
    | add y z _ _ hy hz => exact fun k => add_mem (hy k) (hz k)
    | neg y _ hy => exact fun k => neg_mem (hy k)
  · intro hx
    refine AddSubgroup.subset_closure ⟨fun k => (RingHom.mem_range.1 (hx k)).choose, funext fun k => ?_⟩
    exact (RingHom.mem_range.1 (hx k)).choose_spec
theorem index_cases_sum (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (r : Fin d.n ⊕ Fin d.n) :
    r = Sum.inl L.i₀ ∨ r = Sum.inr L.i₀ ∨ ∃ p, r = Sum.map L.em L.em p := by
  rcases r with i | i <;> rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C5.idx_k L i with rfl | ⟨p, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inr ⟨Sum.inl p, rfl⟩)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨Sum.inr p, rfl⟩)
theorem j_em_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (g : G2 σ L.Y) (p q : Fin L.n ⊕ Fin L.n) :
    inFrame d.b (L.j g) (Sum.map L.em L.em p) (Sum.map L.em L.em q) = inFrame L.b g p q := by
  have := congrFun (congrFun (L.j_in g) p) q
  simpa [Matrix.submatrix_apply] using this
theorem j_entries_rat_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {g : G2 σ L.Y} (hg : g ∈ rat2 σ L.Y) (r s : Fin d.n ⊕ Fin d.n) :
    inFrame d.b (L.j g) r s ∈ (inclR (F := F) (E := E) (AF F)).range := by
  have hP := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.isPad_j_k L g
  have hone : ∀ r s, (1 : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.Mt_k d) r s ∈ (inclR (F := F) (E := E) (AF F)).range := fun r s => by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.index_cases_sum L r with rfl | rfl | ⟨p, rfl⟩
  · rw [(hP _ (by simp) s).1]; exact hone _ _
  · rw [(hP _ (by simp) s).1]; exact hone _ _
  · rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.index_cases_sum L s with rfl | rfl | ⟨q, rfl⟩
    · rw [(hP _ (by simp) _).2]; exact hone _ _
    · rw [(hP _ (by simp) _).2]; exact hone _ _
    · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.j_em_k]; exact inFrame_rat_mem L.b hg p q
theorem extension_by_zero_rational (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {x : Fin L.n → AE F E} (hx : ∀ k, x k ∈ (inclR (F := F) (E := E) (AF F)).range)
    (i : Fin d.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.extendByZeroColumns L x i ∈ (inclR (F := F) (E := E) (AF F)).range := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.extendByZeroColumns
  refine Subring.sum_mem _ fun k _ => Subring.mul_mem _ ?_ (hx k)
  split_ifs
  · exact one_mem _
  · exact zero_mem _
theorem cmp_rat_k {M : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.Mt_k d} (hM : ∀ r s, M r s ∈ (inclR (F := F) (E := E) (AF F)).range)
    {p : (Fin L.n → AE F E) × (Fin L.n → AE F E)} (hp1 : ∀ k, p.1 k ∈ (inclR (F := F) (E := E) (AF F)).range)
    (hp2 : ∀ k, p.2 k ∈ (inclR (F := F) (E := E) (AF F)).range) :
    (∀ k, (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k L M p).1 k ∈ (inclR (F := F) (E := E) (AF F)).range) ∧
      ∀ k, (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k L M p).2 k ∈ (inclR (F := F) (E := E) (AF F)).range := by
  have hv : ∀ r, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_k L p.2 p.1 r ∈ (inclR (F := F) (E := E) (AF F)).range := by
    rintro (i | i)
    · exact _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.extension_by_zero_rational L hp2 i
    · exact _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.extension_by_zero_rational L hp1 i
  have hs : ∀ s, (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_k L p.2 p.1 ᵥ* M) s ∈ (inclR (F := F) (E := E) (AF F)).range := fun s => by
    simp only [Matrix.vecMul, dotProduct]
    exact Subring.sum_mem _ fun r _ => Subring.mul_mem _ (hv r) (hM r s)
  exact ⟨fun k => hs _, fun k => hs _⟩
theorem cmpEquiv_apply_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {J K : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.Mt_k d} (hJ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.IsPad_k L J) (hK : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.IsPad_k L K) (hKJ : K * J = 1) (hJK : J * K = 1)
    (p : (Fin L.n → AE F E) × (Fin L.n → AE F E)) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmpEquiv_k L hJ hK hKJ hJK p = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k L K p := rfl
theorem vV_vecMul_apply_k (M : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.Mt_k d) (u b : Fin L.n → AE F E) (s : Fin d.n ⊕ Fin d.n) :
    (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_k L u b ᵥ* M) s = ∑ k, u k * M (Sum.inl (L.em k)) s + ∑ k, b k * M (Sum.inr (L.em k)) s := by
  simp only [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_k, Sum.elim_inl, Sum.elim_inr]
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sum_split_k L, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sum_split_k L]
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.extension_by_zero_at_base_index, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.extendZeroColumn_apply_embed]
end PositivityTheory.SiegelWeilFormula.Act.C5.JC
namespace PositivityTheory.SiegelWeilFormula.Act.C5
open JC
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
variable {R L}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
theorem j_conj'_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (γ' : G2 σ L.Y) :
    ∃ (Λ : ((Fin L.n → AE F E) × (Fin L.n → AE F E)) ≃ₜ+ ((Fin L.n → AE F E) × (Fin L.n → AE F E)))
      (Q : (Fin L.n → AE F E) × (Fin L.n → AE F E) → AF F), Continuous Q ∧
      (∀ b u a, L.j γ' * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * cM (u, a)) = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (Λ (b, u)).1 * cM ((Λ (b, u)).2, a + Q (b, u)) * L.j γ') ∧
      (γ' ∈ rat2 σ L.Y → ∀ w, w ∈ (L.ratV.prod L.ratV : AddSubgroup _) ↔ Λ w ∈ (L.ratV.prod L.ratV : AddSubgroup _)) := by
  refine ⟨_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmpEquiv_k L (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.isPad_j_k L γ') (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.isPad_inv_k L γ') (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.Kmul_k L γ') (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.Jmul_k L γ'), _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.QQ_k L δ (inFrame d.b (L.j γ')⁻¹),
    _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.continuous_QQ_k L δ _, fun b u a => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.conj_eq_k h γ' b u a, fun hr w => ?_⟩
  have hK : ∀ r s, inFrame d.b (L.j γ')⁻¹ r s ∈ (inclR (F := F) (E := E) (AF F)).range := fun r s => by
    have := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.j_entries_rat_k L (inv_mem hr) r s
    rwa [map_inv] at this
  have hJ : ∀ r s, inFrame d.b (L.j γ') r s ∈ (inclR (F := F) (E := E) (AF F)).range := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.j_entries_rat_k L hr
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmpEquiv_apply_k, AddSubgroup.mem_prod, AddSubgroup.mem_prod, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.mem_ratV_iff_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.mem_ratV_iff_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.mem_ratV_iff_k,
    _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.mem_ratV_iff_k]
  constructor
  · rintro ⟨h1, h2⟩
    exact _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_rat_k hK h1 h2
  · rintro ⟨h1, h2⟩
    have := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_rat_k hJ h1 h2
    rwa [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_cmp_k (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.isPad_inv_k L γ') (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.Kmul_k L γ')] at this
theorem j_move'_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (u : Fin L.n → AE F E) (β'' : nA σ L.Y L.b) :
    ∃ (B : Fin L.n → AE F E) (A : AF F), ∀ b a, L.j (nb' β'') * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * cM (u, a)) =
      _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (b + B) * cM (u, a + A) * L.j (nb' β'') := by
  have hK : inFrame d.b (L.j (nb' β''))⁻¹ = inFrame d.b (L.j (nb' (-β''))) := by
    rw [kunf.nb_neg h.nb' β'', map_inv]
  have hfr : inFrame L.b (nb' (-β'')) = Matrix.fromBlocks 1 (-β''.1) 0 1 := by
    rw [h.nb' (-β'')]; rfl
  have k11 : ∀ p q, inFrame d.b (L.j (nb' β''))⁻¹ (Sum.inl (L.em p)) (Sum.inl (L.em q)) =
      (1 : Matrix (Fin L.n) (Fin L.n) (AE F E)) p q := fun p q => by
    have := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.j_em_k L (nb' (-β'')) (Sum.inl p) (Sum.inl q)
    rw [hfr] at this
    rw [hK]; simpa using this
  have k21 : ∀ p q, inFrame d.b (L.j (nb' β''))⁻¹ (Sum.inr (L.em p)) (Sum.inl (L.em q)) = 0 := fun p q => by
    have := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.j_em_k L (nb' (-β'')) (Sum.inr p) (Sum.inl q)
    rw [hfr] at this
    rw [hK]; simpa using this
  have k12 : ∀ p q, inFrame d.b (L.j (nb' β''))⁻¹ (Sum.inl (L.em p)) (Sum.inr (L.em q)) = -β''.1 p q := fun p q => by
    have := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.j_em_k L (nb' (-β'')) (Sum.inl p) (Sum.inr q)
    rw [hfr] at this
    rw [hK]; simpa using this
  have k22 : ∀ p q, inFrame d.b (L.j (nb' β''))⁻¹ (Sum.inr (L.em p)) (Sum.inr (L.em q)) =
      (1 : Matrix (Fin L.n) (Fin L.n) (AE F E)) p q := fun p q => by
    have := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.j_em_k L (nb' (-β'')) (Sum.inr p) (Sum.inr q)
    rw [hfr] at this
    rw [hK]; simpa using this
  set B : Fin L.n → AE F E := fun k => -∑ k', u k' * β''.1 k' k with hB
  have hc : ∀ b, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.cmp_k L (inFrame d.b (L.j (nb' β''))⁻¹) (b, u) = (b + B, u) := fun b => by
    ext k
    · show (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_k L u b ᵥ* _) (Sum.inr (L.em k)) = b k + B k
      rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_vecMul_apply_k]
      simp only [k12, k22, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        if_true, hB, mul_neg, Finset.sum_neg_distrib]
      ring
    · show (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_k L u b ᵥ* _) (Sum.inl (L.em k)) = u k
      rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.vV_vecMul_apply_k]
      simp only [k11, k21, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        if_true, Finset.sum_const_zero, add_zero]
  refine ⟨B, ellA δ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.hh_k L u B), fun b a => ?_⟩
  have e := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.conj_eq_k (R := R) h (nb' β'') b u a
  have hQ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.QQ_k L δ (inFrame d.b (L.j (nb' β''))⁻¹) (b, u) = ellA δ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.hh_k L u B) := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.QQ_k, hc]
    congr 1
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.JC.hh_k, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  rw [hc, hQ] at e
  exact e
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
