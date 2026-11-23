import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.RDIota
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdPlace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdRDSt

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Krd
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section Glue
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
def sc_k : (InfinitePlace F → ℂ) → AE F E := (Place.exists_sec d.cm d.B.emb).choose
theorem sc_cont_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Krd.sc_k d) := (Place.exists_sec d.cm d.B.emb).choose_spec.1
theorem sc_pi_k (x : InfinitePlace F → ℂ) (w : InfinitePlace F) : piInf (d.B.emb w) (_root_.PositivityTheory.SiegelWeilFormula.Krd.sc_k d x) = x w :=
  (Place.exists_sec d.cm d.B.emb).choose_spec.2.1 x w
theorem sc_fin_k (x : InfinitePlace F → ℂ) : finOne F • _root_.PositivityTheory.SiegelWeilFormula.Krd.sc_k d x = 0 := (Place.exists_sec d.cm d.B.emb).choose_spec.2.2.1 x
variable {p : Type} [Fintype p] [DecidableEq p]
def atM_k (w : InfinitePlace F) (Z : Matrix p p ℂ) : Matrix p p (AE F E) :=
  Matrix.of fun i j => _root_.PositivityTheory.SiegelWeilFormula.Krd.sc_k d (fun w' => fam w Z w' i j) + finOne F • (1 : Matrix p p (AE F E)) i j
theorem cw_mul_k {q : Type} [Fintype q] (w : InfinitePlace F) (A B : Matrix q q (AE F E)) :
    d.cw w (A * B) = d.cw w A * d.cw w B :=
  Matrix.map_mul (f := piInf (d.B.emb w))
theorem cw_one_k {q : Type} [DecidableEq q] (w : InfinitePlace F) : d.cw w (1 : Matrix q q (AE F E)) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)
theorem cw_atM_k (w w' : InfinitePlace F) (Z : Matrix p p ℂ) : d.cw w' (_root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z) = fam w Z w' := by
  ext i j
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_apply, _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k, Matrix.of_apply, map_add, _root_.PositivityTheory.SiegelWeilFormula.Krd.sc_pi_k, Place.piInf_finOne, add_zero]
theorem fin_atM_k (w : InfinitePlace F) (Z : Matrix p p ℂ) : finOne F • _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z = finOne F • (1 : Matrix p p (AE F E)) := by
  ext i j
  simp only [Matrix.smul_apply, _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k, Matrix.of_apply, smul_add, _root_.PositivityTheory.SiegelWeilFormula.Krd.sc_fin_k, zero_add, smul_smul, fin_idem]
theorem atM_mul_k (w : InfinitePlace F) (Z Z' : Matrix p p ℂ) : _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w (Z * Z') = _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z * _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z' := by
  refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w' => ?_) ?_
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k]
    unfold fam
    split_ifs <;> simp
  · rw [fin_mul, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k, ← fin_mul, Matrix.mul_one]
theorem atM_one_k (w : InfinitePlace F) : _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w (1 : Matrix p p ℂ) = 1 := by
  refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w' => ?_) ?_
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_one_k]
    unfold fam
    split_ifs <;> rfl
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k]
theorem continuous_atM_k (w : InfinitePlace F) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k (p := p) d w) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine Continuous.add ((_root_.PositivityTheory.SiegelWeilFormula.Krd.sc_cont_k d).comp (continuous_pi fun w' => ?_)) continuous_const
  unfold fam
  split_ifs
  · exact (continuous_apply j).comp ((continuous_apply i).comp continuous_id)
  · exact continuous_const
end Glue
section Iota
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem bb_k : incM F d.b.1 * incM F (d.b⁻¹).1 = 1 := by
  rw [← incM_mul, Units.mul_inv, incM_one]
theorem bb'_k : incM F (d.b⁻¹).1 * incM F d.b.1 = 1 := by
  rw [← incM_mul, Units.inv_mul, incM_one]
def Zm_k (ζ : ℂ) (y : GR d.n) : M2 d.n := dZ d.n ζ⁻¹ * mR y * dZ d.n ζ
theorem Zm_mul_k {ζ : ℂ} (h : ζ ≠ 0) (y y' : GR d.n) : _root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ (y * y') = _root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ y * _root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ y' := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k]
  rw [show mR (y * y') = mR y * mR y' from rfl]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (dZ d.n ζ) (dZ d.n ζ⁻¹), dZ_mul_inv h, Matrix.one_mul]
theorem Zm_one_k {ζ : ℂ} (h : ζ ≠ 0) : _root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ 1 = 1 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k]
  rw [show mR (1 : GR d.n) = 1 from rfl, Matrix.mul_one, dZ_inv_mul h]
def MxI_k (w : InfinitePlace F) (ζ : ℂ) (y : GR d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  incM F d.b.1 * _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w (_root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ y) * incM F (d.b⁻¹).1
theorem MxI_mul_k {ζ : ℂ} (h : ζ ≠ 0) (w : InfinitePlace F) (y y' : GR d.n) : _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ (y * y') = _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y * _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y' := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_mul_k d h, _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_mul_k, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (incM F (d.b⁻¹).1) (incM F d.b.1), _root_.PositivityTheory.SiegelWeilFormula.Krd.bb'_k, Matrix.one_mul]
theorem MxI_one_k {ζ : ℂ} (h : ζ ≠ 0) (w : InfinitePlace F) : _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ 1 = 1 := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_one_k d h, _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_one_k, Matrix.mul_one, _root_.PositivityTheory.SiegelWeilFormula.Krd.bb_k]
theorem inFrame_MxI_k (w : InfinitePlace F) (ζ : ℂ) (y : GR d.n) :
    incM F (d.b⁻¹).1 * _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y * incM F d.b.1 = _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w (_root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ y) := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k, Matrix.mul_assoc]
  rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.bb'_k, Matrix.mul_one, ← Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Krd.bb'_k, Matrix.one_mul]
theorem dbl_incM_k : dbl (incM F d.Y.J) = incM F (dbl d.Y.J) := by
  simp only [dbl, incM, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _)]
  congr 1
  ext i j
  simp
theorem cw_transpose_k {p q : Type} (w : InfinitePlace F) (A : Matrix p q (AE F E)) : d.cw w Aᵀ = (d.cw w A)ᵀ :=
  Matrix.transpose_map
theorem cw_incM_k {p q : Type} (w : InfinitePlace F) (M : Matrix p q E) : d.cw w (incM F M) = M.map (d.B.emb w).1 :=
  Matrix.ext fun i j => PositivityTheory.ThKG.Tow.Levi.piInf_incl (d.B.emb w) (M i j)
theorem map_sig_emb_k {p q : Type} (w : InfinitePlace F) (M : Matrix p q E) :
    (M.map σ).map (d.B.emb w).1 = (M.map (d.B.emb w).1).map star := by
  ext i j
  exact d.cm.2.2.2 _ _
theorem hQ_w_k {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (w : InfinitePlace F) :
    (d.b.1.map (d.B.emb w).1)ᵀ * (dbl d.Y.J).map (d.B.emb w).1 * (d.b.1.map (d.B.emb w).1).map star = Qc d.n ε := by
  have h := congrArg (fun M => M.map (d.B.emb w).1) hε
  simp only [Matrix.map_mul (f := (d.B.emb w).1), _root_.PositivityTheory.SiegelWeilFormula.Krd.map_sig_emb_k] at h
  rw [Matrix.transpose_map] at h
  rw [h]
  simp only [Qc, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]
  congr 1
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
theorem fin_MxI_k (w : InfinitePlace F) (ζ : ℂ) (y : GR d.n) : finOne F • _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y = finOne F • 1 := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k, fin_mul, fin_mul, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k, ← fin_mul, ← fin_mul, Matrix.mul_one, _root_.PositivityTheory.SiegelWeilFormula.Krd.bb_k]
theorem MxI_unitary_k {ε : ℤˣ} {ζ : ℂ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (w : InfinitePlace F) (y : GR d.n) :
    (_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y)ᵀ * dbl (incM F d.Y.J) * (_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y).map (cA σ) = dbl (incM F d.Y.J) := by
  refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w' => ?_) ?_
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Place.cw_cA_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_transpose_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.dbl_incM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k]
    have hM : d.cw w' (_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y) = d.b.1.map (d.B.emb w').1 * fam w (_root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ y) w' * (d.b⁻¹).1.map (d.B.emb w').1 := by
      rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k]
    rw [hM]
    refine conj_unit _ _ _ _ _ ?_ (_root_.PositivityTheory.SiegelWeilFormula.Krd.hQ_w_k d hε w') ?_
    · rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    · unfold fam
      split_ifs
      · exact (unitary_iff hζ (mR y)).2 y.2
      · rw [Matrix.transpose_one, mapStar_one, Matrix.one_mul, Matrix.mul_one]
  · have e1 : (finOne F • (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))).map (cA σ) = finOne F • 1 := by
      rw [map_cA_smul, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [fin_mul, fin_mul, ← Matrix.transpose_smul, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_MxI_k, ← map_cA_smul, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_MxI_k, e1, Matrix.transpose_smul,
      Matrix.transpose_one, ← fin_mul, ← fin_mul, Matrix.mul_one, Matrix.one_mul]
def iotaF_k {ε : ℤˣ} {ζ : ℂ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (w : InfinitePlace F) (y : GR d.n) : d.G :=
  ⟨⟨_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y, _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y⁻¹, by rw [← _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_mul_k d (zeta_ne hζ), mul_inv_cancel, _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_one_k d (zeta_ne hζ)],
    by rw [← _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_mul_k d (zeta_ne hζ), inv_mul_cancel, _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_one_k d (zeta_ne hζ)]⟩, _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_unitary_k d hε hζ w y⟩
def iota_k {ε : ℤˣ} {ζ : ℂ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (w : InfinitePlace F) : GR d.n →* d.G where
  toFun := _root_.PositivityTheory.SiegelWeilFormula.Krd.iotaF_k d hε hζ w
  map_one' := Subtype.ext (Units.ext (_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_one_k d (zeta_ne hζ) w))
  map_mul' a b := Subtype.ext (Units.ext (_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_mul_k d (zeta_ne hζ) w a b))
theorem inFrame_iota_k {ε : ℤˣ} {ζ : ℂ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (w : InfinitePlace F) (y : GR d.n) :
    inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Krd.iota_k d hε hζ w y) = _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w (_root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ y) :=
  _root_.PositivityTheory.SiegelWeilFormula.Krd.inFrame_MxI_k d w ζ y
theorem continuous_iota_k {ε : ℤˣ} {ζ : ℂ}
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (w : InfinitePlace F) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Krd.iota_k d hε hζ w) := by
  have hm : Continuous fun y : GR d.n => mR y := Units.continuous_val.comp continuous_subtype_val
  have hz : Continuous fun y : GR d.n => _root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ y := (continuous_const.matrix_mul hm).matrix_mul continuous_const
  have hM : Continuous fun y : GR d.n => _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y :=
    (continuous_const.matrix_mul ((_root_.PositivityTheory.SiegelWeilFormula.Krd.continuous_atM_k d w).comp hz)).matrix_mul continuous_const
  refine continuous_induced_rng.2 ?_
  refine Units.continuous_iff.2 ⟨hM, ?_⟩
  exact hM.comp continuous_inv
theorem iotaEx_k : _root_.PositivityTheory.SiegelWeilFormula.Krd.IotaEx_k := by
  intro F E _ _ _ _ _ σ d ε ζ hε hζ
  refine ⟨_root_.PositivityTheory.SiegelWeilFormula.Krd.iota_k d hε hζ, _root_.PositivityTheory.SiegelWeilFormula.Krd.continuous_iota_k d hε hζ, fun w y => ?_, fun w w' y hw => ?_, fun w y => ?_⟩
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.inFrame_iota_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k]
    simp only [fam, if_true, _root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, dZ_mul_inv (zeta_ne hζ), Matrix.one_mul]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.inFrame_iota_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k]
    simp only [fam, if_neg hw]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.inFrame_iota_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k]
end Iota
end PositivityTheory.SiegelWeilFormula.Krd
end
end
