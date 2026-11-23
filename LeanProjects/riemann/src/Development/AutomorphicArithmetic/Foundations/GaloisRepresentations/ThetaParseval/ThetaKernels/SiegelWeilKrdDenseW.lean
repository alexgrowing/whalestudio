import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.DenseW
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdRDIota
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdPlace

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Krd.DM
open PositivityTheory.SiegelWeilFormula.Krd.DC
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem dblJ_det_k {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n ε) : (dbl d.Y.J).det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det hε
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero, zero_mul] at this
  exact QR_det_ne E ε this.symm
def bX_k (X : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E :=
  d.b.1 * X * (d.b⁻¹).1
theorem bX_unitary_k {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n ε)
    {X : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E} (hX : Xᵀ * QR E d.n ε * X.map σ = QR E d.n ε) :
    (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_k d X)ᵀ * dbl d.Y.J * (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_k d X).map σ = dbl d.Y.J :=
  conj_unitE (σ : E →+* E) d.b.1 (d.b⁻¹).1 X (dbl d.Y.J) (QR E d.n ε) (Units.mul_inv d.b) hε hX
def ratG_k {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n ε)
    (X : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) (hX : Xᵀ * QR E d.n ε * X.map σ = QR E d.n ε) : d.G :=
  ⟨Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F))
    (Matrix.nonsingInvUnit (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_k d X) (isUnit_iff_ne_zero.2 (det_ne_of (σ : E →+* E) (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_unitary_k d hε hX) (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.dblJ_det_k d hε)))),
    by
      show (incM F (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_k d X))ᵀ * dbl (incM F d.Y.J) * (incM F (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_k d X)).map (cA σ) = dbl (incM F d.Y.J)
      rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.dbl_incM_k d, incM_cA, incM_alt_bis, ← incM_mul, ← incM_mul, _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_unitary_k d hε hX]⟩
theorem ratG_mem_k {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n ε)
    (X : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) (hX : Xᵀ * QR E d.n ε * X.map σ = QR E d.n ε) :
    _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.ratG_k d hε X hX ∈ rat2 σ d.Y :=
  Subgroup.mem_subgroupOf.2 ⟨_, rfl⟩
theorem inFrame_ratG_k {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n ε)
    (X : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) (hX : Xᵀ * QR E d.n ε * X.map σ = QR E d.n ε) :
    inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.ratG_k d hε X hX) = incM F X := by
  show incM F (d.b⁻¹).1 * incM F (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_k d X) * incM F d.b.1 = incM F X
  rw [← incM_mul, ← incM_mul]
  congr 1
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_k, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
theorem inFrame_mul_k (x z : d.G) : inFrame d.b (x * z) = inFrame d.b x * inFrame d.b z := by
  show incM F (d.b⁻¹).1 * (mat2 x * mat2 z) * incM F d.b.1 =
    (incM F (d.b⁻¹).1 * mat2 x * incM F d.b.1) * (incM F (d.b⁻¹).1 * mat2 z * incM F d.b.1)
  calc incM F (d.b⁻¹).1 * (mat2 x * mat2 z) * incM F d.b.1 =
      incM F (d.b⁻¹).1 * mat2 x * (incM F d.b.1 * incM F (d.b⁻¹).1) * mat2 z * incM F d.b.1 := by
        rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.bb_k d, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]
theorem inFrame_inj_k {x z : d.G} (h : inFrame d.b x = inFrame d.b z) : x = z := by
  have e : ∀ u : d.G, mat2 u = incM F d.b.1 * inFrame d.b u * incM F (d.b⁻¹).1 := fun u => by
    simp only [inFrame, ← Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Krd.bb_k d, Matrix.one_mul]
    rw [Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Krd.bb_k d, Matrix.mul_one]
  apply Subtype.ext
  apply Units.ext
  show mat2 x = mat2 z
  rw [e x, e z, h]
end PositivityTheory.SiegelWeilFormula.Krd.DM
open PositivityTheory.SiegelWeilFormula.Krd PositivityTheory.SiegelWeilFormula.Krd.DM PositivityTheory.SiegelWeilFormula.Krd.DC in
theorem PositivityTheory.SiegelWeilFormula.Krd.denseW_k : _root_.PositivityTheory.SiegelWeilFormula.DenseW_k := by
  intro F E _ _ _ _ _ σ d R w y O hO hy
  have h0 := zeta_ne R.hζ
  have hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n R.ε := R.hε
  obtain ⟨X, hXU, hXO⟩ := exists_rat d.cm (d.B.emb w).1 R.hζ hO hy
  have hX := rat_unitary d.cm (d.B.emb w).1 R.ε X hXU
  refine ⟨_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.ratG_k d hε X hX, _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.ratG_mem_k d hε X hX, _, hXO, _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.ratG_k d hε X hX * (R.ι w (Phi R.hζ ⟨_, hXU⟩))⁻¹,
    (inv_mul_cancel_right _ _).symm, fun y'' => ?_⟩
  set y' := Phi R.hζ ⟨X.map (d.B.emb w).1, hXU⟩ with hy'
  set A := inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.ratG_k d hε X hX * (R.ι w y')⁻¹) with hA
  have hAC : A * inFrame d.b (R.ι w y') = incM F X := by
    rw [hA, ← _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_mul_k, inv_mul_cancel_right, _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_ratG_k]
  have hC : d.cw w (inFrame d.b (R.ι w y')) = X.map (d.B.emb w).1 := by
    have e := R.at_w w y'
    rw [show mR y' = dZ d.n R.ζ * X.map (d.B.emb w).1 * dZ d.n R.ζ⁻¹ from rfl, Matrix.mul_assoc _ (dZ _ R.ζ⁻¹),
      dZ_inv_mul h0, Matrix.mul_one] at e
    have := congrArg (fun M => dZ d.n R.ζ⁻¹ * M) e
    simpa only [← Matrix.mul_assoc, dZ_inv_mul h0, Matrix.one_mul] using this
  have hdet := det_of_inU hXU
  have hAw : d.cw w A = 1 := by
    have e : d.cw w A * X.map (d.B.emb w).1 = X.map (d.B.emb w).1 := by
      have := congrArg (d.cw w) hAC
      rwa [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, hC, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k] at this
    calc d.cw w A = d.cw w A * X.map (d.B.emb w).1 * (X.map (d.B.emb w).1)⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = 1 := by rw [e, Matrix.mul_nonsing_inv _ hdet]
  apply _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_inj_k d
  rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_mul_k d _ (R.ι w y''), _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_mul_k d (R.ι w y''), ← hA]
  refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w' => ?_) ?_
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k]
    by_cases hw : w' = w
    · subst hw; rw [hAw, Matrix.one_mul, Matrix.mul_one]
    · rw [R.off_w w w' y'' hw, Matrix.one_mul, Matrix.mul_one]
  · rw [fin_mul, fin_mul, R.off_f w y'', ← fin_mul, ← fin_mul, Matrix.mul_one, Matrix.one_mul]
end
end
