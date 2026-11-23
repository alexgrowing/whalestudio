import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointGramMinorsAgreeProof
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopTermLem

noncomputable section
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf
namespace GlobalTheory.TypeAsm.FramePf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ka_div (D : D7) : D.host.ka / (2 * Real.pi) = (2 * D.host.v)⁻¹ := by
  have h0 : 0 < D.host.rdE := GlobalTheory.TypeAsm.GramPf.rdE_pos' D
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  simp only [Formalism.BasicNotions.Host.ka, Formalism.BasicNotions.Host.v]
  field_simp

theorem two_v_pos (D : D7) : 0 < 2 * D.host.v := by
  have h0 : 0 < D.host.rdE := GlobalTheory.TypeAsm.GramPf.rdE_pos' D
  simp only [Formalism.BasicNotions.Host.v]
  linarith

theorem phiV_frame (D : D7) (X : HidaSetting D) (C : Choice X 1) (τ : D.what₂.Tau) (a : Fin D.R.rS) :
    GlobalTheory.TypeAsm.phiV C τ (X.eX a) =
                 (((2 * D.host.v) ^ (D.R.rS - a.val) : ℝ) : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) ∧
    GlobalTheory.TypeAsm.phiV C τ (X.fY a) =
                 ((((2 * D.host.v) ^ (D.R.rS - a.val))⁻¹ : ℝ) : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) := by
  obtain ⟨hQiQ, _, _, hfr⟩ := C.isT τ
  obtain ⟨h1, h2⟩ := hfr a a rfl
  have hc : ((2 * D.host.v) ^ (D.R.rS - a.val) : ℝ) ≠ 0 := pow_ne_zero _ (two_v_pos D).ne'
  have hfp : frS D ^ (D.R.rS - a.val) = ((((2 * D.host.v) ^ (D.R.rS - a.val))⁻¹ : ℝ) : ℂ) := by
    unfold frS
    rw [ka_div, ← Complex.ofReal_pow, inv_pow]
  unfold GlobalTheory.TypeAsm.phiV
  constructor
  · have e : rv X.B.I (vOf X τ) (X.crd (X.eX a)) =
        ((((2 * D.host.v) ^ (D.R.rS - a.val)) : ℝ) : ℂ) • (C.Q τ *ᵥ Pi.single (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) 1) := by
      rw [h1, hfp, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hc, Complex.ofReal_one, one_smul]
      rfl
    rw [e, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hQiQ, Matrix.one_mulVec]
    rfl
  · have e : rv X.B.I (vOf X τ) (X.crd (X.fY a)) =
        ((((2 * D.host.v) ^ (D.R.rS - a.val))⁻¹ : ℝ) : ℂ) • (C.Q τ *ᵥ Pi.single (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) 1) := by
      rw [h2, hfp, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_inv, inv_inv, smul_smul,
        ← Complex.ofReal_mul, inv_mul_cancel₀ hc, Complex.ofReal_one, one_smul]
      rfl
    rw [e, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hQiQ, Matrix.one_mulVec]
    rfl

end GlobalTheory.TypeAsm.FramePf
