import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyInt
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyIntOm
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ConjEApply
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyIntQ
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.QuotMeasExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HaarOnSkOfB

noncomputable section

open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open Formalism.L2.SG.RealObj.EnergyIntTor
open scoped InnerProductSpace ENNReal

namespace Formalism.L2.SG.RealObj.EnergyIntLoc

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem scale_eq (D : D7) : Formalism.L2.SG.Pf.WuBL.cS D * muT D = Formalism.QuantumDeterminants.cStd := by
  have h1 := Formalism.L2.SG.Pf.WuBL.cS_ne D
  unfold Formalism.L2.SG.Pf.WuBL.cS at h1
  have hka : D.host.ka ≠ 0 := by rintro h; apply h1; simp [h]
  have hg : ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ≠ 0 := by intro h; apply h1; simp [h]
  have hg0 : (D.host.g 0 : ℂ) ≠ 0 := by
    have := (mul_ne_zero_iff.1 hg).1; exact_mod_cast this
  have hg1 : (D.host.g 1 : ℂ) ≠ 0 := by
    have := (mul_ne_zero_iff.1 hg).2; exact_mod_cast this
  have hka' : (D.host.ka : ℂ) ≠ 0 := by exact_mod_cast hka
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold Formalism.L2.SG.Pf.WuBL.cS muT cfS frS Formalism.QuantumDeterminants.cStd
  push_cast
  field_simp

theorem transpC' (C : Choice X θ) (τ : D.what₂.Tau) :
    IsTranspC X (vOf X τ) (cfS D) D.R.k D.R.rS (Qcs C τ) (Qics C τ) :=
  Formalism.L2.SG.Pf.torTie X _ _ _ (C.isT τ)

theorem zc_eq (C : Choice X θ) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    Qics C τ *ᵥ rv X.B.I (vOf X τ) (X.zR u) = zB X (C.Qi τ) u τ := by
  have hw := (Formalism.L2.SG.Pf.zTr C u τ).1
  unfold Qics
  rw [← Matrix.mulVec_mulVec]
  change torS (muT D)⁻¹ D.R.k D.R.rS *ᵥ zB X (C.Qi τ) u τ = zB X (C.Qi τ) u τ
  funext i
  simp only [torS, Matrix.mulVec_diagonal]
  split_ifs with h1 h2
  · rw [hw i (Or.inl h1), mul_zero]
  · rw [hw i (Or.inr h2), mul_zero]
  · rw [one_mul]

theorem sigC_eq (C : Choice X θ) (τ : D.what₂.Tau) (m : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) :
    sigB X (Qcs C τ) (Qics C τ) τ m =
      sigB X (C.Q τ) (C.Qi τ) τ (torS (muT D) D.R.k D.R.rS * m * torS (muT D)⁻¹ D.R.k D.R.rS) := by
  unfold sigB Qcs Qics
  simp only [Matrix.mul_assoc]

theorem piC_eq (C : Choice X θ) (u : D.what₂.Word) (τ : D.what₂.Tau)
    {h : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    (hh : h ∈ Formalism.QuantumDeterminants.UWset D.R.k D.R.rS (zB X (C.Qi τ) u τ)) :
    piB X (Qcs C τ) (Qics C τ) u τ h = piB X (C.Q τ) (C.Qi τ) u τ h := by
  unfold piB Qcs Qics
  have e : C.Q τ * torS (muT D) D.R.k D.R.rS * h * (torS (muT D)⁻¹ D.R.k D.R.rS * C.Qi τ)
      = C.Q τ * (torS (muT D) D.R.k D.R.rS * h * torS (muT D)⁻¹ D.R.k D.R.rS) * C.Qi τ := by
    simp only [Matrix.mul_assoc]
  rw [e, tor_conj_uw (Formalism.L2.SG.Pf.muT_ne D) hh]

theorem inUJ_tr {v : InfinitePlace X.B.I.F} {lam : ℂ} {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ} (hQ : IsTranspC X v lam D.R.k D.R.rS Q Qi)
    {m : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    (hm : m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) : Formalism.REAL.inUJ (X.B.I.ε v) (Q * m * Qi) := by
  obtain ⟨h1, h2, h3, -⟩ := hQ
  unfold Formalism.REAL.inUJ
  have hm' : mᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * m = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hm
  have hJ : Formalism.REAL.Jm (X.B.I.ε v) = Qiᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * Qi := by
    rw [← h3]
    calc Formalism.REAL.Jm (X.B.I.ε v) = (Q * Qi)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * (Q * Qi) := by
          rw [h2]; simp
      _ = Qiᴴ * (Qᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Q) * Qi := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  calc (Q * m * Qi)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * (Q * m * Qi)
      = Qiᴴ * (mᴴ * (Qᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Q) * m) * Qi := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm (X.B.I.ε v) := by rw [h3, hm', hJ]

private theorem conj_mem_lemma (D : D7)
    {a : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    torS (muT D) D.R.k D.R.rS * a * torS (muT D)⁻¹ D.R.k D.R.rS ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
  have hμ := Formalism.L2.SG.Pf.muT_ne D
  have g1 := Formalism.L2.SG.Pf.Choice.torS_gram (k := D.R.k) (r := D.R.rS) (muT D)⁻¹ (inv_ne_zero hμ)
  have g2 := Formalism.L2.SG.Pf.Choice.torS_gram (k := D.R.k) (r := D.R.rS) (muT D) hμ
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * a = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := ha
  show (torS (muT D) D.R.k D.R.rS * a * torS (muT D)⁻¹ D.R.k D.R.rS)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (torS (muT D) D.R.k D.R.rS * a * torS (muT D)⁻¹ D.R.k D.R.rS) = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS
  calc (torS (muT D) D.R.k D.R.rS * a * torS (muT D)⁻¹ D.R.k D.R.rS)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (torS (muT D) D.R.k D.R.rS * a * torS (muT D)⁻¹ D.R.k D.R.rS)
      = (torS (muT D)⁻¹ D.R.k D.R.rS)ᴴ * (aᴴ * ((torS (muT D) D.R.k D.R.rS)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * torS (muT D) D.R.k D.R.rS) * a) * torS (muT D)⁻¹ D.R.k D.R.rS := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := by rw [g2, ha', g1]

theorem sigC_mul (C : Choice X θ) (τ : D.what₂.Tau)
    {a b : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) (hb : b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS))
    (x : X.B.H (vOf X τ)) :
    sigB X (Qcs C τ) (Qics C τ) τ a (sigB X (Qcs C τ) (Qics C τ) τ b x) = sigB X (Qcs C τ) (Qics C τ) τ (a * b) x := by
  rw [sigC_eq, sigC_eq, sigC_eq]
  have hrep := (Formalism.L2.SG.Pf.WuBL.sigB_rep C τ).1.2 _ (conj_mem_lemma D ha) _ (conj_mem_lemma D hb)
  have hi := Formalism.L2.SG.Pf.Choice.torS_inv_mul (k := D.R.k) (r := D.R.rS) (muT D) (Formalism.L2.SG.Pf.muT_ne D)
  have e : torS (muT D) D.R.k D.R.rS * (a * b) * torS (muT D)⁻¹ D.R.k D.R.rS = (torS (muT D) D.R.k D.R.rS * a * torS (muT D)⁻¹ D.R.k D.R.rS) * (torS (muT D) D.R.k D.R.rS * b * torS (muT D)⁻¹ D.R.k D.R.rS) := by
    calc torS (muT D) D.R.k D.R.rS * (a * b) * torS (muT D)⁻¹ D.R.k D.R.rS
        = torS (muT D) D.R.k D.R.rS * a * (torS (muT D)⁻¹ D.R.k D.R.rS * torS (muT D) D.R.k D.R.rS) * b * torS (muT D)⁻¹ D.R.k D.R.rS := by
          rw [hi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = (torS (muT D) D.R.k D.R.rS * a * torS (muT D)⁻¹ D.R.k D.R.rS) * (torS (muT D) D.R.k D.R.rS * b * torS (muT D)⁻¹ D.R.k D.R.rS) := by simp only [Matrix.mul_assoc]
  rw [e, hrep]
  rfl

theorem sigC_norm (C : Choice X θ) (τ : D.what₂.Tau)
    {a : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) (x : X.B.H (vOf X τ)) :
    ‖sigB X (Qcs C τ) (Qics C τ) τ a x‖ = ‖x‖ := by
  rw [sigC_eq]
  exact (Formalism.L2.SG.Pf.WuBL.sigB_rep C τ).2 _ (conj_mem_lemma D ha) x

private theorem mul_mem_UH_Hpk' (D : D7) {a b : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) (hb : b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    a * b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * a = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := ha
  have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * b = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hb
  show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (a * b) = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS
  calc (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := by rw [ha', hb']

theorem dd_sub (C : Choice X θ) (τ : D.what₂.Tau)
    {yc : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    (hyc : yc ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    Formalism.FourierDecayAlt.ThreeDimData.DDsp (sigB X (Qcs C τ) (Qics C τ) τ) (sigB X (Qcs C τ) (Qics C τ) τ yc (X.B.w (vOf X τ))) ≤
      Formalism.FourierDecayAlt.ThreeDimData.DDsp (sigB X (C.Q τ) (C.Qi τ) τ) (v0Of C τ) := by
  have hy := C.y_mem τ
  obtain ⟨hyi, -, hyy⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hy
  have hrep := Formalism.L2.SG.Pf.WuBL.sigB_rep C τ
  unfold Formalism.FourierDecayAlt.ThreeDimData.DDsp
  apply Submodule.span_le.2
  rintro _ ⟨g, hg, rfl⟩
  beta_reduce
  rw [sigC_mul C τ hg hyc, sigC_eq]
  have hg'm : torS (muT D) D.R.k D.R.rS * (g * yc) * torS (muT D)⁻¹ D.R.k D.R.rS ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := conj_mem_lemma D (mul_mem_UH_Hpk' D hg hyc)
  have e : sigB X (C.Q τ) (C.Qi τ) τ (torS (muT D) D.R.k D.R.rS * (g * yc) * torS (muT D)⁻¹ D.R.k D.R.rS * (C.y τ)⁻¹) (v0Of C τ)
      = sigB X (C.Q τ) (C.Qi τ) τ (torS (muT D) D.R.k D.R.rS * (g * yc) * torS (muT D)⁻¹ D.R.k D.R.rS) (X.B.w (vOf X τ)) := by
    unfold v0Of
    rw [← ContinuousLinearMap.comp_apply, ← hrep.1.2 _ (mul_mem_UH_Hpk' D hg'm hyi) _ hy,
      Matrix.mul_assoc, hyy, Matrix.mul_one]
  rw [← e]
  exact Submodule.subset_span ⟨_, mul_mem_UH_Hpk' D hg'm hyi, rfl⟩

end Formalism.L2.SG.RealObj.EnergyIntLoc
