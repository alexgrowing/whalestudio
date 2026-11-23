import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacExGoodOfN
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HpkMulVecEs
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ExistsPowMulPredGe
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarUniquenessConjugation

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.RI

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj

section Model

variable {k r : ℕ}

theorem cont_of : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r =>
    (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) := by
  exact continuous_id

theorem meas_rmul (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable (Formalism.FourierDecayAlt.B.rmulF a : Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r) := by
  have hc : Continuous (Formalism.FourierDecayAlt.B.rmulF a : Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r) :=
    cont_of.matrix_mul continuous_const
  exact hc.measurable

theorem meas_conj (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable (Formalism.QuantumDeterminants.conjM (k := k) (r := r) a) := by
  have hc : Continuous (Formalism.QuantumDeterminants.conjM (k := k) (r := r) a) :=
    (continuous_const.matrix_mul cont_of).matrix_mul continuous_const
  exact hc.measurable

theorem meas_mulP : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
    (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) := by
  have hc : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) :=
    (cont_of.comp continuous_fst).matrix_mul (cont_of.comp continuous_snd)
  exact hc.measurable

theorem sigmaFinite_of_b {U : Set (Formalism.FourierDecayAlt.B.Mat k r)} {μ : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (h : Formalism.FourierDecayAlt.B.IsHaarOn U μ) : SigmaFinite μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨h.finite_compact⟩
  infer_instance

theorem haarOn_sk_of_b' {U : Set (Formalism.FourierDecayAlt.B.Mat k r)} {μ : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (h : Formalism.FourierDecayAlt.B.IsHaarOn U μ) : Formalism.MainNotions.S.IsHaarOn U μ := by
  exact ⟨sigmaFinite_of_b h, h.ne_zero, h.conc, h.left⟩

theorem det_unit_of_UH {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : IsUnit g.det := by
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  rw [isUnit_iff_ne_zero]
  intro h0
  have h1 := congrArg Matrix.det hg'
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at h1
  exact (Formalism.FourierDecayAlt.P.B2x5.isUnit_det_Hpk k r).ne_zero h1.symm

theorem inv_mem_UW {z : Fin (2 * r + k + 1) → ℂ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UWset k r z) : g⁻¹ ∈ Formalism.QuantumDeterminants.UWset k r z := by
  obtain ⟨hU, hfix, hz⟩ := hg
  have hdet := det_unit_of_UH hU
  have hinv : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hdet
  have hinv' : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hdet
  have hfixinv : ∀ v, g *ᵥ v = v → g⁻¹ *ᵥ v = v := fun v hv => by
    calc g⁻¹ *ᵥ v = g⁻¹ *ᵥ (g *ᵥ v) := by rw [hv]
      _ = v := by rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  refine ⟨?_, fun a => ⟨hfixinv _ (hfix a).1, hfixinv _ (hfix a).2⟩, hfixinv _ hz⟩
  have hU' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hU
  show (g⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * g⁻¹ = Formalism.QuantumDeterminants.Hpk k r
  calc (g⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Formalism.QuantumDeterminants.Hpk k r * g) * g⁻¹ := by rw [hU']
    _ = (g * g⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (g * g⁻¹) := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := by rw [hinv']; simp

theorem muS_right {z : Fin (2 * r + k + 1) → ℂ} (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z)
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} (hW : Formalism.FourierDecayAlt.B.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : Formalism.FourierDecayAlt.B.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) :
    ∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, (Formalism.MainNotions.S.muS μW μN).map (Formalism.FourierDecayAlt.B.rmulF s) = Formalism.MainNotions.S.muS μW μN := by
  intro s hs
  obtain ⟨h0, hh0, n0, hn0, rfl⟩ := hs
  have := sigmaFinite_of_b hW
  have := sigmaFinite_of_b hN
  have hd := det_unit_of_UH hh0.1
  have hinv0 := inv_mem_UW hh0
  have hNc : μN.map (Formalism.QuantumDeterminants.conjM h0⁻¹) = μN :=
    Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k r z μN hz hT hN h0⁻¹ hinv0
  have hW1 : μW.map (Formalism.FourierDecayAlt.B.rmulF h0) = μW := hW.right h0 hh0
  have hN1 : μN.map (Formalism.FourierDecayAlt.B.rmulF n0) = μN := hN.right n0 hn0
  let F : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r :=
    Prod.map (Formalism.FourierDecayAlt.B.rmulF h0) (Formalism.FourierDecayAlt.B.rmulF n0 ∘ Formalism.QuantumDeterminants.conjM h0⁻¹)
  have hFm : Measurable F := (meas_rmul h0).prodMap ((meas_rmul n0).comp (meas_conj _))
  have hF : (μW.prod μN).map F = μW.prod μN := by
    have h2 : μN.map (Formalism.FourierDecayAlt.B.rmulF n0 ∘ Formalism.QuantumDeterminants.conjM h0⁻¹) = μN := by
      rw [← Measure.map_map (meas_rmul n0) (meas_conj _), hNc, hN1]
    haveI : SigmaFinite (μW.map (Formalism.FourierDecayAlt.B.rmulF h0)) := by rw [hW1]; infer_instance
    haveI : SigmaFinite (μN.map (Formalism.FourierDecayAlt.B.rmulF n0 ∘ Formalism.QuantumDeterminants.conjM h0⁻¹)) := by rw [h2]; infer_instance
    rw [← Measure.map_prod_map _ _ (meas_rmul h0) ((meas_rmul n0).comp (meas_conj _)), hW1, h2]
  have hcomm : (Formalism.FourierDecayAlt.B.rmulF (h0 * n0)) ∘
      (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) =
      (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) ∘ F := by
    funext p
    have hi : h0 * h0⁻¹ = 1 := Matrix.mul_nonsing_inv h0 hd
    have hii : (h0⁻¹)⁻¹ = h0 := Matrix.nonsing_inv_nonsing_inv h0 hd
    show Matrix.of p.1 * Matrix.of p.2 * (h0 * n0) =
      (Matrix.of p.1 * h0) * (h0⁻¹ * Matrix.of p.2 * (h0⁻¹)⁻¹ * n0)
    rw [hii]
    calc Matrix.of p.1 * Matrix.of p.2 * (h0 * n0) = Matrix.of p.1 * (h0 * h0⁻¹) * Matrix.of p.2 * h0 * n0 := by
          rw [hi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  unfold Formalism.MainNotions.S.muS
  rw [Measure.map_map (meas_rmul _) meas_mulP, hcomm, ← Measure.map_map meas_mulP hFm, hF]

end Model

theorem psiP_mul {r k : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : IsUnit P.det) (x s : Formalism.REAL.UJ ε) :
    psiP P (x * s) = Formalism.FourierDecayAlt.B.rmulF (P⁻¹ * Formalism.MainNotions.S.uMat s * P) (psiP P x) := by
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  have hm : Formalism.MainNotions.S.uMat (x * s) = Formalism.MainNotions.S.uMat x * Formalism.MainNotions.S.uMat s := by
    simp [Formalism.MainNotions.S.uMat]
  have key : P⁻¹ * Formalism.MainNotions.S.uMat (x * s) * P =
      (P⁻¹ * Formalism.MainNotions.S.uMat x * P) * (P⁻¹ * Formalism.MainNotions.S.uMat s * P) := by
    rw [hm, show P⁻¹ * Formalism.MainNotions.S.uMat x * P * (P⁻¹ * Formalism.MainNotions.S.uMat s * P) =
        P⁻¹ * Formalism.MainNotions.S.uMat x * (P * P⁻¹) * Formalism.MainNotions.S.uMat s * P by simp only [Matrix.mul_assoc], hPP,
      Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  funext i j
  exact congrFun (congrFun key i) j

theorem rightInvS_of (hSC : SetCorr) (hHC : HaarCorr) : RightInvS := by
  intro n r k ε e z z' T T' hF μ hμ s hs
  have hn : n = 2 * r + k + 1 := by have := hF.dim; omega
  subst hn
  obtain ⟨d, hGP⟩ := goodPos_shift hF
  have hF'' := frameLoc_shift hF d
  obtain ⟨P, hPJ, hPdet, hPe, zH, -, hzH, -, hPz, -, hTz, -⟩ :=
    pFrame_holds r k ε e z (z' + ∑ a, d a • e a) T T' hF'' hGP
  have hT : 0 < Formalism.QuantumDeterminants.Tz k r zH := by rw [hTz]; exact hF.T_pos
  obtain ⟨μW0, hW0⟩ := Formalism.FourierDecayAlt.P.weyl_haar_exists k r zH hzH hT
  obtain ⟨μN0, hN0⟩ := Formalism.FourierDecayAlt.P.unipotent_haar_exists k r
  obtain ⟨-, hC⟩ := hHC r k ε e z zH P hPJ hPdet hPe hzH hPz hT hF.k_pos
  obtain ⟨c, -, hm⟩ := hC μW0 μN0 (haarOn_sk_of_b' hW0) (haarOn_sk_of_b' hN0) μ hμ
  have hψs : P⁻¹ * Formalism.MainNotions.S.uMat s * P ∈ Formalism.QuantumDeterminants.Sset k r zH := (hSC r k ε e z zH P hPJ hPdet hPe hzH hPz hT s).1 hs
  have hme : MeasurableEmbedding (psiP (ε := ε) P) :=
    (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi_closedEmbedding (ε := ε) (P := P) Formalism.REAL.uJEmb hPdet).measurableEmbedding
  have hms : Measurable (fun x : Formalism.REAL.UJ ε => x * s) := (continuous_mul_const s).measurable
  have hmap : (μ.map (fun x => x * s)).map (psiP P) = μ.map (psiP P) := by
    rw [Measure.map_map hme.measurable hms]
    have : psiP P ∘ (fun x : Formalism.REAL.UJ ε => x * s) = Formalism.FourierDecayAlt.B.rmulF (P⁻¹ * Formalism.MainNotions.S.uMat s * P) ∘ psiP P := by
      funext x; exact psiP_mul hPdet x s
    rw [this, ← Measure.map_map (meas_rmul _) hme.measurable, hm, Measure.map_smul,
      muS_right hzH hT hW0 hN0 _ hψs]
  rw [← hme.comap_map (μ.map (fun x => x * s)), hmap, hme.comap_map]

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.RI

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

theorem rightInvS_of (hSC : SetCorr) (hHC : HaarCorr) : RightInvS := RI.rightInvS_of hSC hHC

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
