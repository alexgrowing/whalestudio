import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.KronConjTranspose
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.LefRho

noncomputable section

open Matrix
open scoped Kronecker ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem cxData_of (hCP : CfPair) (hM : MtLaws) (hG : GamMul) (hB : Car) (hC : GamCre) (hScal : GamScal) (hN : Number)
    (hRL : RmLaws) (hRC : RmChar) (hA : Avg) (hF : MatrixFrechetDerivativeAtZeroLaws) (hS : SwapLaws)
    (hTD : ∀ (n : ℕ) (lam : Fin n → ℤ), lefT n lam * (∑ p, lefε n lam (hb p) * fderiv ℝ (lefFr n lam) 1 (hb p)) =
      -((∑ p, lefε n lam (hb p) * fderiv ℝ (lefFr n lam) 1 (hb p)) * lefT n lam))
    (hEig : ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ w : EV n lam,
      IsEig (infOf lam) fun x => lefFr n lam x⁻¹ (lefS n lam 0 w))
    {n : ℕ} (lam : Fin n → ℤ) (hlam : Antitone lam) :
    CxData lam (lefE n lam) (lefFr n lam) (lefε n lam) (lefι n lam) (lefS n lam) (lefΓ n lam) (lefT n lam) := by
  have hQ : IsUnit (sqQ lam) := (hA n lam).1
  exact
    { smooth := smooth_f hF
      one := one_f hQ hF
      mul := mul_f hQ hF
      onK := fun k => rfl
      car := car_f hQ hB hCP
      frι := frι_f hQ hC hM
      frε := frε_f hQ hC hM
      Γsq := Γsq_f hQ hG
      Γε := Γε_f hQ hG hC
      Γι := Γι_f hQ hG hC
      ΓFr := fun x _ => ΓFr_f hQ hG x
      ΓT := ΓT_f hQ hG
      Tsq := Tsq_f hQ hS
      Tiso := Tiso_f hQ hA hS
      TK := TK_f hQ hS
      Tε := Tε_f hQ hS
      Tι := Tι_f hQ hS
      TD := hTD n lam
      Ssmooth := Ssmooth_f hScal
      S1 := sym_one_eq_one hQ hG
      Sε := Sε_f hQ hG hC
      Sder := Sder_f hQ hScal hN
      SΓ := SΓ_f hQ hG
      S0sq := S0sq_f hQ hG
      S0Γ := S0Γ_f hQ hG
      sym_zero_comm_frame := fun x _ => sym_zero_comm_frame_matrix hQ hG x
      time_comm_sym_zero := time_comm_sym_zero_matrix hQ hG
      S0θ := S0θ_f hQ hS hG
      eig := hEig n lam hlam
      char := char_f hQ hG hScal hS hRL hRC hlam }

end PositivityTheory.RgBcC
