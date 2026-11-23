import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.IntSmooth

noncomputable section

namespace PositivityTheory.RgBcC.VC

theorem trZero : TrZero := by
  intro V _ _ _ B T e i c hc hei heB hTe
  let t : (V →L[ℂ] V) → ℂ := fun A => LinearMap.trace ℂ V (A : V →ₗ[ℂ] V)
  have tadd : ∀ A A' : V →L[ℂ] V, t (A + A') = t A + t A' := fun A A' => by
    simp only [t, ContinuousLinearMap.coe_add, map_add]
  have tneg : ∀ A : V →L[ℂ] V, t (-A) = -t A := fun A => by
    simp only [t, ContinuousLinearMap.coe_neg, map_neg]
  have tsmul : ∀ (a : ℂ) (A : V →L[ℂ] V), t (a • A) = a * t A := fun a A => by
    simp only [t, ContinuousLinearMap.coe_smul, map_smul, smul_eq_mul]
  have tcomm : ∀ A A' : V →L[ℂ] V, t (A * A') = t (A' * A) := fun A A' =>
    LinearMap.trace_mul_comm ℂ (A : V →ₗ[ℂ] V) (A' : V →ₗ[ℂ] V)
  set X := B * T with hXdef
  have hX : e * X = -(X * e) := by
    calc e * X = (e * B) * T := (mul_assoc _ _ _).symm
      _ = -(B * e) * T := by rw [heB]
      _ = -(B * (e * T)) := by rw [neg_mul, mul_assoc]
      _ = -(B * (T * e)) := by rw [hTe]
      _ = -(X * e) := by rw [hXdef, mul_assoc]
  have h1 : X * (e * i + i * e) = c • X := by rw [hei, mul_smul_comm, mul_one]
  have key : c * t X = 0 := by
    rw [← tsmul, ← h1, mul_add, tadd, ← mul_assoc, ← mul_assoc, tcomm (X * i) e, ← mul_assoc, hX,
      neg_mul, tneg, add_neg_cancel]
  exact (mul_eq_zero.mp key).resolve_left hc

end PositivityTheory.RgBcC.VC
