import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementJ
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowTwoTorsionWp
import Formalism.EllipticTorsion.FormalGroupPointsNoTorsion

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.A

namespace Bridge

section Ball

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem integral_of_coeff {f : K⟦X⟧} (h : ∀ n, coeff n f ∈ Formalism.G.unitBall K) :
    Formalism.DworkPowerSeriesWeights.Integral (ι := Unit) f := by
  unfold Formalism.DworkPowerSeriesWeights.Integral
  intro n
  have e : n = Finsupp.single () (n ()) := by
    ext
    simp
  have hn := h (n ())
  rw [e]
  exact hn

theorem integral_of_mvCoeff {ι : Type} {f : MvPowerSeries ι K}
    (h : ∀ n, MvPowerSeries.coeff n f ∈ Formalism.G.unitBall K) : Formalism.DworkPowerSeriesWeights.Integral f := by
  unfold Formalism.DworkPowerSeriesWeights.Integral
  intro n
  exact h n

theorem integral_map {ι : Type} (c : MvPowerSeries ι (Formalism.G.unitBall K)) :
    Formalism.DworkPowerSeriesWeights.Integral (MvPowerSeries.map (Formalism.G.unitBall K).subtype c) := by
  unfold Formalism.DworkPowerSeriesWeights.Integral
  intro n
  rw [MvPowerSeries.coeff_map]
  exact (MvPowerSeries.coeff n c).2

def model (W : WeierstrassCurve K) (h : IntModel W) : WeierstrassCurve (Formalism.G.unitBall K) :=
  ⟨⟨W.a₁, h.1⟩, ⟨W.a₂, h.2.1⟩, ⟨W.a₃, h.2.2.1⟩, ⟨W.a₄, h.2.2.2.1⟩, ⟨W.a₆, h.2.2.2.2⟩⟩

theorem model_map (W : WeierstrassCurve K) (h : IntModel W) :
    (model W h).map (Formalism.G.unitBall K).subtype = W := by
  rfl

end Ball

end Bridge

open Bridge

theorem bridgeWp_of (h : WpCleared.{0}) : BridgeWp := by
  unfold BridgeWp
  intro K _ _ W
  exact h K W

theorem bridgeLaw_of (hM : CoeffMem.{0}) (hFL : FglLog.{0}) (hHS : HalfSpec.{0})
    (hHL : HalfLog.{0, 0}) : BridgeLaw := by
  intro K _ _ _ W hW
  obtain ⟨-, -, -, -, -, hi, hF, -, hh, -, -⟩ :=
    hM K W (Formalism.G.unitBall K) hW.1 hW.2.1 hW.2.2.1 hW.2.2.2.1 hW.2.2.2.2
  obtain ⟨hl0, hl1, -, -⟩ := logSpec K W
  refine ⟨⟨(fglChord K W).2.2.2.2.1, integral_of_mvCoeff hF, hl0, hl1, ?_⟩,
    ⟨(iSerSpec K W).1, integral_of_coeff hi, (logNeg K W).1⟩, fun h2 => ?_⟩
  · unfold Formalism.InvariantFactorPaths.G7.cob Formalism.InvariantFactorPaths.G7.at1
    rw [(hFL K W).1]
    ring
  · have hu : IsUnit (2 : K) := isUnit_iff_ne_zero.mpr two_ne_zero
    refine ⟨(hHS K W hu).1, integral_of_coeff (hh ⟨2⁻¹, ?_, mul_inv_cancel₀ two_ne_zero⟩), ?_⟩
    · change ‖(2 : K)⁻¹‖ ≤ 1
      rw [norm_inv, h2, inv_one]
    · have key := hHL.1 K W
      have h21 : (C (2 : K)⁻¹ : K⟦X⟧) * 2 = 1 := by
        rw [← map_ofNat (C : K →+* K⟦X⟧) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
      calc (logSer W).subst (halfSer W)
          = (C (2 : K)⁻¹ * 2) * (logSer W).subst (halfSer W) := by rw [h21, one_mul]
        _ = C (2 : K)⁻¹ * (2 * (logSer W).subst (halfSer W)) := by ring
        _ = C (2 : K)⁻¹ * logSer W := by rw [key]

theorem bridgeCurve_of (hM : CoeffMem.{0}) (hU : WpInU.{0}) (hC : CubeTwoR.{0}) :
    BridgeCurve := by
  intro K _ _ _ W hW
  obtain ⟨-, hx, -⟩ :=
    hM K W (Formalism.G.unitBall K) hW.1 hW.2.1 hW.2.2.1 hW.2.2.2.1 hW.2.2.2.2
  refine ⟨integral_of_coeff hx, CurveSer.xS_cc W, hU K W, ?_⟩
  obtain ⟨c, hc0, hc⟩ := hC (Formalism.G.unitBall K) (model W hW)
  refine ⟨MvPowerSeries.map (Formalism.G.unitBall K).subtype c, integral_map c, ?_, ?_⟩
  · rw [MvPowerSeries.constantCoeff_map, hc0]
    simp
  · have hi0 : constantCoeff (iSer (model W hW)) = 0 := (iSerSpec _ (model W hW)).1
    have hs : MvPowerSeries.HasSubst
        (![U₁, (iSer (model W hW)).subst
            (U₂ : MvPowerSeries (Fin 2) (Formalism.G.unitBall K))] :
          Fin 2 → MvPowerSeries (Fin 2) (Formalism.G.unitBall K)) := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro i
      fin_cases i
      · simp
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        exact PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X 1) _ hi0
    have key := congrArg (MvPowerSeries.map (Formalism.G.unitBall K).subtype) hc
    rw [map_sub, map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, MvPowerSeries.map_X,
      MvPowerSeries.map_X, PowerSeries.map_subst (HasSubst.X 0),
      PowerSeries.map_subst (HasSubst.X 1), MvPowerSeries.map_X, MvPowerSeries.map_X,
      CurveSer.map_xS, MvPowerSeries.map_subst hs, fglMap, model_map] at key
    unfold Formalism.L2.Th1.B.FI Formalism.InvariantFactorPaths.G7.at1
    rw [key]
    congr 2
    funext i
    fin_cases i
    · simp
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [PowerSeries.map_subst (HasSubst.X 1), MvPowerSeries.map_X, CurveSer.map_iSer, model_map]

theorem bridgeTwo_of (hM : CoeffMem.{0}) (hT : TInZ.{0}) (hZ : TwoTorsionZ.{0}) : BridgeTwo := by
  unfold BridgeTwo
  intro K _ _ _ W xT yT heq h2y
  obtain ⟨_, _, _, _, hdvd, h2c, _, hder, _, _, _⟩ := hZ K W xT yT heq h2y
  have hT' := hT K W xT
  have hD : constantCoeff (1 + X ^ 2 * wpReg W - C (xT + W.b₂ / 12) * X ^ 2 : K⟦X⟧) ≠ 0 := by
    simp
  have h3 : (C (3 : K) : K⟦X⟧) = 3 := by
    rw [show (3 : K) = ((3 : ℕ) : K) by norm_num, map_natCast]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · unfold Formalism.L2.Th1.B.wOf
    calc (tS W xT).subst (expSer W)
        = (tS W xT).subst (expSer W) * ((1 + X ^ 2 * wpReg W - C (xT + W.b₂ / 12) * X ^ 2)
          * (1 + X ^ 2 * wpReg W - C (xT + W.b₂ / 12) * X ^ 2)⁻¹) := by
          rw [PowerSeries.mul_inv_cancel _ hD, mul_one]
      _ = ((tS W xT).subst (expSer W) * (1 + X ^ 2 * wpReg W - C (xT + W.b₂ / 12) * X ^ 2))
          * (1 + X ^ 2 * wpReg W - C (xT + W.b₂ / 12) * X ^ 2)⁻¹ := by ring
      _ = X ^ 2 * (1 + X ^ 2 * wpReg W - C (xT + W.b₂ / 12) * X ^ 2)⁻¹ := by rw [hT']
  · unfold Formalism.L2.Th1.B.IsW
    obtain ⟨q, hq⟩ := hdvd
    refine ⟨?_, h2c, ?_⟩
    · rw [hq]
      simp
    · show (PowerSeries.derivative K ((tS W xT).subst (expSer W))) ^ 2 = _
      rw [hder, map_mul, h3]
      ring
  · intro hI hx
    apply Bridge.integral_of_coeff
    exact (hM K W (Formalism.G.unitBall K) hI.1 hI.2.1 hI.2.2.1 hI.2.2.2.1 hI.2.2.2.2).2.2.2.2.2.2.2.2.2.1 xT hx

end Formalism.L2.Th1.A
