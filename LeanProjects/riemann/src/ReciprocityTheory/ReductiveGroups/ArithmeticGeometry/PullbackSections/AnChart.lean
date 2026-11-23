import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValCSteps

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField MvPowerSeries
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj

def taylorPS {g : ℕ} (θ : (Fin g → ℂ) → ℂ) : MvPowerSeries (Fin 1 × Fin g) ℂ :=
  fun m => (∏ j : Fin g, (Nat.factorial (m ((0 : Fin 1), j)) : ℂ))⁻¹ *
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.monomial m (1 : ℂ)) (fun p : Fin 1 × Fin g => (Pi.single p.2 1 : Fin g → ℂ))
      θ 0

def AnChartSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)] (σ : T.Q.c.F →+* ℂ),
    GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (xf : ((T.U j σ).X k).dom),
    (∀ τ' i', ‖dmin ((T.U j σ).X k).Gm xf.1 τ' i'‖ = 1) →
    ∀ (nab : NabV (T.Q.Xo j) T.Q.c), IsNab (T.Q.Xo j) T.Q.c nab →
    ∀ (W : UnfAt (T.U j σ) k xf) (Wu : UnitAt W),
      letI : Algebra ℚ (CAt σ) := inferInstanceAs (Algebra ℚ ℂ)
      ∃ (C : ChartAt (T.Q.Xo j) T.Q.c ((T.U j σ).un k xf)) (hd : C.d = W.g),
        C.h = 0 ∧
        (∀ i, C.B.G.F i = (MvPowerSeries.X (R := CAt σ) ((0 : Fin 2), i) + MvPowerSeries.X (R := CAt σ) ((1 : Fin 2), i))) ∧
        (∀ (τ : D.host.E →+* ℂ) (i : Fin ((T.Q.Dw j).mult τ)) (i' : Fin C.d),
          C.uvec ⟨τ, i⟩ i' = if Fin.cast hd i' = W.e.symm ⟨τ, i⟩ then 1 else 0) ∧
        ∀ (kk : ℕ) (F : LB.Sec (LPow (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP.L kk
            (ptO (T.Q.Xo j) ((T.U j σ).un k xf).x))) (θF : (Fin W.g → ℂ) → ℂ),
          IsFrRd W Wu kk F θF →
          IsGerm ((T.U j σ).un k xf) C.d C.x C.B.A.act C.e C.wP kk F
            (MvPowerSeries.rename (fun p : Fin 1 × Fin W.g => (p.1, Fin.cast hd.symm p.2)) (taylorPS θF))

end ReciprocityTheory.ChartRestriction.G.PullbackSections
