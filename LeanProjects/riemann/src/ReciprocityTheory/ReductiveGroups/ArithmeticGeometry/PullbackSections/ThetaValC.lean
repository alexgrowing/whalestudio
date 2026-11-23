import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.TorusPin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData
import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

def ThetaValCSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (nab : NabV (T.Q.Xo j) T.Q.c),
    (∃ _ : StarRing (𝓞 D.host.E), IsNab (T.Q.Xo j) T.Q.c nab) →
    ∀ (w : WeightFamilies.Wt D j) (x : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F),
    P ∈ harmA T.Q.c (wtA w) w.n → ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c nab x P f →
    ∀ (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (xf : ((T.U j σ).X k).dom),
    (∀ τ' i', ‖dmin ((T.U j σ).X k).Gm xf.1 τ' i'‖ = 1) →
    ∀ (W : UnfAt (T.U j σ) k xf) (Wu : UnitAt W) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt ((T.U j σ).X k) xf.1)
      (L : (Fin W.g → ℂ) →ₗ[ℂ] ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim),
    TorusPins W Wu A L →
    ∀ (x2 : Fin w.n → (T.Q.Dw j).La),
      (∀ b, x2 b ∈ (Ideal.span {(2 : 𝓞 D.host.E)} *
          (T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) ^ 2) •
            (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La)) →
      (∀ b, x2 b - x b ∈ T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La)) →
      toC (evR (T.Q.Xo j) T.Q.c f ((T.U j σ).un k xf)) =
        ((T.Q.l.M : ℂ)⁻¹) ^ P.totalDegree *
          star (ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.map ((starRingEnd ℂ).comp σ) P)
            (fun l => Pi.single l.2.2 (L (Pi.single (W.e.symm ⟨l.1, l.2.1⟩) 1)))
            (A.T.U (T.Q.l.M ^ 2) (fun b => -((((T.Q.l.M : ℂ) ^ 2)⁻¹) • L (star (W.Pm (W.F.t (W.ik k) (x2 b))))))
              (ReciprocityTheory.ChartRestriction.G.I2.s0 A.T ((T.Q.l.M : ℂ) • LinearMap.id) A.s)) 0)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
