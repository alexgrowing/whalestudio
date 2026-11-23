import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValC
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBC

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

section FrRd

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def IsFrRd {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom} (W : UnfAt U k x) (Wu : UnitAt W) (kk : ℤ)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L kk (Over.mk (U.un k x).x))) (θF : (Fin W.g → ℂ) → ℂ) : Prop :=
  ∀ j z (pt : Sp ℂ ⟶ Gx (U.un k x).x),
    pt ≫ gxFst (U.un k x).x = (W.F.ex (W.ik k) W.Pm z).left →
    pt ≫ gxSnd (U.un k x).x = 𝟙 (Sp ℂ) →
    ⊤ ≤ (W.F.ex (W.ik k) W.Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
    valAt' pt ((LPow Xo.univ.t.G Xo.univ.t.PP.L kk (Over.mk (U.un k x).x)).U (fun _ => j))
      (F.f (fun _ => j)) = θF z * Wu.fr j z ^ kk

end FrRd

def VtFrRdSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j)
    (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (xf : ((T.U j σ).X k).dom),
    (∀ τ' i', ‖dmin ((T.U j σ).X k).Gm xf.1 τ' i'‖ = 1) →
    ∀ (W : UnfAt (T.U j σ) k xf) (Wu : UnitAt W) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt ((T.U j σ).X k) xf.1)
      (L : (Fin W.g → ℂ) →ₗ[ℂ] ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim),
    TorusPins W Wu A L →
    ∀ (x x2 : (T.Q.Dw j).La),
      x2 ∈ (Ideal.span {(2 : 𝓞 D.host.E)} *
          (T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) ^ 2) •
            (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La) →
      x2 - x ∈ T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La) →
      ∀ F : LB.Sec (LPow (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP.L ((T.Q.l.M : ℤ) ^ 2)
          (ptO (T.Q.Xo j) ((T.U j σ).un k xf).x)),
      IsVtOver (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP T.Q.l.M (KilledBy (T.Q.Xo j) (T.Q.l.Mb ^ 2))
        ((T.U j σ).un k xf).s (levPt (T.Q.Xo j) ((T.U j σ).un k xf).x x) F →
      IsFrRd W Wu ((T.Q.l.M : ℤ) ^ 2) F (fun z =>
        star (A.T.U (T.Q.l.M ^ 2) (fun _ : Fin 1 => -((((T.Q.l.M : ℂ) ^ 2)⁻¹) • L (star (W.Pm (W.F.t (W.ik k) x2)))))
          (ReciprocityTheory.ChartRestriction.G.I2.s0 A.T ((T.Q.l.M : ℂ) • LinearMap.id) A.s) (fun _ => L (star z))))

section BC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def VtPullSt (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ (S S' : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] [CommRing S'] [Algebra c.F S'] [Algebra ℚ S']
    (φ : S →ₐ[c.F] S') (x0 : Sp S ⟶ Xo.X)
    (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 (ptO Xo x0)))
    (s' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 (ptO Xo (spMap (φ : S →+* S') ≫ x0)))),
    IsPullSec Xo.univ.t.G Xo.univ.t.PP.L 1 (Formalism.MainNotions.ModuliIntegralCharts.H1.ptBC (φ : S →+* S') x0 ▷ Xo.univ.t.G)
      (whiskerRight_snd _ _) s s' →
    ∀ (a : Dw.La)
      (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo x0)))
      (F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo (spMap (φ : S →+* S') ≫ x0)))),
      IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) s (levPt Xo x0 a) F →
      IsPullSec Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2)
        (Formalism.MainNotions.ModuliIntegralCharts.H1.ptBC (φ : S →+* S') x0 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F F' →
      IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) s' (levPt Xo (spMap (φ : S →+* S') ≫ x0) a) F'

def VtUniqSt (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (x0 : Sp S ⟶ Xo.X)
    (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 (ptO Xo x0))) (a : Dw.La)
    (F F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo x0))),
    IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) s (levPt Xo x0 a) F →
    IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) s (levPt Xo x0 a) F' → F = F'

def ThValDescSt (Xo : Moduli Dw l) (c : Coeff l) : Prop :=
  ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y0 : FrPt Xo c S) (K : Type) [Field K] [Algebra c.F K]
      (φ : S →ₐ[c.F] K) (y : FrPt Xo c K), FrMap φ y0 y →
      ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n →
        ∀ v0 w, ThValAt Xo c nab y0 x P v0 → ThValAt Xo c nab y x P w → φ v0 = w

end BC

end ReciprocityTheory.ChartRestriction.G.PullbackSections
