import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValCSteps
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GermExCut

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

def FinExtRootSplitSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (n : ℕ) (x : Fin n → (T.Q.Dw j).La)
    (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io), yI.IsAlg →
    ∃ (Tc' : CDVR) (iT : Tc.Fr →+* Tc'.Fr) (e' : ℕ), 0 < e' ∧
      (∀ a : Tc.Fr, a ≠ 0 → vV Tc'.V (iT a) = (e' : ℤ) * vV Tc.V a) ∧
      ∃ (yI' : IntFr (T.Q.Xo j) T.Q.c Tc' (iT.comp io)), yI'.IsAlg ∧
        (∀ I : IntData (T.Q.Xo j) T.Q.c Tc' (iT.comp io) yI'.1, SplitModel I) ∧
        letI := io.toAlgebra
        letI := (iT.comp io).toAlgebra
        ∃ (φ : Tc.Fr →ₐ[T.Q.c.F] Tc'.Fr)
          (F : Fin n → LB.Sec (LPow (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP.L ((T.Q.l.M : ℤ) ^ 2)
            (ptO (T.Q.Xo j) yI'.1.x))),
          φ.toRingHom = iT ∧ FrMap φ yI.1 yI'.1 ∧
          (∀ b, IsVtOver (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP T.Q.l.M (KilledBy (T.Q.Xo j) (T.Q.l.Mb ^ 2))
            yI'.1.s (levPt (T.Q.Xo j) yI'.1.x (x b)) (F b))

def ThValFinExtSplitSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (nab : NabV (T.Q.Xo j) T.Q.c),
    (∃ _ : StarRing (𝓞 D.host.E), IsNab (T.Q.Xo j) T.Q.c nab) →
    ∀ (w : WeightFamilies.Wt D j) (x : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F),
    P ∈ harmA T.Q.c (wtA w) w.n → ∀ (f : T.R j), IsThRule (T.Q.Xo j) T.Q.c nab x P f →
    ∀ (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io), yI.IsAlg →
    ∃ (Tc' : CDVR) (iT : Tc.Fr →+* Tc'.Fr) (e' : ℕ), 0 < e' ∧
      (∀ a : Tc.Fr, a ≠ 0 → vV Tc'.V (iT a) = (e' : ℤ) * vV Tc.V a) ∧
      ∃ (yI' : IntFr (T.Q.Xo j) T.Q.c Tc' (iT.comp io)), yI'.IsAlg ∧
        (∀ I : IntData (T.Q.Xo j) T.Q.c Tc' (iT.comp io) yI'.1, SplitModel I) ∧
        letI := io.toAlgebra
        letI := (iT.comp io).toAlgebra
        ∃ (φ : Tc.Fr →ₐ[T.Q.c.F] Tc'.Fr)
          (F : Fin w.n → LB.Sec (LPow (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP.L ((T.Q.l.M : ℤ) ^ 2)
            (ptO (T.Q.Xo j) yI'.1.x))),
          φ.toRingHom = iT ∧ FrMap φ yI.1 yI'.1 ∧
          (∀ b, IsVtOver (T.Q.Xo j).univ.t.G (T.Q.Xo j).univ.t.PP T.Q.l.M (KilledBy (T.Q.Xo j) (T.Q.l.Mb ^ 2))
            yI'.1.s (levPt (T.Q.Xo j) yI'.1.x (x b)) (F b)) ∧
          iT (evI yI f) = thExpr (T.Q.Xo j) T.Q.c nab yI'.1 P F

end ReciprocityTheory.ChartRestriction.G.PullbackSections
