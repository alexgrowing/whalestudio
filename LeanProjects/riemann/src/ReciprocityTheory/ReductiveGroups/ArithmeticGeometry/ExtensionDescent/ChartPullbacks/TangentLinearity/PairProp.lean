import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.Imports
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.WchartPullLe

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf

open Semi

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιD : D.OAct O) (ιG : RingAct G O) (e : ℕ) (a : O) (χ : D.toPre.X)
  (u : LB.Gen (LB.LinComb D.toPre.P.L
    (rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a)) rosatiε))

def PairProp (ρ : Γ((thickObj R I e G).left, ⊤)ˣ) : Prop :=
  ∀ (jA : Fin 4 ⊕ Fin 6 → D.toPre.P.L.ι) (jB : Fin 4 → D.toPre.P.L.ι),
    LB.Coh D.toPre.P.L (φA U ιD e a χ) jA → LB.Coh D.toPre.P.L (φB U ιG e a χ) jB →
    (∀ k k', φB U ιG e a χ k = φA U ιD e a χ k' → jB k = jA k') →
    res (inf_le_right : LB.wchart D.toPre.P.L (φB U ιG e a χ) jB ⊓
        LB.wchart D.toPre.P.L (φA U ιD e a χ) jA ≤ LB.wchart D.toPre.P.L (φA U ιD e a χ) jA)
        ((lhs U ιD e a χ u).s jA) =
      res le_top ρ * res inf_le_left ((rhs U ιG e a χ).s jB)

end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
