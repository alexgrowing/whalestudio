import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaSectionsClosedFibre

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

section General

variable {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) {N : LB Y}

def IsSmul (r : R) (s s' : LB.Sec N) : Prop :=
  ∀ j : N.ι, s'.f j = resTop (N.U j) (scal p r) * s.f j

def Generates (s : LB.Sec N) : Prop :=
  ∀ s' : LB.Sec N, ∃ r : R, IsSmul p r s s'

def NonzeroOnClosedFibre [IsLocalRing R] (s : LB.Sec N) : Prop :=
  ∃ j : N.ι,
    ((pullback.fst p (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).app (N.U j)).hom
      (s.f j) ≠ 0

end General

section Theta

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def HasExpansion (U : UnifPre I D A G) (σ : H0 U.LG.L 1) (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α) :
    Prop :=
  ∀ e : ℕ, U.ExpandsAt e 1 σ f

def WeightZeroIs (U : UnifPre I D A G) (σ : H0 U.LG.L 1) (th : H0 D.toPre.P.L 1) : Prop :=
  ∃ f : ∀ α : D.toPre.X, D.toPre.SecB 1 α, HasExpansion U σ f ∧
    GeneratorPullback.SecScal D.toPre.P.L (fun _ : Fin 1 => 𝟙 D.toPre.P.A.left) (fun _ => ((1 : ℕ) : ℤ)) th
      (D.toPre.famφB 0) (DegPre.famε 1) (f 0) (𝟙 D.toPre.P.A.left) 1

def IsThetaSec (U : UnifPre I D A G) (σ : H0 U.LG.L 1) : Prop :=
  ∃ th : H0 D.toPre.P.L 1, Generates D.toPre.P.A.hom th ∧ WeightZeroIs U σ th

def ExistsThetaSec (U : UnifPre I D A G) : Prop :=
  ∃ σ : H0 U.LG.L 1, IsThetaSec U σ

def ThetaSecGenerates (U : UnifPre I D A G) : Prop :=
  ∀ σ : H0 U.LG.L 1, IsThetaSec U σ → Generates G.hom σ

def GeneratesIffNonzero [IsLocalRing R] (U : UnifPre I D A G) : Prop :=
  ∀ s : H0 U.LG.L 1, Generates G.hom s ↔ NonzeroOnClosedFibre G.hom s

def NonzeroImpThetaSec [IsLocalRing R] (U : UnifPre I D A G) : Prop :=
  ∀ s : H0 U.LG.L 1, NonzeroOnClosedFibre G.hom s → IsThetaSec U s

structure ThetaClaims [IsLocalRing R] (U : UnifPre I D A G) : Prop where
  exists_theta : ExistsThetaSec U
  theta_generates : ThetaSecGenerates U
  generates_iff : GeneratesIffNonzero U
  theta_of_nonzero : NonzeroImpThetaSec U

end Theta

def ThetaClaimsOver (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) : Prop :=
  ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ U : Unif I D A G, ThetaClaims U.toUnifPre

def ThetaDvrSt : Prop :=
  Laws → Laws4 →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
      [IsAdicComplete (IsLocalRing.maximalIdeal V) V],
      ThetaClaimsOver V (IsLocalRing.maximalIdeal V)

def ThetaArcSt : Prop :=
  Laws → Laws4 →
    ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
      [IsAdicComplete (IsLocalRing.maximalIdeal O') O'],
      ThetaClaimsOver (PowerSeries O') (Ideal.span {(PowerSeries.X : PowerSeries O')})

def ThetaSectionSt : Prop := ThetaDvrSt ∧ ThetaArcSt

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaSectionsClosedFibre
