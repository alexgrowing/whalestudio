import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SvalUpSec
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecScalIffPullAb
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTermBasis
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenT
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGoodIntegral

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.LN GlobalTheory.TorRef GlobalTheory.IntegralCombination GlobalTheory.UU Formalism.L2.Pj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.IntFam

def StableBasis {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (k : ℕ) (α : D.X) {m : ℕ}
    (b : Fin m → D.SecB k α) : Prop :=
  ∀ (R' : Type) [CommRing R'] (f : R →+* R'),
    ∀ b' : Fin m → LB.Sec (LB.LinComb D.P.L
        (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left ≫ DegPre.famφB D α i)
        (DegPre.famε k)),
      (∀ i, IsPullSecLC D.P.L (DegPre.famφB D α) (DegPre.famε k)
        (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left (b i) (b' i)) →
      IsSecBasis (T := Over.mk (Spec.map (CommRingCat.ofHom f))) (A := D.P.A) _ b'

def IntegralCharts {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R)
    (J : (Spec (CommRingCat.of (FractionRing R)) ⟶ D.P.A.left) → D.P.L.ι) : Prop :=
  ∀ p : Spec (CommRingCat.of R) ⟶ D.P.A.left, p ≫ D.P.A.hom = 𝟙 _ →
    p (closedPoint R) ∈ D.P.L.U (J (jK R ≫ p))

end GlobalTheory.IntFam
