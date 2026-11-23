import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDual1Dot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodORingOfIntegers

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition

noncomputable section

namespace GlobalTheory.Pass.LocDual

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

def locU {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous fun g => M g) :
    GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) :=
  GlobalTheory.JumpDual.matG ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) (Br.loc D.nbr i w hw M)
    (GlobalTheory.JumpDual.loc_cont D i w hw M hM)

def IsSummandTw (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i))
    (X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw)) : Prop :=
  ∃ (a : ℕ) (x : Fin a → ↥Xs) (j : X.V →ₗ[Br.LL D.nbr i w hw] (Fin a → Fin D.R.nV → Br.LL D.nbr i w hw)),
    Function.Injective j ∧
    (∀ g v, j (X.ρ g v) = fun b => (Br.loc D.nbr i w hw (rTwO D.nd i r (x b)) g).mulVec (j v b)) ∧
    ∃ C : Submodule (Br.LL D.nbr i w hw) (Fin a → Fin D.R.nV → Br.LL D.nbr i w hw),
      (∀ g, ∀ u ∈ C, (fun b => (Br.loc D.nbr i w hw (rTwO D.nd i r (x b)) g).mulVec (u b)) ∈ C) ∧
      IsCompl (LinearMap.range j) C

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL]

def DualLatLe (U U' : GRep G Qp LL O) (LT : Lattice (O := O) U.ρ) (P : U.V →ₗ[LL] U'.V →ₗ[LL] LL) (b : ℕ) : Prop :=
  ∃ LT' : Lattice (O := O) U'.ρ, IsDualLat1 PD LT LT' P ∧ finrank O ↥(latticeFiniteCohomology PD LT') + finrank O ↥LT.T ≤ b

end Gen

end GlobalTheory.Pass.LocDual

end
