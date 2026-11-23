import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.KeyEven

def KeyOn {R K : Type} [CommRing R] [CommRing K] (f : R →+* K) (x : KeyIn K) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : RigLB G)
    (σ : L.L.Sec) (y : Fin x.P.g → (epsR R ⟶ G)) : Prop :=
  ∃ (φ : x.P.A.left ⟶ G.left) (he : eSec x.P.A ≫ φ = spMap f ≫ eSec G) (ψ : LB.Iso x.P.L (L.L.pull φ))
    (F : DualNumber R →+* DualNumber K),
    IsGrpPullback x.P.A G (spMap f) φ ∧ ψ.IsGen ∧
    LB.Gen.Maps (LB.linCombIso ψ (K := PUnit) (fun _ => eSec x.P.A) (fun _ => 1)) x.rig
      (rigPullOf φ (spMap f) he L.L L.rig) ∧
    (∀ (j : (L.L.pull φ).ι) (i : x.P.L.ι) (h : (L.L.pull φ).U j ⊓ x.P.L.U i ≤ φ ⁻¹ᵁ L.L.U (j PUnit.unit)),
      (φ.appLE _ _ h).hom (σ.f (j PUnit.unit)) =
        (show Γ(x.P.A.left, (L.L.pull φ).U j ⊓ x.P.L.U i) from (ψ.s (j, i)).val) * resG _ inf_le_right (x.th.f i)) ∧
    (∀ a, F (algebraMap R _ a) = algebraMap K _ (f a)) ∧ F DualNumber.eps = DualNumber.eps ∧
    ∀ i, (x.v i).left ≫ φ = spMap F ≫ (y i).left

def HasUnif {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G]
    (L : LB G.left) : Prop :=
  ∃ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V)))
    (U : Unif (IsLocalRing.maximalIdeal V) D A G), LBIso U.LG.L L

def UnifAlong {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) →
    ∀ ξ : Sp V ⟶ S, (ξ ⁻¹' abLocus G).Nonempty → ∀ [IsCommMonObj ((Over.pullback ξ).obj G)],
      HasUnif ((Over.pullback ξ).obj G) (L.pull (pullback.fst G.hom ξ))

def PolOnAb {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) : Prop :=
  ∀ W : S.Opens, (W : Set S) ⊆ abLocus G →
    RelAmple ((Over.pullback W.ι).obj G) (L.pull (pullback.fst G.hom W.ι)) ∧
    KTriv ((Over.pullback W.ι).obj G) (L.pull (pullback.fst G.hom W.ι))

def NzFib {S : Scheme.{0}} {G : Over S} {L : LB G.left} (σ : L.Sec) : Prop :=
  ∀ s : S, ∃ z : G.left, G.hom z = s ∧ z ∈ nonzeroLocus σ

def KeyTrait (κ : GlobalTheory.KeyCl.Rule) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) →
    ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ : L.L.Sec) (x : KeyIn (FractionRing V))
      (y : Fin x.P.g → (epsR V ⟶ G)), IsSemiAbelian G → HasUnif G L.L → IsLieBasis y → NzFib σ →
      KeyOn (algebraMap V (FractionRing V)) x G L σ y →
      ∃ u : Vˣ, (κ (FractionRing V) x : FractionRing V) = algebraMap V (FractionRing V) u

def KeyTraitU (κ : GlobalTheory.KeyCl.Rule) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) →
    ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (x : KeyIn (FractionRing V)) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G],
    IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal V) D x.P G) (w₀ : GlobalTheory.UT.W0 U.toUnifPre),
    GlobalTheory.UT.NormW U.toUnifPre w₀ x.rig → ∀ y : Fin x.P.g → (epsR V ⟶ G), IsLieBasis y →
    (∀ i, GlobalTheory.IsVecOver (algebraMap V (FractionRing V)) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) (y i) (x.v i)) →
    ∀ σ : U.LG.L.Sec, NzFib σ →
      GlobalTheory.Cartier.SecMaps w₀ (GlobalTheory.Cartier.secPull x.th U.gen.hom.left) (GlobalTheory.Cartier.secPull σ (pullback.fst G.hom (jK V))) →
      ∃ u : Vˣ, (κ (FractionRing V) x : FractionRing V) = algebraMap V (FractionRing V) u

def KeyLoc (κ : GlobalTheory.KeyCl.Rule) : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CharZero A] [Algebra.FiniteType ℤ A]
    (G : Over (Sp A)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ : L.L.Sec) (x : KeyIn (FractionRing A))
    (y : Fin x.P.g → (epsR A ⟶ G)), IsSemiAbelian G → SmoothOfRelativeDimension x.P.g G.hom → IsOpen (abLocus G) →
    L.IsSymmetric → PolOnAb G L.L → UnifAlong G L.L → IsLieBasis y → NzFib σ →
    KeyOn (algebraMap A (FractionRing A)) x G L σ y →
    ∃ u : Aˣ, (κ (FractionRing A) x : FractionRing A) = algebraMap A (FractionRing A) u

def KeyGlob : Prop :=
  ∀ (S : Scheme.{0}) (s : S ⟶ Sp ℤ) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec), 1 ≤ g → IsIntegral S → Geo.Tor.IsNormalScheme S → LocallyOfFiniteType s →
    CharZero Γ(S, ⊤) → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → (abLocus G).Nonempty → IsOpen (abLocus G) →
    L.IsSymmetric → δ.IsLB → PolOnAb G L.L → UnifAlong G L.L → NzFib σ →
    LBIso (lbPow δ 8) (lbPow (GlobalTheory.SiegelTor.hodge G g) 4)

end GlobalTheory.KeyEven

end
