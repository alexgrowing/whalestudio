import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct

def KeyOver {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R K : Type} [CommRing R] [Field K]
    (f : R →+* K) (t : SAB H (Sp R)) (th : t.PP.L.Sec) (x : KeyIn K) (v : Fin x.P.g → (epsR R ⟶ t.G)) : Prop :=
  ∃ (φ : x.P.A.left ⟶ t.G.left) (he : eSec x.P.A ≫ φ = spMap f ≫ eSec t.G) (w : LB.Iso x.P.L (t.PP.L.pull φ)),
    IsGrpPullback x.P.A t.G (spMap f) φ ∧ w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec x.P.A) (fun _ => 1)) x.rig
      (rigPullOf φ (spMap f) he t.PP.L t.PP.rig) ∧
    (∀ (j : (t.PP.L.pull φ).ι) (i : x.P.L.ι) (h : (t.PP.L.pull φ).U j ⊓ x.P.L.U i ≤ φ ⁻¹ᵁ t.PP.L.U (j PUnit.unit)),
      (φ.appLE _ _ h).hom (th.f (j PUnit.unit)) =
        (show Γ(x.P.A.left, (t.PP.L.pull φ).U j ⊓ x.P.L.U i) from (w.s (j, i)).val) *
          resG _ inf_le_right (x.th.f i)) ∧
    ∀ i, (x.v i).left ≫ φ = spMap (dualMap f) ≫ (v i).left

def KeyBadSt : Prop :=
  ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.UnitSp κ →
    GlobalTheory.KeyCl.ThetaOne κ → GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R K : Type) [CommRing R] [IsDomain R]
      [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)] [Field K] [CharZero K] [Algebra R K]
      [IsFractionRing R K] (t : SAB H (Sp R))
      (th : t.PP.L.Sec) (x : KeyIn K) (v : Fin x.P.g → (epsR R ⟶ t.G)),
      KeyOver (algebraMap R K) t th x v → IsLieBasis v →
      (∀ (d : R) (th' : t.PP.L.Sec), (∀ i, th.f i = constFn t.G.hom _ d * th'.f i) → IsUnit d) →
      (κ K x : K) ∈ Set.range (algebraMap R K)

end GlobalTheory.CompanionTheory.Ar.Sl
