import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Glues
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PinchLift

def GenOn {Y : Scheme.{0}} (L : LB Y) (O : Y.Opens) (s : ∀ k, Γ(Y, L.U k ⊓ O)ˣ) : Prop :=
  ∀ (k l : L.ι) (y : Y), y ∈ L.U k → y ∈ L.U l → y ∈ O →
    gm (𝟙 Y) y (L.U k ⊓ O) (s k) = gm (𝟙 Y) y (L.U k ⊓ L.U l) (L.g k l) * gm (𝟙 Y) y (L.U l ⊓ O) (s l)

def Matched {X' Z Z' : Scheme.{0}} (i' : Z' ⟶ X') (p' : Z' ⟶ Z) (L' : LB X') (LZ : LB Z)
    (w : LB.Iso (L'.pull i') (LZ.pull p')) (O' : X'.Opens) (OZ : Z.Opens) (s' : ∀ k, Γ(X', L'.U k ⊓ O')ˣ)
    (sZ : ∀ j, Γ(Z, LZ.U j ⊓ OZ)ˣ) : Prop :=
  ∀ (z : Z') (j : LZ.ι) (k : L'.ι), p' z ∈ LZ.U j → i' z ∈ L'.U k → p' z ∈ OZ → i' z ∈ O' →
    gm p' z (LZ.U j ⊓ OZ) (sZ j) =
      gm (𝟙 Z') z ((LZ.pull p').U (fun _ => j) ⊓ (L'.pull i').U (fun _ => k)) (w.s (fun _ => j, fun _ => k)) *
        gm i' z (L'.U k ⊓ O') (s' k)

end GlobalTheory.PinchLift
