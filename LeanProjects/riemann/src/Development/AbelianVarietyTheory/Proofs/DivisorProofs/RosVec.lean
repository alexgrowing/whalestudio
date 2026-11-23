import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfMulComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.XValuePf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointBalancedPowerLift
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TensBal

abbrev Vec (r : ℕ) := Fin r ⊕ Fin r → ℤ

section Formal

variable {r : ℕ}

def lam (u v : Vec r) : Vec r →₀ ℤ :=
  Finsupp.single (u + v) 1 - Finsupp.single u 1 - Finsupp.single v 1 + Finsupp.single 0 1

def theta (a b c : Vec r) : Vec r →₀ ℤ :=
  Finsupp.single (a + b + c) 1 - Finsupp.single (a + b) 1 - Finsupp.single (a + c) 1 - Finsupp.single (b + c) 1 +
    Finsupp.single a 1 + Finsupp.single b 1 + Finsupp.single c 1 - Finsupp.single 0 1

def xv (i : Fin r) : Vec r := Sum.elim (Pi.single i 1) 0

def zv (i : Fin r) : Vec r := Sum.elim 0 (Pi.single i 1)

def axv (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) : Vec r := Sum.elim (fun l => A i l) 0

def azv (A' : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) : Vec r := Sum.elim 0 (fun l => A' i l)

def rosVec (A A' : Matrix (Fin r) (Fin r) ℤ) (a : Fin 6) (i : Fin r) : Vec r :=
  ![axv A i + zv i, axv A i, zv i, xv i + azv A' i, xv i, azv A' i] a

def sig (W A A' : Matrix (Fin r) (Fin r) ℤ) : Vec r →₀ ℤ :=
  ∑ a : Fin 6, ∑ i, ∑ j, (rosatiε a * W i j) • lam (rosVec A A' a i) (rosVec A A' a j)

end Formal

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

def vecHom (T : Tens D D' W) (v : Vec r) : D'.P.A ⊗ D'.P.A ⟶ D.P.A :=
  (∏ k, (fst D'.P.A D'.P.A ≫ T.pr k) ^ v (Sum.inl k)) * ∏ k, (snd D'.P.A D'.P.A ≫ T.pr k) ^ v (Sum.inr k)

def vecLat (T : Tens D D' W) (v : Vec r) (y y' : D'.X) : D.X :=
  ∑ k, v (Sum.inl k) • T.xe y k + ∑ k, v (Sum.inr k) • T.xe y' k

def isoV {X X' Z : Scheme.{0}} {M : LB X} {M' : LB X'} {K₀ : Type} [Fintype K₀] {ψ : K₀ → (X' ⟶ X)} {δ : K₀ → ℤ}
    (w : LB.Iso M' (LB.LinComb M ψ δ)) (z : Z) (J : (Z ⟶ X) → M.ι) (J' : (Z ⟶ X') → M'.ι) (χ : Z ⟶ X') :
    (Z.presheaf.stalk z)ˣ :=
  gm χ z _ (w.s (fun k => J (χ ≫ ψ k), J' χ))

def qv (T : Tens D D' W) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι) (χ : D'.X) :
    ((TK R).left.presheaf.stalk z)ˣ :=
  ∏ i, ∏ j, val (D.tau (T.xe χ i) (T.xe χ j)) (𝟙 _) z J ^ W i j

def rosLat (T : Tens D D' W) (A A' : Matrix (Fin r) (Fin r) ℤ) (y y' : D'.X) : Fin 6 → D'.X :=
  ![GlobalTheory.TensAct.latAct T A y + y', GlobalTheory.TensAct.latAct T A y, y', y + GlobalTheory.TensAct.latAct T A' y', y,
    GlobalTheory.TensAct.latAct T A' y']

def Triv (T : Tens D D' W) (c : Vec r →₀ ℤ) : Prop :=
  ∃ Ξ : LB.Gen (LB.LinComb D.P.L (fun v : c.support => (vecHom T v.1).left) (fun v => c v.1)), Ξ.IsGen ∧
    (∀ (z : (𝟙_ (Over (Spec (CommRingCat.of R)))).left) J, Good D.P.L z J → val Ξ (zero2 D'.P.A) z J = 1) ∧
    ∀ (z : (TK R).left) J, Good D.P.L z J → ∀ y y' : D'.X,
      val Ξ (D'.pt2 y y') z J = ∏ v ∈ c.support, val (D.psi (vecLat T v y y')) (𝟙 _) z J ^ (-(c v))

end GlobalTheory.TensBal
