import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TransSec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.MBX
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBEx

def d8 {A U : Type} [CommGroup A] [CommGroup U] (e : A → U) (x y z : A) : U :=
  e (x * y * z) * (e (x * y))⁻¹ * (e (x * z))⁻¹ * (e (y * z))⁻¹ * e x * e y * e z * (e 1)⁻¹

section Generic

variable {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] {X : Scheme.{0}} (F : A.left ⟶ X) (M : LB X)

abbrev ThGen : Type := LB.Gen (LB.LinComb M (fun I : thK.{0} => thφ A (x3 A) I ≫ F) thε)

variable {A F M}

def pt3 (x y z : 𝟙_ (Over (Sp K)) ⟶ A) : Sp K ⟶ (G3 A).left := (lift x (lift y z)).left

def cv (t : ThGen A F M) (j : thK.{0} → M.ι) (x y z : 𝟙_ (Over (Sp K)) ⟶ A) : K :=
  valR (pt3 x y z) (LB.wchart M (fun I : thK.{0} => thφ A (x3 A) I ≫ F) j) (t.s j).val

variable [IsCommMonObj A]

def GCub (t : ThGen A F M) : Prop :=
  t.IsGen ∧ ∀ (T : Over (Sp K)) (z : T.left) (J : (T.left ⟶ X) → M.ι), Good M z J →
    IsCub fun a b c : T ⟶ A => val t (lift a (lift b c)).left z J

def RootRel (t : ThGen A F M) (N : ℕ) (J : (Sp K ⟶ X) → M.ι) (e : (𝟙_ (Over (Sp K)) ⟶ A) → Kˣ) : Prop :=
  (∀ q : Sp K ⟶ X, ⊤ ≤ q ⁻¹ᵁ M.U (J q)) ∧ ∃ n : ℕ, n ≠ 0 ∧ ∀ x y z : 𝟙_ (Over (Sp K)) ⟶ A, x ^ N = 1 → y ^ N = 1 →
    z ^ N = 1 → cv t (fun I => J (pt3 x y z ≫ thφ A (x3 A) I ≫ F)) x y z ^ n = ((d8 e x y z : Kˣ) : K) ^ n

end Generic

def UnitAt {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {P : PolAV (Sp K)} {N : ℕ} (m : TGrp R K P N) {M : LB m.AA.left} (t : ThGen P.A m.φ M) : Prop :=
  ∀ (v : IsDedekindDomain.HeightOneSpectrum R) (z : Sp R) (x y w : Tor P N) (j : thK.{0} → M.ι),
    z.asIdeal = v.asIdeal →
    (lift (m.τ x) (lift (m.τ y) (m.τ w))).left z ∈ LB.wchart M (thφ m.AA (x3 m.AA)) j →
    v.valuation K (cv t j x.1 y.1 w.1) = 1

end GlobalTheory.MBEx

end
