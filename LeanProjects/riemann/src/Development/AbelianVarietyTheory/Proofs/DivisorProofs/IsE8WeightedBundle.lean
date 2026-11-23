import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.E8Fibration

def e8 (W : Matrix (Fin 8) (Fin 8) ℤ) : Matrix (Fin 8) (Fin 8) ℤ := W + W.transpose

def actMat (W : Matrix (Fin 8) (Fin 8) ℤ) : Fin 2 → Matrix (Fin 8) (Fin 8) ℤ :=
  ![(e8 W).adjugate * W, (e8 W).adjugate * W.transpose]

variable {S : Scheme.{0}}

def IsProd {A B : Over S} [GrpObj A] [GrpObj B] (pr : Fin 8 → (A ⟶ B)) : Prop :=
  (∀ a, IsMonHom (pr a)) ∧ ∀ (T : Over S) (y : Fin 8 → (T ⟶ B)), ∃! x : T ⟶ A, ∀ a, x ≫ pr a = y a

def IsE8WeightedBundle (W : Matrix (Fin 8) (Fin 8) ℤ) {A B : Over S} [GrpObj A] [GrpObj B] (pr : Fin 8 → (A ⟶ B))
    (L : LB A.left) (M : LB B.left) : Prop :=
  LBIso L (LB.LinComb M (K := (Fin 8 × Fin 8) × Fin 4) (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2)
    (fun k => -(W k.1.1 k.1.2 * negε k.2)))

def IsPPFib (B : Over S) [GrpObj B] (g : ℕ) (M : RigLB B) : Prop :=
  IsAbelianScheme B ∧ SmoothOfRelativeDimension g B.hom ∧ Nonempty (CubicalStr B M) ∧ RelAmple B M.L ∧ KTriv B M.L

def ActsBy {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj B] (pr : Fin 8 → (A ⟶ B)) (f : A ⟶ A)
    (m : Matrix (Fin 8) (Fin 8) ℤ) : Prop :=
  ∀ a, f ≫ pr a = ∏ b, pr b ^ m a b

end GlobalTheory.Poinc.Sep.E8Fibration

end
