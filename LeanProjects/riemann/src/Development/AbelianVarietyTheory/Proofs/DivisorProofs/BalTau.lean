import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UTau0

section Bal

variable {R : Type} [CommRing R] {B : Over (Sp R)} [GrpObj B] [IsCommMonObj B] (M : RigLB B) (cub : CubicalStr B M)
  {O : Type} [CommRing O] [StarRing O] (act : RingAct B O) {X : Type} [AddCommGroup X] [Module O X]
  (c : X → (𝟙_ (Over (Sp R)) ⟶ B))

def BalTau (τ : ∀ y z : X, LB.Gen (LB.LinComb M.L (GlobalTheory.PolDeg.lamPts (c y) (c z)) GlobalTheory.PolDeg.negε)) : Prop :=
  (∀ y z, (τ y z).IsGen) ∧
  (∀ y y' z p J, Good M.L p J →
    val (τ (y + y') z) (𝟙 _) p J * cubV cub p J (c y) (c y') (c z) =
      val (τ y z) (𝟙 _) p J * val (τ y' z) (𝟙 _) p J) ∧
  (∀ y z z' p J, Good M.L p J →
    val (τ y (z + z')) (𝟙 _) p J * cubV cub p J (c z) (c z') (c y) =
      val (τ y z) (𝟙 _) p J * val (τ y z') (𝟙 _) p J) ∧
  (∀ (a : O) (u : LB.Gen (LB.LinComb M.L (rosatiφ B (act.act a) (act.act (star a))) rosatiε)), u.IsGen →
    LB.Gen.Corr M.L _ _ _ _ (LB.pullGen M.L _ _ u (zero2 B)) (LB.oneGen M.L) →
    ∀ y z p J, Good M.L p J →
      val (τ (a • y) z) (𝟙 _) p J * val u (lift (c y) (c z)).left p J = val (τ y (star a • z)) (𝟙 _) p J)

end Bal

section Psi

variable {R : Type} [CommRing R] [IsDomain R]

abbrev w0φ (D₀ : DegPre R) (f : D₀.P.A ⟶ D₀.P.A) : Fin 4 → (D₀.P.A.left ⟶ D₀.P.A.left) :=
  ![(padd D₀.P.A (𝟙 _) f).left, 𝟙 D₀.P.A.left, f.left, (toUnit D₀.P.A ≫ η[D₀.P.A]).left]

abbrev w0ε : Fin 4 → ℤ := ![1, -2, -1, 2]

def rigV (D₀ : DegPre R) (p : Sp R) (J : (Sp R ⟶ D₀.P.A.left) → D₀.P.L.ι) :=
  val (L := D₀.P.L) (φ := fun _ : PUnit => eSec D₀.P.A) (ε := fun _ => 1) D₀.rig (𝟙 _) p J

def tauV (D₀ : DegPre R)
    (ψ : ∀ y : D₀.X, LB.Gen (LB.LinComb D₀.P.L (K := PUnit) (fun _ => (D₀.c y).left) (fun _ => -1)))
    (p : Sp R) (J : (Sp R ⟶ D₀.P.A.left) → D₀.P.L.ι) (y z : D₀.X) :=
  val (ψ (y + z)) (𝟙 _) p J * (val (ψ y) (𝟙 _) p J)⁻¹ * (val (ψ z) (𝟙 _) p J)⁻¹ * (rigV D₀ p J)⁻¹

def RLaws (D₀ : DegPre R) {O : Type} [CommRing O] [StarRing O] [Module O D₀.X] (onB : D₀.P.OAct O) (w0 : O)
    (uw : LB.Gen (LB.LinComb D₀.P.L (w0φ D₀ (onB.act w0)) w0ε))
    (ψ : ∀ y : D₀.X, LB.Gen (LB.LinComb D₀.P.L (K := PUnit) (fun _ => (D₀.c y).left) (fun _ => -1))) : Prop :=
  (∀ y, (ψ y).IsGen) ∧
  (∀ y y' z p J, Good D₀.P.L p J →
    tauV D₀ ψ p J (y + y') z * cubV D₀.cub p J (D₀.c y) (D₀.c y') (D₀.c z) = tauV D₀ ψ p J y z * tauV D₀ ψ p J y' z) ∧
  (∀ y p J, Good D₀.P.L p J → val (ψ (-y)) (𝟙 _) p J * val D₀.sym (D₀.c y).left p J = val (ψ y) (𝟙 _) p J) ∧
  (∀ (a : O) (u : LB.Gen (LB.LinComb D₀.P.L (rosatiφ D₀.P.A (onB.act a) (onB.act (star a))) rosatiε)), u.IsGen →
    LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ u (zero2 D₀.P.A)) (LB.oneGen D₀.P.L) →
    ∀ y z p J, Good D₀.P.L p J →
      tauV D₀ ψ p J (a • y) z * val u (lift (D₀.c y) (D₀.c z)).left p J = tauV D₀ ψ p J y (star a • z)) ∧
  (∀ y p J, Good D₀.P.L p J →
    tauV D₀ ψ p J y (w0 • y) * val uw (D₀.c y).left p J = val (ψ y) (𝟙 _) p J * rigV D₀ p J)

end Psi

end GlobalTheory.UTau0
