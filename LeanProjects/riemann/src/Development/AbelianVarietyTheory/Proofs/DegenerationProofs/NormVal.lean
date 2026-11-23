import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH
section
variable {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {F : Type} [Field F] [Algebra (FractionRing R) F]

abbrev FrAt (x : TFK (R := R) F ⟶ A.A) : Type :=
  LB.Gen (LB.LinComb A.L (Y := (TFK (R := R) F).left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))

def ValAt {k : ℕ} (t : SecA A F k) (x : TFK (R := R) F ⟶ A.A) (e : FrAt x) (c : F) : Prop :=
  ∀ z J, Good A.L z J → sA t (ptSecT A.A x).left z J =
    @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) * (val (powFrame A.A A.L x e k) (𝟙 _) z J).val

def IsComb {k : ℕ} {J : Type} [Fintype J] (t : J → SecA A F k) (b : J → F) (σ : SecA A F k) : Prop :=
  ∀ j, σ.f j = ∑ l, liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (b l)) * (t l).f j
end
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p}

structure ThetaSys.Real.UTest.Geom (u : ρ.UTest p y₀) where
  pt : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)
  pt_over : ∀ a, (pt a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left
  pt_add : ∀ a b, pt (a + b) = pt a * pt b
  pt_bij : ∀ z : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, z ^ (S.r * S.N) = 1 → ∃! a, pt a = z
  weil : ∀ a b (c : (PadicAlgCl p)ˣ),
    (c : PadicAlgCl p) = y₀ (algebraMap o S.R (S.ζ ^ (S.r * S.N * (eStd S.g _ a b).val))) →
    WeilIs u.A.A u.A.L (S.r * S.N : ℕ) (pt a) (pt b) (unitOn c)
  rig : LB.Gen (u.A.L.pull (eSec u.A.A))
  rig_gen : rig.IsGen
  fr : ∀ a, FrAt (pt a)
  fr_tors : ∀ a, IsTorsFrame u.A rig (S.r * S.N) (pt a) (fr a)
  th : SecA u.A (PadicAlgCl p) 1
  th_val : ∀ a, ValAt th (pt a) (fr a) (y₀ ⟨S.th a, S.th_mem a⟩)
  s : S.J → SecA u.A (PadicAlgCl p) S.N
  ev_val : ∀ a i, ValAt (s i) (pt a) (fr a) (y₀ ⟨S.ev a i, S.ev_mem a i⟩)
  α : LB.Gen (LB.LinComb u.A.L (K := Fin 2) ![(snd (TFK (R := u.V) (PadicAlgCl p)) u.A.A).left,
    (snd (TFK (R := u.V) (PadicAlgCl p)) u.A.A ^ (ρ.n ^ ρ.k)).left] ![(S.N : ℤ), -((1 : ℕ) : ℤ)])
  α_gen : α.IsGen
  α_norm : LB.Gen.Corr u.A.L _ _ _ _ (LB.pullGen u.A.L _ _ α (ptSecT u.A.A 1).left)
    (rigT u.A.A u.A.L rig (TFK (R := u.V) (PadicAlgCl p)) ((S.N : ℤ) - 1))
  s_zero : IsTwistPull u.A.A u.A.L (mulT u.A.A _ (ρ.n ^ ρ.k)) (snd _ u.A.A ^ (ρ.n ^ ρ.k)) (lift_snd _ _)
    (S.N : ℤ) ((1 : ℕ) : ℤ) α th (s ρ.i₀)
  U : S.Gam → ThetaGrp u.A.A u.A.L (S.N : ℤ) (TFK (R := u.V) (PadicAlgCl p))
  U_sym : ∀ a, SymLift u.A.A u.A.L S.N S.N (pt (S.r • a)) (U a)
  U_act : ∀ a i σ, IsActOf u.A.A u.A.L S.N (U a) (s i) σ ↔ IsComb s (fun l => y₀ (algebraMap o S.R (S.ρ a l i))) σ

def NormVal {p : ℕ} [Fact p.Prime] (π : PadicAlgCl p) (v : AddValuation (PadicAlgCl p) (WithTop ℚ)) : Prop :=
  0 < ‖π‖ ∧ ‖π‖ < 1 ∧ ∀ (x : PadicAlgCl p) (q : ℚ), v x = (q : WithTop ℚ) ↔ ‖x‖ = ‖π‖ ^ (q : ℝ)
end GlobalTheory.ZH
end
