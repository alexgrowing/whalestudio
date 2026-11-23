import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistedPrincipalPolarisationSectionsBaseChange
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsThirdToSixthOfLaws
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfCoord
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TestFibre

section
variable {R : Type} [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
  {F : Type} [Field F] [Algebra (FractionRing R) F]

abbrev cF (R : Type) [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F] (c : F) :
    Γ((TFK (R := R) F).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c

def IsComb {k : ℕ} {J : Type} [Fintype J] (s : J → SecA A F k) (b : J → F) (t : SecA A F k) : Prop :=
  ∀ j, t.f j = ∑ l, liftFun A.A _ (cF R (b l)) * (s l).f j

abbrev FrameAt (x : TFK (R := R) F ⟶ A.A) : Type :=
  LB.Gen (LB.LinComb A.L (Y := (TFK (R := R) F).left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))

def ValIs {k : ℕ} (t : SecA A F k) (x : TFK (R := R) F ⟶ A.A) (e : FrameAt A x) (c : F) : Prop :=
  ∀ z J, Good A.L z J → sA t (ptSecT A.A x).left z J =
    @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) * (val (powFrame A.A A.L x e k) (𝟙 _) z J).val

def IsNormPull (ρ : LB.Gen (A.L.pull (eSec A.A))) (m N : ℕ) (th : SecA A F 1) (s : SecA A F N) : Prop :=
  ∃ α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, (snd (TFK (R := R) F) A.A ^ m).left]
      ![(N : ℤ), -((1 : ℕ) : ℤ)]),
    α.IsGen ∧ LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left)
      (rigT A.A A.L ρ (TFK (R := R) F) ((N : ℤ) - 1)) ∧
    IsTwistPull A.A A.L (mulT A.A _ m) (snd _ A.A ^ m) (lift_snd _ _) (N : ℤ) ((1 : ℕ) : ℤ) α th s

end

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)

def PtsOver (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)) : Prop :=
  ∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left

def SecsOver (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)) (rig : LB.Gen (u.A.L.pull (eSec u.A.A)))
    (e : ∀ a, FrameAt u.A (x a)) (th : SecA u.A (PadicAlgCl p) 1) (s : S.J → SecA u.A (PadicAlgCl p) S.N) : Prop :=
  rig.IsGen ∧ (∀ a, IsTorsFrame u.A rig (S.r * S.N) (x a) (e a)) ∧
  (∀ a, ValIs u.A th (x a) (e a) (y₀ ⟨S.th a, S.th_mem a⟩)) ∧
  (∀ i a, ValIs u.A (s i) (x a) (e a) (y₀ ⟨S.ev a i, S.ev_mem a i⟩)) ∧
  IsNormPull u.A rig (ρ.n ^ ρ.k) S.N th (s ρ.i₀) ∧
  ∀ a, ∃ θ : ThetaGrp u.A.A u.A.L (S.N : ℤ) (TFK (R := u.V) (PadicAlgCl p)),
    SymLift u.A.A u.A.L S.N S.N (x (S.r • a)) θ ∧ ∀ i σ, IsActOf u.A.A u.A.L S.N θ (s i) σ →
      IsComb u.A s (fun j => y₀ (algebraMap o S.R (S.ρ a j i))) σ

def NormIs (l : u.Lab) (ϖ : u.V) (Q : u.D.toPre.X → ℤ) (v : AddValuation (PadicAlgCl p) (WithTop ℚ)) (lam : ℝ) : Prop :=
  0 < lam ∧ QForm.IsQ u.D.toPre ϖ Q ∧ (∀ χ, l.q χ = lam * Q χ) ∧
  (∀ (c : PadicAlgCl p) (r : ℚ), (r : WithTop ℚ) ≤ v c ↔ ‖c‖ ≤ Real.exp (-(lam * r))) ∧
  ∀ (c : PadicAlgCl p) (r : ℚ), v c = (r : WithTop ℚ) ↔ ‖c‖ = Real.exp (-(lam * r))

theorem laws_all (h : Laws) (h₂ : Laws2) :
    LL ∧ TwistBCSpanStatement ∧ TWM.VRatioGtStatement ∧ TWStatement ∧ UUStatement := by
  have hS : SecBaseChangeSt := h.secBaseChange
  have hT : TwistBCSpanStatement := twistBCSpan_of twistBaseChange
  exact ⟨⟨h, h₂, laws3, uniformisationLaws_of_baseChange_laws polBaseChange_holds globalFns_holds hS twistBaseChange,
      laws5 globalFns_holds hS⟩, hT, RatioVal.main, TWM.tw_of globalFns_holds hT RatioVal.main,
    UnitBallFree.main globalFns_holds twistBaseChange⟩

end GlobalTheory.TestFibre
end
