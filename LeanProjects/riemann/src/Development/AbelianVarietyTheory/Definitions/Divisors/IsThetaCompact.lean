import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ}

structure Trait (F : SFam g n ζ) where

  V : Type
  [ring : CommRing V]
  [dom : IsDomain V]
  [dvr : IsDiscreteValuationRing V]
  [char : CharZero V]
  complete : IsAdicComplete (maximalIdeal V) V

  ϖ : V
  irr : Irreducible ϖ

  y : Sp (FractionRing V) ⟶ F.X

  G : Over (Sp V)
  [grp : GrpObj G]
  [comm : IsCommMonObj G]
  semi : IsSemiAbelian G

  D : DegData V (maximalIdeal V)

  A : PolAV (Sp (FractionRing V))

  U : Unif (maximalIdeal V) D A G

  α : A.A.left ⟶ F.univ.A.left

  α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left
  cart : IsGrpPullback A.A F.univ.A y α
  sq : IsSquare α α₂
  lb : LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂)

  β : LinearMap.BilinForm ℤ D.toPre.X
  symm : ∀ a b, β a b = β b a
  mono : IsMonomial D.toPre ![ϖ] ![β]

attribute [instance] Trait.ring Trait.dom Trait.dvr Trait.char Trait.grp Trait.comm

def ValOn (F : SFam g n ζ) {S : Scheme.{0}} (j : F.X ⟶ S) (φ : InvFun ℤ) (J : S.IdealSheafData) (d : ℕ) : Prop :=
  ∀ (T : Trait F) (ξ : Sp T.V ⟶ S), jK T.V ≫ ξ = T.y ≫ j →
    ∃ a : ℕ, (a : ℝ) = d * φ.evalZ T.β ∧ idlAlong J ξ = Ideal.span {T.ϖ ^ a}

def SharpOver (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) {T : Scheme.{0}} (P : PolAV T) (u : T ⟶ F.X) : Prop :=
  ∃ c : SiegPre g n ζ (u ≫ F.s), SiegPB c F.univ u ∧ ∃ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) ∧
    (∀ (T' : Over T) (y : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y a) ∧
    LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2))

def ThetaInt (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) {Z : Scheme.{0}} (i : F.X ⟶ Z) : Prop :=
  ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real)
    (u : Sp S.R ⟶ F.X), SharpOver F W ρ.P u → (∀ w, (spMap S.R.val.toRingHom ≫ u) w ∈ genericPoints F.X) →
    ∀ (M : RatModel o' Ω) (π : M.Z ⟶ Z), IsNormalScheme M.Z → M.pt ≫ π = spMap S.R.val.toRingHom ≫ u ≫ i →
      M.HasDiv S.th

def IsNormBl {S Z : Scheme.{0}} (π : S ⟶ Z) (J : Z.IdealSheafData) : Prop :=
  IsNormalScheme S ∧ ∃ (S₀ : Scheme.{0}) (π₀ : S₀ ⟶ Z) (ν : S ⟶ S₀) (U : S₀.Opens), FinalTheorems.Blowup π₀ J ∧ ν ≫ π₀ = π ∧
    IsFinite ν ∧ Dense (U : Set S₀) ∧ Dense (ν ⁻¹' U : Set S) ∧ IsIso (ν ∣_ U)

def IsThetaCompact (F : SFam g n (zetaAway n)) {Z : Scheme.{0}} (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) : Prop :=
  IsProjOver z ∧ IsNormalScheme Z ∧ IsOpenImmersion i ∧ i ≫ z = F.s ∧ Dense (Set.range i) ∧
    ∃ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W ∧ ThetaInt F W i

def IdealSt : Prop :=
  ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n))
    (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ →
      ∃ (d : ℕ) (J : Z.IdealSheafData), 1 ≤ d ∧ (∀ x ∈ J.support, x ∉ Set.range i) ∧ ValOn F i φ J d

def PoinSt : Prop :=
  ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n))
    (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ OZ : LB Z, OZ.IsLB → IsAmpleLB OZ → ∀ φ : InvFun ℤ, IsPolFan id g φ →
      ∃ (d : ℕ) (J : Z.IdealSheafData) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) (BD : EffCartierData S),
        1 ≤ d ∧ (∀ x ∈ J.support, x ∉ Set.range i) ∧ ValOn F i φ J d ∧ IsNormBl π J ∧ IsProjOver (π ≫ z) ∧
        IsOpenImmersion j ∧ Dense (Set.range j) ∧ j ≫ π = i ∧ π ⁻¹' Set.range i = Set.range j ∧
        BD.idealSheaf = J.comap π ∧ ValOn F j φ BD.idealSheaf d ∧
        ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → IsAmpleLB (CechPic.tens (lbPow (OZ.pull π) k) (CechPic.dual BD.lb))

end GlobalTheory.Poinc
