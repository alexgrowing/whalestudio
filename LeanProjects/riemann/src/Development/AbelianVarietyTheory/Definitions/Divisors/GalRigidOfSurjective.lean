import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOfPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

def HasRoot {S T : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left) (f : T ⟶ S) : Prop :=
  ∃ (A' : Over T) (_ : GrpObj A') (_ : IsCommMonObj A') (β : A'.left ⟶ A.left) (β₂ : (G2 A').left ⟶ (G2 A).left)
    (L : LB A'.left), IsGrpPullback A' A f β ∧ IsSquare β β₂ ∧ L.IsLB ∧ LBIso (abelian₂ A' L) (P.pull β₂)

def IsBiRig {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left) : Prop :=
  P.IsLB ∧ (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) ∧ LBIso P (P.pull (lift (snd A A) (fst A A)).left)

def IsPPol {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left) : Prop :=
  IsBiRig A P ∧ RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) ∧
    ∀ (T : Over S) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1

theorem isPPol_of_principal {S : Scheme.{0}} {h M : ℕ} {B : Type} [CommRing B] {ζ : B} {s : S ⟶ Sp B} (c : SiegPre h M ζ s)
    (hc : c.Principal) : IsPPol c.A c.P := ⟨⟨c.isLB, c.rig₁, c.rig₂, c.symm⟩, hc.1, hc.2⟩

def IsComplAt {A R : Type} [CommRing A] [CommRing R] [IsLocalRing R] (ψ : A →+* R) : Prop :=
  IsNoetherianRing R ∧ IsAdicComplete (maximalIdeal R) R ∧ ψ.Flat ∧ ((maximalIdeal R).comap ψ).map ψ = maximalIdeal R ∧
    ∀ r : R, ∃ a b : A, IsUnit (ψ b) ∧ r * ψ b - ψ a ∈ maximalIdeal R

theorem isComplAt_id (K : Type) [Field K] : IsComplAt (RingHom.id K) :=
  ⟨inferInstance, inferInstance, RingHom.Flat.id K, by rw [Ideal.comap_id, Ideal.map_id],
    fun r => ⟨r, 1, isUnit_one, by simp⟩⟩

section From

variable {o W V : Type} [CommRing o] [CommRing W] [IsLocalRing W] [CommRing V] [IsDomain V] (T : TautBase o W) (iw : W →+* V)
  {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ)

def DataFrom (Q : Data V) (e : Q.X ≃+ (Fin T.r → ℤ)) : Prop :=
  ∃ (β : Q.B.left ⟶ T.B.left) (β₂ : (G2 Q.B).left ⟶ (G2 T.B).left)
    (w : LB.Iso (abelian₂ Q.B Q.M.L) ((abelian₂ T.B T.M.L).pull β₂)),
    IsGrpPullback Q.B T.B (spMap iw) β ∧ IsSquare β β₂ ∧ w.IsGen ∧
    (∀ a, (Q.c a).left ≫ β = spMap iw ≫ (T.c₀ ((n : ℤ) • e a)).left) ∧
    ∀ a b, ∃ k : (FractionRing V)ˣ,
      (k : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ((n : ℤ) * ε i (e a) (e b)) ∧
      ∀ z J J', Good T.M.L z J → Good Q.M.L z J' →
        val (Q.tau a b) (𝟙 _) z J' = gm (𝟙 (TK V).left) z ⊤ (unitOn k) *
          (lamVal w (lift (toUnit (TK V) ≫ Q.c a) (toUnit (TK V) ≫ Q.c b)).left z J J' *
            val (T.τ₀ ((n : ℤ) • e a) ((n : ℤ) • e b)) ((TK V).hom ≫ spMap iw) z J)

def DegFrom (D : DegPre V) (e : D.X ≃+ (Fin T.r → ℤ)) : Prop :=
  ∃ (Q : Data V) (e' : D.X ≃+ Q.X), Refines Q (RingHom.id V) D e' ∧ DataFrom T iw s ε n Q (e'.symm.trans e)

end From

structure LowBase {o : Type} [CommRing o] (ζ : o) (n : ℕ) where

  h : ℕ

  F : SFam h n ζ

  W : Type
  [ring : CommRing W]
  [loc : IsLocalRing W]
  noeth : IsNoetherianRing W
  complete : IsAdicComplete (maximalIdeal W) W

  T : TautBase o W

  u : Sp W ⟶ (LowChart.powA F T.r).left
  u_et : IsEtaleCompletion (Scheme.stalkClosedPointTo u).hom
  u_sep : ((residue W).comp (Scheme.stalkClosedPointTo u).hom).FormallyUnramified
  u_base : u ≫ LowChart.toO F T.r = spMap T.b
  dim : T.g = h

  β : T.B.left ⟶ F.univ.A.left

  β₂ : (G2 T.B).left ⟶ (G2 F.univ.A).left
  cart : IsGrpPullback T.B F.univ.A (u ≫ (LowChart.powA F T.r).hom) β
  sq : IsSquare β β₂
  lb : LBIso (abelian₂ T.B T.M.L) (F.univ.P.pull β₂)
  coord : ∀ i, (T.c₀ (Pi.single i 1)).left ≫ β = u ≫ (LowChart.coord F i).left

attribute [instance] LowBase.ring LowBase.loc

structure Taut {o : Type} [CommRing o] (ζ : o) (g n : ℕ) (φ : InvFun ℤ) extends LowBase ζ n where
  genus : h + T.r = g

  m : ℕ

  N : ℕ

  ε : Module.Basis (Fin m ⊕ Fin N) ℤ (balForms (id : ℤ → ℤ) (Fin T.r → ℤ))
  cone : IsCone id φ fun k => (ε (.inl k) : LinearMap.BilinForm ℤ (Fin T.r → ℤ))
  defin : ∀ x, x ≠ 0 → ∃ k, 0 < (ε (.inl k) : LinearMap.BilinForm ℤ (Fin T.r → ℤ)) x x

  R : Type
  [ringR : CommRing R]
  [domR : IsDomain R]
  [locR : IsLocalRing R]

  ψ : MvPolynomial (Fin m ⊕ Fin N) W →+* R
  compl : IsComplAt ψ
  ψ_loc : IsLocalHom (ψ.comp MvPolynomial.C)
  bd : ∀ k, ψ (MvPolynomial.X (.inl k)) ∈ maximalIdeal R
  tor : ∀ k, IsUnit (ψ (MvPolynomial.X (.inr k)))

  Q : Data R

  e : Q.X ≃+ (Fin T.r → ℤ)
  data : DataFrom T (ψ.comp MvPolynomial.C) (fun k => ψ (MvPolynomial.X k))
    (fun k => (ε k : LinearMap.BilinForm ℤ (Fin T.r → ℤ))) n Q e

attribute [instance] Taut.ringR Taut.domR Taut.locR

namespace Taut

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {φ : InvFun ℤ} (C : Taut ζ g n φ)

def iw : C.W →+* C.R := C.ψ.comp MvPolynomial.C

def b : o →+* C.R := C.iw.comp C.T.b

def s (k : Fin C.m ⊕ Fin C.N) : C.R := C.ψ (MvPolynomial.X k)

def t (k : Fin C.m) : C.R := C.s (.inl k)

def form (k : Fin C.m ⊕ Fin C.N) : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ) := C.ε k

def δ (k : Fin C.m) : LinearMap.BilinForm ℤ C.Q.X := pull C.e.toIntLinearEquiv.toLinearMap (C.form (.inl k))

def IsFam (F : SFam g n ζ) (G₁ : Over (Sp C.R)) [GrpObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X)
    (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) : Prop :=
  IsSemiAbelian G₁ ∧ (∀ p : Sp C.R, p ∈ abLocus G₁ ↔ ∏ k, C.t k ∉ p.asIdeal) ∧ IsGenFibre F y α₁ ∧
    IsMumfordFam F y α₁ C.Q ∧ y ≫ F.s = jK C.R ≫ spMap C.b

end Taut

def IsMumPol {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁]
    (P : LB (G2 G₁).left) : Prop :=
  IsCN R ∧ Q.IsPos (maximalIdeal R) ∧ IsSemiAbelian G₁ ∧ IsBiRig G₁ P ∧
  ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), IsCN R' → Function.Injective ρ → ρ.Finite →
    ∀ (D : DegData R' (maximalIdeal R')) (ε : D.toPre.X ≃+ Q.X), Refines Q ρ D.toPre ε →
      ∃ (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G₁.left) (π₂ : (G2 G').left ⟶ (G2 G₁).left)
        (A : PolAV (Sp (FractionRing R'))) (U : Unif (maximalIdeal R') D A G'),
        IsGrpPullback G' G₁ (spMap ρ) π ∧ IsSquare π π₂ ∧ LBIso (abelian₂ G' U.LG.L) (P.pull π₂)

def SameFib {S S' T : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left) (f : T ⟶ S)
    (A' : Over S') [GrpObj A'] [IsCommMonObj A'] (P' : LB (G2 A').left) (f' : T ⟶ S') : Prop :=
  ∃ (H : Over T) (_ : GrpObj H) (_ : IsCommMonObj H) (a : H.left ⟶ A.left) (a₂ : (G2 H).left ⟶ (G2 A).left)
    (a' : H.left ⟶ A'.left) (a₂' : (G2 H).left ⟶ (G2 A').left),
    IsGrpPullback H A f a ∧ IsSquare a a₂ ∧ IsGrpPullback H A' f' a' ∧ IsSquare a' a₂' ∧ LBIso (P.pull a₂) (P'.pull a₂')

def TorsRat {R : Type} [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] (n : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (κ : FractionRing R →+* K) (x : Over.mk (spMap κ ≫ jK R) ⟶ G), x ^ n = 1 →
    ∃ x₀ : Over.mk (jK R) ⟶ G, x.left = spMap κ ≫ x₀.left

theorem torsRat_one {R : Type} [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] : TorsRat G 1 := fun K _ _ κ x hx =>
  ⟨1, by
    rw [pow_one] at hx
    let ρ : Over.mk (spMap κ ≫ jK R) ⟶ Over.mk (jK R) := Over.homMk (spMap κ) rfl
    rw [hx, ← MonObj.comp_one ρ]
    rfl⟩

def GalRigid {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) : Prop :=
  ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (θ : R →+* R') (σ : R' ≃+* R'), IsCN R' → Function.Injective θ →
    θ.Finite → IsOfFinOrder σ → (∀ a, σ (θ (f a)) = θ (f a)) → (∀ r, σ (θ r) - θ r ∈ maximalIdeal R') → ∀ r, σ (θ r) = θ r

theorem galRigid_of_surjective {A R : Type} [CommRing A] [CommRing R] {f : A →+* R} (hf : Function.Surjective f) : GalRigid f :=
  fun _ _ _ _ _ _ _ _ _ _ h _ r => by
    obtain ⟨a, rfl⟩ := hf r
    exact h a

end GlobalTheory.TChart
