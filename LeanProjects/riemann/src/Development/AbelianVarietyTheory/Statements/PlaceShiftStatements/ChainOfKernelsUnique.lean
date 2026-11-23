import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CompEqOneIffPush
import Development.AbelianVarietyTheory.Definitions.Divisors.Subsingleton

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IwLevel

def QuotGlobal : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] (H : Over S) [GrpObj H] (i : H ⟶ A),
    IsAbelianScheme A → IsMonHom i → Mono i → IsFinite H.hom → Flat H.hom →
    ∃ (B : Over S) (_ : GrpObj B) (q : A ⟶ B), IsAbelianScheme B ∧ IsMonHom q ∧ IsFinite q.left ∧
      Flat q.left ∧ Surjective q.left ∧ IsPullback ((fst H A ≫ i) * snd H A) (snd H A) q q

def IsStable {S : Scheme.{0}} {O : Type} [Ring O] {A K : Over S} [GrpObj A] (ρ : RingAct A O) (i : K ⟶ A) : Prop :=
  ∀ a : O, ∃ g : K ⟶ K, g ≫ i = i ≫ ρ.act a

def InSub {S : Scheme.{0}} {A K T : Over S} (i : K ⟶ A) (x : T ⟶ A) : Prop :=
  ∃ y : T ⟶ K, y ≫ i = x

def ChainOfKernels : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (O : Type) [Ring O] (A : Over S) [GrpObj A] [IsCommMonObj A]
    (ρ : RingAct A O) (𝔴 : Ideal O) (d n : ℕ) (K : Fin (n + 1) → Over S) (_ : ∀ j, GrpObj (K j))
    (i : ∀ j, K j ⟶ A), IsAbelianScheme A → (∀ j, IsMonHom (i j)) → (∀ j, Mono (i j)) →
    (∀ j, IsIsogDeg (toUnit (K j)) (d ^ (j : ℕ))) → (∀ j, IsStable ρ (i j)) →
    (∀ (j : Fin n) (T : Over S) (x : T ⟶ A), InSub (i j.castSucc) x → InSub (i j.succ) x) →
    (∀ (T : Over S) (x : T ⟶ A), InSub (i (Fin.last n)) x ↔ KilledBy ρ 𝔴 x) →
    ∃ C : Chain ρ 𝔴 d n, ∀ (j : Fin (n + 1)) (T : Over S) (x : T ⟶ A), x ≫ C.π j = 1 ↔ InSub (i j) x

def ChainOfKernelsUnique : Prop :=
  ∀ (S : Scheme.{0}) (O : Type) [Ring O] (A : Over S) [GrpObj A] [IsCommMonObj A] (ρ : RingAct A O)
    (𝔴 : Ideal O) (d n : ℕ) (C C' : Chain ρ 𝔴 d n),
    (∀ (j : Fin (n + 1)) (T : Over S) (x : T ⟶ A), x ≫ C.π j = 1 ↔ x ≫ C'.π j = 1) →
    Nonempty (ChainMap C' C (𝟙 S) (𝟙 A.left))

def KernelsOfChain : Prop :=
  ∀ (S : Scheme.{0}) (O : Type) [Ring O] (A : Over S) [GrpObj A] [IsCommMonObj A] (ρ : RingAct A O)
    (𝔴 : Ideal O) (d n : ℕ) (C : Chain ρ 𝔴 d n) (j : Fin (n + 1)),
    ∃ (K : Over S) (_ : GrpObj K) (i : K ⟶ A), IsMonHom i ∧ Mono i ∧ IsIsogDeg (toUnit K) (d ^ (j : ℕ)) ∧
      IsStable ρ i ∧ ∀ (T : Over S) (x : T ⟶ A), x ≫ C.π j = 1 ↔ InSub i x

def ChainFunctorRep : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (O : Type) [Ring O] (A : Over S) [GrpObj A] [IsCommMonObj A]
    (ρ : RingAct A O) (𝔴 : Ideal O) (d n : ℕ) (K : Over S) (_ : GrpObj K) (i : K ⟶ A), IsAbelianScheme A →
    IsMonHom i → Mono i → IsIsogDeg (toUnit K) (d ^ n) →
    (∀ (T : Over S) (x : T ⟶ A), InSub i x ↔ KilledBy ρ 𝔴 x) →
    ∃ (Y : Scheme.{0}) (g : Y ⟶ S) (C : Chain (actPull ρ g) 𝔴 d n), IsProper g ∧
      ∀ (T : Scheme.{0}) (t : T ⟶ S) (C' : Chain (actPull ρ t) 𝔴 d n),
        ∃! f : T ⟶ Y, f ≫ g = t ∧ ∃ u : ((Over.pullback t).obj A).left ⟶ ((Over.pullback g).obj A).left,
          u ≫ pullback.fst A.hom g = pullback.fst A.hom t ∧ Nonempty (ChainMap C' C f u)

end GlobalTheory.IwLevel
