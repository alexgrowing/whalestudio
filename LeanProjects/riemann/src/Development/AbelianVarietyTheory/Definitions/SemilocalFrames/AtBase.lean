import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

namespace GlobalTheory.LocOver

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def Uni {K : Type} [Zero K] [One K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : Prop :=
  (∀ a b, b < a → A a b = 0) ∧ ∀ a, A a a = 1

def Chg {K W : Type} [Semiring K] [AddCommMonoid W] [Module K W] {n : ℕ} (f : Fin n → W)
    (A : Matrix (Fin n) (Fin n) K) (g : Fin n → W) : Prop :=
  ∀ b, g b = ∑ a, A a b • f a

def Tri (K : Type) {W : Type} [Semiring K] [AddCommMonoid W] [Module K W] {n : ℕ} (f g : Fin n → W) : Prop :=
  ∃ A : Matrix (Fin n) (Fin n) K, Uni A ∧ Chg f A g

section Loc

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {r : ℕ}

def move (g : V ≃ₗ[E] V) (t : Term V M r) : Term V M r where
  abelian₂ := img g t.abelian₂
  f b := g (t.f b)
  f' b := g (t.f' b)
  T := t.T
  T' := t.T'

def Over {H : HermSp M V} (P : FPair H r) (d : Datum P) (t : Term V M r) : Prop :=
  ∃ g : V ≃ₗ[E] V, IsUnitary H g ∧ ∃ d' : Datum P, Datum.Rel d d' ∧ IsTermOver P d' (move g t)

def NU (H : HermSp M V) (f : Fin (r + 1) → V) : Set (V ≃ₗ[E] V) :=
  {n | IsUnitary H n ∧
    (∀ a : Fin r, n (f a.castSucc) - f a.castSucc ∈
      Submodule.span E ((fun b : Fin r => f b.castSucc) '' {b | b < a})) ∧
    ∀ v ∈ H.perp (H.X f), n v - v ∈ H.X f}

def Cong (H : HermSp M V) (Λ : Submodule M.L.O V) (f f' : Fin (r + 1) → V) (x : V) : Prop :=
  ∃ a ∈ H.smulLat (algebraMap F E (theta M)) Λ, ∃ b ∈ Λ, ∃ c ∈ Λ, b ∈ H.X f ∧ c ∈ H.X f' ∧ x = a + b + c

end Loc

section Glob

variable {D : D7}

def scaled (Z : LocDat D) (p : PlF D) (f : Fin (D.R.rS + 1) → (VS D).V) : Fin (D.R.rS + 1) → Vp D p :=
  fun a => frFac Z.δ p a • baseChange₂ D p (f a)

def locU (Z : LocDat D) (p : PlF D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}
    (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (Tn T'n : ℕ) : Loc.Term (Vp D p) (Z.M p) D.R.rS where
  abelian₂ := lattice₂ D Z.M p Λ
  f a := frFac Z.δ p a • baseChange₂ D p (frame F a)
  f' b := frFac Z.δ p b • baseChange₂ D p (frameAct (frame F') (admXi D Λ F F')⁻¹ b)
  T := (Tn : (D.s.atP p).Fp)
  T' := (T'n : (D.s.atP p).Fp)

def AtBase (Z : LocDat D) (p : PlF D) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')
    (Tn T'n : ℕ) (P : LocNG.FPair (locH Z p) D.R.rS) : Prop :=
  P.A.f = scaled Z p (frame F) ∧ P.B.f = scaled Z p (frame F') ∧
    P.A.T = (Tn : (D.s.atP p).Fp) ∧ P.B.T = (T'n : (D.s.atP p).Fp)

def Ext (p : PlF D) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) : Prop :=
  ∀ x, g (baseChange₂ D p x) = baseChange₂ D p (γ x)

end Glob

end GlobalTheory.LocOver
