import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TwoNeZeroClosure
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CechPic GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.AV.LTors GlobalTheory.PDivGroup GlobalTheory.Dieu
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IsogParam

def zpW (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] : ℤ_[p] →+* WittVector p k :=
  (WittVector.map (ZMod.castHom (dvd_refl p) k)).comp (WittVector.equiv p).symm.toRingHom

abbrev eh {k : Type} [Field k] {A : AbVar k} (x : End A) : A.X ⟶ A.X := Hom.hom (A := A) (B := A) x

def oactOf {k : Type} [Field k] {C : Type} [CommRing C] (A : AbVar k) (φ : C →+* End A) : OAct C A.X where
  act c := eh (φ c)
  hom c := inferInstance
  one := by rw [map_one]; rfl
  mul a b := by rw [mul_comm, map_mul]; rfl
  add a b := by rw [map_add]; rfl

structure Pt (p : ℕ) {k : Type} [Field k] {O : Type} [Ring O] (star : O ≃+* Oᵐᵒᵖ) (A₀ : AbVar k)
    (ι₀ : O →+* End A₀) (c₀ : Pic A₀.X.left) where

  A : AbVar k

  act : O →+* End A

  c : Pic A.X.left
  ample : IsAmpleCls c
  rosati : ∀ b : O, IsAdj (A := A) (B := A) c c (act b) 1 (act (star b).unop)
  primeToP : ∃ e : ℕ, e.Coprime p ∧ ∀ (Y : Over (Sp k)) (x : Y ⟶ A.X),
    AbVar.lam c (fst Y A.X ≫ x) (snd Y A.X) = 0 → x ^ e = 1

  f : A₀ ⟶ A

  N : ℕ
  N_pos : 0 < N
  isog : IsIsogeny f
  lin : ∀ b : O, ι₀ b ≫ f = f ≫ act b

  den : ℕ

  num : ℕ
  den_pos : 0 < den
  num_pos : 0 < num
  pol : den • AbVar.lam c (fst A₀.X A₀.X ≫ f.hom) (snd A₀.X A₀.X ≫ f.hom) = num • AbVar.lam c₀ (fst A₀.X A₀.X) (snd A₀.X A₀.X)

section

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k]

variable {O : Type} [Ring O] {star : O ≃+* Oᵐᵒᵖ} {A₀ : AbVar k} {ι₀ : O →+* End A₀} {c₀ : Pic A₀.X.left}

def Pt.mOf (P : Pt p star A₀ ι₀ c₀) : ℤ := padicValRat p ((P.num : ℚ) / (P.den * P.N ^ 2))

def latl (P : Pt p star A₀ ι₀ c₀) (l : ℕ) [Fact l.Prime] : Submodule ℤ_[l] (Vl l A₀) :=
  Submodule.comap ((vmap l P.f).restrictScalars ℤ_[l]) (LinearMap.range ((P.N : ℤ_[l]) • tv l P.A))

variable (p) in

def IsPrimeToPLat (ι₀ : O →+* End A₀) (L : ∀ (l : ℕ) [Fact l.Prime], Submodule ℤ_[l] (Vl l A₀)) : Prop :=
  (∀ (l : ℕ) [Fact l.Prime], l ≠ p → (L l).FG ∧ Submodule.span ℚ_[l] (L l : Set (Vl l A₀)) = ⊤ ∧
      ∀ (b : O), ∀ x ∈ L l, vmap l (ι₀ b) x ∈ L l) ∧
    Set.Finite {l : ℕ | ∃ h : l.Prime, haveI := Fact.mk h; L l ≠ LinearMap.range (tv l A₀)}

variable [CharP k p] [PerfectRing k p]

abbrev VM (T : Theory p) (G : PDivGroup p k) : Type :=
  FractionRing (WittVector p k) ⊗[WittVector p k] T.M G

def incl (T : Theory p) (G : PDivGroup p k) : T.M G →ₗ[WittVector p k] VM T G :=
  TensorProduct.mk (WittVector p k) (FractionRing (WittVector p k)) (T.M G) 1

def latp (T : Theory p) {G₀ : PDivGroup p k} (t₀ : G₀.TorsionTower A₀.X) (P : Pt p star A₀ ι₀ c₀)
    {G : PDivGroup p k} (t : G.TorsionTower P.A.X) : Submodule (WittVector p k) (VM T G₀) :=
  Submodule.comap ((P.N : WittVector p k) • LinearMap.id)
    (Submodule.map (incl T G₀) (LinearMap.range (T.map (t₀.map t P.f.hom))))

def halfV (T : Theory p) {G₀ : PDivGroup p k} (t₀ : G₀.TorsionTower A₀.X) (ω : End A₀) (ρ : ℤ_[p]) :
    Submodule (WittVector p k) (VM T G₀) :=
  (LinearMap.ker ((T.map (t₀.map t₀ (eh ω))).baseChange (FractionRing (WittVector p k)) -
    algebraMap (WittVector p k) (FractionRing (WittVector p k)) (zpW p k ρ) • LinearMap.id)).restrictScalars
      (WittVector p k)

def latu (T : Theory p) {G₀ : PDivGroup p k} (t₀ : G₀.TorsionTower A₀.X) (P : Pt p star A₀ ι₀ c₀)
    {G : PDivGroup p k} (t : G.TorsionTower P.A.X) (ω : End A₀) (ρ : ℤ_[p]) : Submodule (WittVector p k) (VM T G₀) :=
  latp T t₀ P t ⊓ halfV T t₀ ω ρ

def IsHalfLat (T : Theory p) {G₀ : PDivGroup p k} (t₀ : G₀.TorsionTower A₀.X) (ι₀ : O →+* End A₀) (ω : End A₀)
    (ρ : ℤ_[p]) (L : Submodule (WittVector p k) (VM T G₀)) : Prop :=
  ∃ (n : ℕ) (L' : Submodule (WittVector p k) (T.M G₀)),
    (∀ x, x ∈ L ↔ ((p : FractionRing (WittVector p k)) ^ n) • x ∈ L'.map (incl T G₀)) ∧
    (∀ m ∈ L', T.map (t₀.map t₀ (eh ω)) m = zpW p k ρ • m) ∧
    (∃ j : ℕ, ∀ m, T.map (t₀.map t₀ (eh ω)) m = zpW p k ρ • m → p ^ j • m ∈ L') ∧
    (∀ m ∈ L', T.F G₀ m ∈ L') ∧ (∀ m ∈ L', T.V G₀ m ∈ L') ∧
    ∀ (b : O), ∀ m ∈ L', T.map (t₀.map t₀ (eh (ι₀ b))) m ∈ L'

def lieDim (T : Theory p) {C : Type} [CommRing C] {A : AbVar k} {G : PDivGroup p k} (t : G.TorsionTower A.X)
    (φ : C →+* End A) (ω : C) (ρ : ℤ_[p]) (τ : C →+* k) : ℕ∞ :=
  let Mρ : Submodule (WittVector p k) (T.M G) :=
    LinearMap.ker (T.map (t.map t (eh (φ ω))) - zpW p k ρ • LinearMap.id)
  let VM : Submodule (WittVector p k) (T.M G) := Submodule.span (WittVector p k) (T.V G '' Mρ)
  let N : Submodule (WittVector p k) (T.M G) :=
    Submodule.span (WittVector p k) ((fun x => (p : WittVector p k) • x) '' Mρ) ⊔
      Submodule.span (WittVector p k)
        {y | ∃ x ∈ VM, ∃ c, y = T.map (t.map t (eh (φ c))) x - WittVector.teichmuller p (τ c) • x}
  Module.length (WittVector p k) (VM ⧸ N.comap VM.subtype)

end

def St : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [PerfectRing k p]
    (O : Type) [Ring O] (star : O ≃+* Oᵐᵒᵖ), (∀ x, (star (star x).unop).unop = x) →
    ∀ (C : Type) [CommRing C] [Algebra C O] (ω : C) (tr nm : ℤ),
    algebraMap C O ω + (star (algebraMap C O ω)).unop = tr →
    algebraMap C O ω * (star (algebraMap C O ω)).unop = nm →
    ¬ (p : ℤ) ∣ tr ^ 2 - 4 * nm → ∀ ρ : ℤ_[p], ρ ^ 2 - tr * ρ + nm = 0 →
    ∀ (A₀ : AbVar k) (ι₀ : O →+* End A₀) (c₀ : Pic A₀.X.left), 0 < A₀.dim → IsAmpleCls c₀ →
    (∀ b, IsAdj (A := A₀) (B := A₀) c₀ c₀ (ι₀ b) 1 (ι₀ (star b).unop)) →
    ∀ (G₀ : PDivGroup p k) (t₀ : G₀.TorsionTower A₀.X),
      (∀ P : Pt p star A₀ ι₀ c₀, IsPrimeToPLat p ι₀ (fun l _ => latl P l) ∧
        ∀ (G : PDivGroup p k) (t : G.TorsionTower P.A.X),
          IsHalfLat T t₀ ι₀ (ι₀ (algebraMap C O ω)) ρ (latu T t₀ P t (ι₀ (algebraMap C O ω)) ρ)) ∧
      (∀ (L : ∀ (l : ℕ) [Fact l.Prime], Submodule ℤ_[l] (Vl l A₀)) (Lu : Submodule (WittVector p k) (VM T G₀))
          (m : ℤ), IsPrimeToPLat p ι₀ L → IsHalfLat T t₀ ι₀ (ι₀ (algebraMap C O ω)) ρ Lu →
        ∃ P : Pt p star A₀ ι₀ c₀, (∀ (l : ℕ) [Fact l.Prime], l ≠ p → latl P l = L l) ∧
          (∃ (G : PDivGroup p k) (t : G.TorsionTower P.A.X), latu T t₀ P t (ι₀ (algebraMap C O ω)) ρ = Lu) ∧
          P.mOf = m) ∧
      (∀ P P' : Pt p star A₀ ι₀ c₀, (∀ (l : ℕ) [Fact l.Prime], l ≠ p → latl P l = latl P' l) →
        (∃ (G : PDivGroup p k) (t : G.TorsionTower P.A.X) (G' : PDivGroup p k) (t' : G'.TorsionTower P'.A.X),
          latu T t₀ P t (ι₀ (algebraMap C O ω)) ρ = latu T t₀ P' t' (ι₀ (algebraMap C O ω)) ρ) →
        P.mOf = P'.mOf →
        ∃ e : P.A ≅ P'.A, P'.N • (P.f ≫ e.hom) = P.N • P'.f ∧ (∀ b, P.act b ≫ e.hom = e.hom ≫ P'.act b) ∧
          ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a.Coprime p ∧ b.Coprime p ∧
            a • AbVar.lam P'.c (fst P.A.X P.A.X ≫ e.hom.hom) (snd P.A.X P.A.X ≫ e.hom.hom) =
              b • AbVar.lam P.c (fst P.A.X P.A.X) (snd P.A.X P.A.X)) ∧
      (∀ (P P' : Pt p star A₀ ι₀ c₀) (e : P.A ≅ P'.A), P'.N • (P.f ≫ e.hom) = P.N • P'.f →
        (∀ b, P.act b ≫ e.hom = e.hom ≫ P'.act b) →
        (∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a.Coprime p ∧ b.Coprime p ∧
            a • AbVar.lam P'.c (fst P.A.X P.A.X ≫ e.hom.hom) (snd P.A.X P.A.X ≫ e.hom.hom) =
              b • AbVar.lam P.c (fst P.A.X P.A.X) (snd P.A.X P.A.X)) →
        (∀ (l : ℕ) [Fact l.Prime], l ≠ p → latl P l = latl P' l) ∧
        (∀ (G : PDivGroup p k) (t : G.TorsionTower P.A.X) (G' : PDivGroup p k) (t' : G'.TorsionTower P'.A.X),
          latu T t₀ P t (ι₀ (algebraMap C O ω)) ρ = latu T t₀ P' t' (ι₀ (algebraMap C O ω)) ρ) ∧
        P.mOf = P'.mOf) ∧
      ∀ (A : AbVar k) (act : O →+* End A) (G : PDivGroup p k) (t : G.TorsionTower A.X) (τ : C →+* k),
        τ ω = WittVector.constantCoeff (zpW p k ρ) → ∀ n : ℕ,
          (LieMult (oactOf A (act.comp (algebraMap C O))) (𝟙 (Sp k)) τ n ↔
            lieDim T t (act.comp (algebraMap C O)) ω ρ τ = n)

end GlobalTheory.IsogParam
