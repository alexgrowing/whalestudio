import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field

namespace UpperTheory.Gal.crystallineComparison.Mod

def WModEx : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (w : Ideal (𝓞 D.F)) (T : Over S), Nonempty (WMod o w T)

def ObjTri : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S₁ S₂ S₃ : Scheme.{0}) (s₁ : S₁ ⟶ Sp R) (s₂ : S₂ ⟶ Sp R) (s₃ : S₃ ⟶ Sp R)
    (o₁ : Obj b N s₁) (o₂ : Obj b N s₂) (o₃ : Obj b N s₃) (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃),
    (∀ m m' : ObjMap o₁ o₂ f, m.φ = m'.φ) ∧
    ∀ (fg : S₁ ⟶ S₃), f ≫ g = fg → ∀ (m₁₃ : ObjMap o₁ o₃ fg) (m₂₃ : ObjMap o₂ o₃ g), ∃ m₁₂ : ObjMap o₁ o₂ f, m₁₂.φ ≫ m₂₃.φ = m₁₃.φ

def PullIsog : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (f : S' ⟶ S), f ≫ s = s' →
    ∀ (c : ℕ) (o o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ → ∀ (o₁ : Obj b N s') (m : ObjMap o₁ o f),
    ∃ (o₁' : Obj b N s') (m' : ObjMap o₁' o' f) (ψ₁ : o₁.A ⟶ o₁'.A), IsPIsog c o₁ o₁' ψ₁ ∧ m.φ ≫ ψ.left = ψ₁.left ≫ m'.φ

def PullKer : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (f : S' ⟶ S) (o o' : Obj b N s) (o₁ o₁' : Obj b N s')
    (m : ObjMap o₁ o f) (m' : ObjMap o₁' o' f) (ψ : o.A ⟶ o'.A) (ψ₁ : o₁.A ⟶ o₁'.A), m.φ ≫ ψ.left = ψ₁.left ≫ m'.φ →
    (∀ (T : Over S') (T₀ : Over S) (h : T₀.left = T.left) (g : T ⟶ o₁.A) (g₀ : T₀ ⟶ o.A), g₀.left = eqToHom h ≫ g.left ≫ m.φ →
      (g ≫ ψ₁ = 1 ↔ g₀ ≫ ψ = 1) ∧ (g = 1 ↔ g₀ = 1) ∧ ∀ I : Ideal (𝓞 D.F), KilledBy o₁ I g ↔ KilledBy o I g₀) ∧
    ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j : ℕ), IsTj r w j o o' ψ → IsTj r w j o₁ o₁' ψ₁

def PulledEx : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (M : Model b N) (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ) (T : TjD M r w j c)
    (S : Scheme.{0}) (x : S ⟶ M.X) (σ : S ⟶ Sp R), x ≫ M.s = σ → ∀ (o₁ : Obj b N σ) (m₁ : ObjMap o₁ M.univ x) (y : S ⟶ T.Y),
    y ≫ T.s = x → Nonempty (Pulled T m₁ y)

def KerU : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)), w ≠ ⊤ → uIdeal D r ≤ w → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S]
    (s : S ⟶ Sp R) (o o' : Obj b N s) (ψ : o.A ⟶ o'.A) (ψ' : o'.A ⟶ o.A) (e : ℕ), IsMonHom ψ → IsMonHom ψ' →
    (∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ o'.act.act a) → ψ ≫ ψ' = (𝟙 o.A) ^ p ^ e → ψ' ≫ ψ = (𝟙 o'.A) ^ p ^ e →
    RepFF o.A (UKer r o ψ) ∧ IsSub o.A (UKer r o ψ) ∧ ∀ T g, UKer r o ψ T g → g ^ p ^ e = 1

def UElt : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (r : ℤ) (w : Ideal (𝓞 D.F)), w ≠ ⊤ → uIdeal D r ≤ w → ∀ e : ℕ,
    ∃ α : 𝓞 D.F, (∀ a ∈ uIdeal D r ^ e, a * α ∈ Ideal.span {(p : 𝓞 D.F) ^ e}) ∧ α + D.bar α - 1 ∈ Ideal.span {(p : 𝓞 D.F) ^ e} ∧
      D.bar α ∈ uIdeal D r ^ e

def TanOne : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), D.m = 1 → D.a = 1 → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)), uIdeal D r ≤ w →
    ∀ (κ : Type) [Field κ] [IsAlgClosed κ] [CharP κ p] (β : R →+* κ), (∀ i, ∀ x ∈ w, β (b.t i x) = 0) →
    ∀ (o : Obj b N (spMap β)) (e : ℕ), TanLe o.A (UKer r o ((𝟙 o.A) ^ p ^ (e + 1)))

def Adjoint : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (k : Type) [Field k] (s : Sp k ⟶ Sp R) (c : ℕ) (o o' : Obj b N s) (ψ : o.A ⟶ o'.A) (ψ' : o'.A ⟶ o.A),
    IsPIsog c o o' ψ → IsMonHom ψ' → ψ' ≫ ψ = (𝟙 o'.A) ^ c → ∀ (T : Over (Sp k)) (x : T ⟶ o.A) (y : T ⟶ o'.A),
    evc o'.isLB (x ≫ ψ) y = evc o.isLB x (y ≫ ψ') ∧ evc o'.isLB y (x ≫ ψ) = evc o.isLB (y ≫ ψ') x

def PairCalc : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s),
    IsAdditive (A := o.A) (T := o.A) o.P ∧ IsAdditive (swap (A := o.A) (B := o.A) o.P) ∧
    (∀ (T : Over S) (x y : T ⟶ o.A) (a : 𝓞 D.F), evc o.isLB (x ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) y =
      evc o.isLB x (y ≫ o.act.act (algebraMap (𝓞 D.F) D.O (D.bar a)))) ∧
    (∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ o.A), evc o.isLB (snd o.A T ≫ x) (fst o.A T) = 0 → x ^ e = 1) ∧
    ∀ (o' : Obj b N s) (ψ : o.A ⟶ o'.A) (c : ℕ), Nonempty (LBIso (Hecke.lbPow o.P c) (o'.P.pull (sq2 ψ))) ↔
      ∀ (T : Over S) (x y : T ⟶ o.A), evc o'.isLB (x ≫ ψ) (y ≫ ψ) = c • evc o.isLB x y

def KerFromU : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)), w ≠ ⊤ → uIdeal D r ≤ w → ∀ (k : Type) [Field k] (s : Sp k ⟶ Sp R) (c : ℕ)
    (o o₁ o₂ : Obj b N s) (ψ₁ : o.A ⟶ o₁.A) (ψ₂ : o.A ⟶ o₂.A), IsPIsog c o o₁ ψ₁ → IsPIsog c o o₂ ψ₂ →
    (∀ T g, UKer r o ψ₁ T g ↔ UKer r o ψ₂ T g) → ∀ (T : Over (Sp k)) (g : T ⟶ o.A), g ≫ ψ₁ = 1 → g ≫ ψ₂ = 1

def IsoOfKer : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (k : Type) [Field k] (s : Sp k ⟶ Sp R) (c : ℕ)
    (o o₁ o₂ : Obj b N s) (ψ₁ : o.A ⟶ o₁.A) (ψ₂ : o.A ⟶ o₂.A), IsPIsog c o o₁ ψ₁ → IsPIsog c o o₂ ψ₂ →
    (∀ (T : Over (Sp k)) (g : T ⟶ o.A), g ≫ ψ₁ = 1 ↔ g ≫ ψ₂ = 1) → ∃ m : ObjMap o₁ o₂ (𝟙 _), ψ₁.left ≫ m.φ = ψ₂.left

def IsogComp : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (c c' : ℕ) (o o₁ o₂ : Obj b N s) (ψ : o.A ⟶ o₁.A) (χ : o₁.A ⟶ o₂.A),
    IsPIsog c o o₁ ψ → IsPIsog c' o₁ o₂ χ → IsPIsog (c * c') o o₂ (ψ ≫ χ)

def QuasiInv : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (κ : Type) [Field κ] [IsAlgClosed κ] [CharP κ p] (s : Sp κ ⟶ Sp R) (c : ℕ), 0 < c →
    ∀ (o o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsMonHom ψ → IsFinite ψ.left → Surjective ψ.left →
    Nonempty (LBIso (Hecke.lbPow o.P c) (o'.P.pull (sq2 ψ))) →
    (∀ (K : Type) [Field K] [IsAlgClosed K] (z : Sp K ⟶ Sp κ) (g : Over.mk z ⟶ o.A), g ≫ ψ = 1 → g = 1) →
    ∃ ψ' : o'.A ⟶ o.A, IsMonHom ψ' ∧ ψ ≫ ψ' = (𝟙 o.A) ^ c ∧ ψ' ≫ ψ = (𝟙 o'.A) ^ c

def FrobIsog : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (f : ℕ) (κ : Type) [Field κ] [IsAlgClosed κ] [CharP κ p] (s : Sp κ ⟶ Sp R) (φ : κ →+* κ),
    (∀ a, φ a = a ^ p ^ f) → spMap φ ≫ s = s → ∀ o : Obj b N s, ∃ (o' : Obj b N s) (m : ObjMap o' o (spMap φ)) (F : o.A ⟶ o'.A),
      IsPIsog (p ^ f) o o' F ∧ (∀ a : 𝟙_ (Over (Sp κ)) ⟶ o.A, (a ≫ F).left ≫ m.φ = spMap φ ≫ a.left) ∧
      ∀ (T : Over (Sp κ)) (g : T ⟶ o.A), g ≫ F = 1 ↔ FrobKill p f Fact.out g

def SameE : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (r : ℤ) (κ : Type) [Field κ] [IsAlgClosed κ] (s : Sp κ ⟶ Sp R) (o o₁ o₂ : Obj b N s)
    (ψ₁ : o.A ⟶ o₁.A) (ψ₂ : o.A ⟶ o₂.A), IsMonHom ψ₂ → IsSub o.A (UKer r o ψ₁) → ∀ d : ℕ, RepAlg o.A (UKer r o ψ₁) d →
    Nat.card {g : 𝟙_ (Over (Sp κ)) ⟶ o.A // UKer r o ψ₁ _ g} = d → (∀ g : 𝟙_ (Over (Sp κ)) ⟶ o.A, UKer r o ψ₁ _ g → g ≫ ψ₂ = 1) →
    ∀ T g, UKer r o ψ₁ T g → UKer r o ψ₂ T g

def FrobPass : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (r : ℤ) (f : ℕ) (κ : Type) [Field κ] [IsAlgClosed κ] [CharP κ p] (s : Sp κ ⟶ Sp R) (o o' : Obj b N s)
    (ψ : o.A ⟶ o'.A), IsMonHom ψ → ∀ d : ℕ, RepAlg o.A (UKer r o ψ) d → Nat.card {g : 𝟙_ (Over (Sp κ)) ⟶ o.A // UKer r o ψ _ g} = d →
    (∀ g : 𝟙_ (Over (Sp κ)) ⟶ o'.A, FrobKill p f Fact.out g → g = 1) ∧
    ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra κ Λ] (ε : Λ →ₐ[κ] κ) (g : algPt κ Λ ⟶ o.A),
      (∃ e : ℕ, KilledBy o (uIdeal D r ^ e) g) → Inf ε g → (FrobKill p f Fact.out (g ≫ ψ) ↔ FrobKill p f Fact.out g)

def SameW : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), D.m = 1 → D.a = 1 → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)), w ≠ ⊤ → uIdeal D r ≤ w →
    ∀ (f : ℕ) (κ : Type) [Field κ] [IsAlgClosed κ] [CharP κ p] (β : R →+* κ), (∀ i, ∀ x ∈ w, β (b.t i x) = 0) →
    ∀ (o o₁ o₂ o₃ : Obj b N (spMap β)) (ψ₁ : o.A ⟶ o₁.A) (ψ₂ : o.A ⟶ o₂.A) (F : o₂.A ⟶ o₃.A) (e : ℕ),
    IsPIsog (p ^ (e + 1)) o o₁ ψ₁ → IsMonHom ψ₂ → IsPIsog (p ^ (e + 1)) o o₃ (ψ₂ ≫ F) →
    (∀ (T : Over (Sp κ)) (g : T ⟶ o₂.A), g ≫ F = 1 ↔ FrobKill p f Fact.out g) → ∀ d : ℕ, 0 < d →
    RepAlg o.A (UKer r o ψ₁) (p ^ f * d) → Nat.card {g : 𝟙_ (Over (Sp κ)) ⟶ o.A // UKer r o ψ₁ _ g} = d →
    RepAlg o.A (UKer r o ψ₂) d → Nat.card {g : 𝟙_ (Over (Sp κ)) ⟶ o.A // UKer r o ψ₂ _ g} = d →
    (∀ g : 𝟙_ (Over (Sp κ)) ⟶ o.A, UKer r o ψ₁ _ g ↔ UKer r o ψ₂ _ g) → ∀ T g, UKer r o ψ₁ T g ↔ UKer r o (ψ₂ ≫ F) T g

def OMod : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), D.m = 1 → ∀ x : D.O, ∃ (c : 𝓞 D.F) (y : D.O),
    x = algebraMap (𝓞 D.F) D.O c + algebraMap (𝓞 D.F) D.O (p : 𝓞 D.F) * y

def ImgEq : Prop := ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (M : Model b N) (S : Scheme.{0}) (s : S ⟶ Sp R) (o₁ o₂ : Obj b N s)
    (t₁ t₂ : S ⟶ M.X), t₁ ≫ M.s = s → t₂ ≫ M.s = s → ∀ (n₁ : ObjMap o₁ M.univ t₁) (n₂ : ObjMap o₂ M.univ t₂) (m : ObjMap o₁ o₂ (𝟙 S)),
    t₁ = t₂ ∧ m.φ ≫ n₂.φ = n₁.φ

end UpperTheory.Gal.crystallineComparison.Mod
