import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TruncQuotSymmTruncTensor

noncomputable section

open CategoryTheory

namespace GlobalTheory.MoritaHT

open GlobalTheory.VDiv GlobalTheory.VDefo

abbrev unitE (O : Type) [CommRing O] (n : ℕ) [NeZero n] : Matrix (Fin n) (Fin n) O :=
  Matrix.single 0 0 1

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {n : ℕ} [NeZero n]

section OneBase

variable {S : Type} [CommRing S] [Algebra O S]

def IsHTType [Algebra ℤ_[p] O] (G : PDivGroup p S) (ι : PDivGroup.Action (Matrix (Fin n) (Fin n) O) G) :
    Prop :=
  G.height = n * n * Module.finrank ℤ_[p] O ∧
    (∀ (a : O) (x : G.Lie), ι.onLie (Matrix.scalar (Fin n) a) x = algebraMap O S a • x) ∧
    Module.Finite S (LinearMap.range (ι.onLie (unitE O n))) ∧
    Module.Projective S (LinearMap.range (ι.onLie (unitE O n))) ∧
    ∀ q : PrimeSpectrum S, Module.rankAtStalk (LinearMap.range (ι.onLie (unitE O n))) q = 1

def IsCorner (G : PDivGroup p S) (ι : PDivGroup.Action (Matrix (Fin n) (Fin n) O) G)
    (H : VarpiDivModule p O S) (i : H.G ⟶ G) (r : G ⟶ H.G) : Prop :=
  i ≫ r = 𝟙 H.G ∧ r ≫ i = (ι (unitE O n) : G ⟶ G) ∧
    ∀ a : O, (H.ι a : H.G ⟶ H.G) = i ≫ (ι (Matrix.scalar (Fin n) a) : G ⟶ G) ≫ r

end OneBase

section TwoBases

variable {S S' : Type} [CommRing S] [CommRing S'] {f : S →+* S'}

def IsMatLinear {G : PDivGroup p S} {G' : PDivGroup p S'}
    (ι : PDivGroup.Action (Matrix (Fin n) (Fin n) O) G) (ι' : PDivGroup.Action (Matrix (Fin n) (Fin n) O) G')
    (t : PDivGroup.SemiHom f G' G) : Prop :=
  ∀ (c : Matrix (Fin n) (Fin n) O) (m : ℕ) (a : G.A m),
    t.app m (PDivGroup.Hom.app (ι c) m a) = PDivGroup.Hom.app (ι' c) m (t.app m a)

variable [Algebra O S] [Algebra O S']

def IsOLinear {H : VarpiDivModule p O S} {H' : VarpiDivModule p O S'} (s : PDivGroup.SemiHom f H'.G H.G) :
    Prop :=
  ∀ (c : O) (m : ℕ) (a : H.G.A m),
    s.app m (PDivGroup.Hom.app (H.ι c) m a) = PDivGroup.Hom.app (H'.ι c) m (s.app m a)

def cornerMap {G : PDivGroup p S} {G' : PDivGroup p S'} {H : VarpiDivModule p O S}
    {H' : VarpiDivModule p O S'} (i' : H'.G ⟶ G') (r : G ⟶ H.G) (t : PDivGroup.SemiHom f G' G) :
    PDivGroup.SemiHom f H'.G H.G :=
  ((PDivGroup.SemiHom.ofHom i').comp t).comp (PDivGroup.SemiHom.ofHom r)

end TwoBases

end GlobalTheory.MoritaHT

namespace GlobalTheory.MoritaHT

open GlobalTheory.VDiv GlobalTheory.VDefo

def St : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Algebra ℤ_[p] O] [Module.Free ℤ_[p] O]
    [Module.Finite ℤ_[p] O] (n : ℕ) [NeZero n],
    (∀ (S : Type) [CommRing S] [Algebra O S], IsNilpotent (p : S) →
      ∀ (G : PDivGroup p S) (ι : PDivGroup.Action (Matrix (Fin n) (Fin n) O) G), IsHTType G ι →
        ∃ (H : VarpiDivModule p O S) (i : H.G ⟶ G) (r : G ⟶ H.G),
          IsCorner G ι H i r ∧ H.IsOneDimOfHeight n) ∧
    (∀ (S : Type) [CommRing S] [Algebra O S] (H : VarpiDivModule p O S), H.IsOneDimOfHeight n →
      ∃ (G : PDivGroup p S) (ι : PDivGroup.Action (Matrix (Fin n) (Fin n) O) G) (i : H.G ⟶ G)
        (r : G ⟶ H.G), IsHTType G ι ∧ IsCorner G ι H i r) ∧
    (∀ (S S' : Type) [CommRing S] [Algebra O S] [CommRing S'] [Algebra O S'] (f : S →ₐ[O] S')
      (G : PDivGroup p S) (ι : PDivGroup.Action (Matrix (Fin n) (Fin n) O) G) (H : VarpiDivModule p O S)
      (i : H.G ⟶ G) (r : G ⟶ H.G)
      (G' : PDivGroup p S') (ι' : PDivGroup.Action (Matrix (Fin n) (Fin n) O) G')
      (H' : VarpiDivModule p O S') (i' : H'.G ⟶ G') (r' : G' ⟶ H'.G),
      IsCorner G ι H i r → IsCorner G' ι' H' i' r' →
        (∀ t : PDivGroup.SemiHom (f : S →+* S') G' G, IsMatLinear ι ι' t →
          IsOLinear (H := H) (H' := H') (cornerMap i' r t) ∧
            (IsCart t ↔ IsCart (cornerMap (H := H) (H' := H') i' r t))) ∧
        (∀ t₁ t₂ : PDivGroup.SemiHom (f : S →+* S') G' G, IsMatLinear ι ι' t₁ → IsMatLinear ι ι' t₂ →
          cornerMap (H := H) (H' := H') i' r t₁ = cornerMap i' r t₂ → t₁ = t₂) ∧
        ∀ s : PDivGroup.SemiHom (f : S →+* S') H'.G H.G, IsOLinear s →
          ∃ t : PDivGroup.SemiHom (f : S →+* S') G' G, IsMatLinear ι ι' t ∧ cornerMap i' r t = s) ∧
    ∀ (S : Type) [CommRing S], IsNilpotent (p : S) →
      ∀ G : PDivGroup p S, Subsingleton G.Lie → ∀ m : ℕ, Algebra.Etale S (G.A m)

end GlobalTheory.MoritaHT

namespace GlobalTheory.MoritaHT

open GlobalTheory.VDiv GlobalTheory.VDefo CategoryTheory

section Checks

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Algebra ℤ_[p] O] [Module.Free ℤ_[p] O]
  [Module.Finite ℤ_[p] O] {S : Type} [CommRing S]
  [Algebra O S]

theorem unitE_one : unitE O 1 = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [unitE]

end Checks

end GlobalTheory.MoritaHT

namespace GlobalTheory.MoritaHT

open GlobalTheory.VDiv GlobalTheory.VDefo CategoryTheory

section Checks2

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Algebra ℤ_[p] O] [Module.Free ℤ_[p] O]
  [Module.Finite ℤ_[p] O] {S : Type} [CommRing S] [Algebra O S]

end Checks2

end GlobalTheory.MoritaHT

namespace GlobalTheory.MoritaHT

section Checks3

example : Fact (Nat.Prime 2) ∧ Module.Free ℤ_[2] ℤ_[2] ∧ Module.Finite ℤ_[2] ℤ_[2] ∧
    Module.finrank ℤ_[2] ℤ_[2] = 1 ∧ NeZero (2 : ℕ) :=
  ⟨⟨Nat.prime_two⟩, inferInstance, inferInstance, Module.finrank_self _, inferInstance⟩

example : unitE ℤ_[2] 2 ≠ 1 ∧ unitE ℤ_[2] 2 ≠ 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := congrFun (congrFun h 1) 1
    simp [unitE, Matrix.single_apply] at this
  · have := congrFun (congrFun h 0) 0
    simp [unitE] at this

end Checks3

end GlobalTheory.MoritaHT
