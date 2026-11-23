import Mathlib
open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace GlobalTheory.DescentLocal

abbrev Datum {X U Y : Scheme.{0}} (u : U ⟶ X) (p : Y ⟶ U) :=
  ∀ (T : Scheme.{0}) (a b : T ⟶ U), a ≫ u = b ≫ u → {y : T ⟶ Y // y ≫ p = a} → {y : T ⟶ Y // y ≫ p = b}

variable {X U Y X' : Scheme.{0}} (u : U ⟶ X) (p : Y ⟶ U) (j : X' ⟶ X)

def bcDatum (θ : Datum u p) : Datum (pullback.snd u j) (pullback.snd p (pullback.fst u j)) :=
  fun T a b h y ↦
    ⟨pullback.lift (θ T (a ≫ pullback.fst u j) (b ≫ pullback.fst u j)
        (by rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% h])
        ⟨y.1 ≫ pullback.fst p (pullback.fst u j),
          by rw [Category.assoc, pullback.condition, reassoc_of% y.2]⟩).1 b
        (θ T _ _ _ _).2,
      pullback.lift_snd _ _ _⟩

end GlobalTheory.DescentLocal

namespace GlobalTheory.DescentLocal

variable {X U Y X' : Scheme.{0}} (u : U ⟶ X) (p : Y ⟶ U) (j : X' ⟶ X)

def Natural {X U Y : Scheme.{0}} {u : U ⟶ X} {p : Y ⟶ U} (θ : Datum u p) : Prop :=
  ∀ (T T' : Scheme.{0}) (w : T' ⟶ T) (a b : T ⟶ U) (h : a ≫ u = b ≫ u) (y : {y : T ⟶ Y // y ≫ p = a}),
    (θ T' (w ≫ a) (w ≫ b) (by rw [Category.assoc, Category.assoc, h]) ⟨w ≫ y.1, by rw [Category.assoc, y.2]⟩).1 =
      w ≫ (θ T a b h y).1

def Unital {X U Y : Scheme.{0}} {u : U ⟶ X} {p : Y ⟶ U} (θ : Datum u p) : Prop :=
  ∀ (T : Scheme.{0}) (a : T ⟶ U) (y : {y : T ⟶ Y // y ≫ p = a}), θ T a a rfl y = y

def Cocycle {X U Y : Scheme.{0}} {u : U ⟶ X} {p : Y ⟶ U} (θ : Datum u p) : Prop :=
  ∀ (T : Scheme.{0}) (a b c : T ⟶ U) (hab : a ≫ u = b ≫ u) (hbc : b ≫ u = c ≫ u) (y : {y : T ⟶ Y // y ≫ p = a}),
    θ T b c hbc (θ T a b hab y) = θ T a c (hab.trans hbc) y

end GlobalTheory.DescentLocal

namespace GlobalTheory.DescentLocal

variable {X U Y X₁ X₂ X₃ : Scheme.{0}} (u : U ⟶ X) (p : Y ⟶ U) {j₁ : X₁ ⟶ X} {j₂ : X₂ ⟶ X}
  {j₃ : X₃ ⟶ X}

def cmpU (k : X₁ ⟶ X₂) (hk : k ≫ j₂ = j₁) : pullback u j₁ ⟶ pullback u j₂ :=
  pullback.lift (pullback.fst u j₁) (pullback.snd u j₁ ≫ k)
    (by rw [Category.assoc, hk, pullback.condition])

@[reassoc (attr := simp)]
theorem cmpU_fst (k : X₁ ⟶ X₂) (hk : k ≫ j₂ = j₁) :
    cmpU u k hk ≫ pullback.fst u j₂ = pullback.fst u j₁ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem cmpU_snd (k : X₁ ⟶ X₂) (hk : k ≫ j₂ = j₁) :
    cmpU u k hk ≫ pullback.snd u j₂ = pullback.snd u j₁ ≫ k := pullback.lift_snd _ _ _

def cmpY (k : X₁ ⟶ X₂) (hk : k ≫ j₂ = j₁) :
    pullback p (pullback.fst u j₁) ⟶ pullback p (pullback.fst u j₂) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ cmpU u k hk)
    (by rw [Category.assoc, cmpU_fst, pullback.condition])

@[reassoc (attr := simp)]
theorem cmpY_fst (k : X₁ ⟶ X₂) (hk : k ≫ j₂ = j₁) :
    cmpY u p k hk ≫ pullback.fst p (pullback.fst u j₂) = pullback.fst p (pullback.fst u j₁) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem cmpY_snd (k : X₁ ⟶ X₂) (hk : k ≫ j₂ = j₁) :
    cmpY u p k hk ≫ pullback.snd p (pullback.fst u j₂) =
      pullback.snd p (pullback.fst u j₁) ≫ cmpU u k hk :=
  pullback.lift_snd _ _ _

end GlobalTheory.DescentLocal
