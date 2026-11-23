import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureForms

open ReciprocityTheory.ChartRestriction.G.Out

def stdForm {g : ℕ} (a b : Fin g ⊕ Fin g → ℤ) : ℤ :=
  ∑ i : Fin g, (a (Sum.inl i) * b (Sum.inr i) - a (Sum.inr i) * b (Sum.inl i))

def reduce {g : ℕ} (k : ℕ) (a : Fin g ⊕ Fin g → ℤ) : Fin g ⊕ Fin g → ZMod k :=
  fun j => (a j : ZMod k)

variable {S : Scheme.{0}}

def mulBy (A : Over S) [GrpObj A] (k : ℕ) : A ⟶ A := (𝟙 A) ^ k

abbrev constOver (S : Scheme.{0}) (I : Type) : Over S := ∐ fun _ : I => 𝟙_ (Over S)

structure Level (P : PolAV S) (k : ℕ) (ζ : Γ(S, ⊤)ˣ) where

  hom : Multiplicative (Fin P.g ⊕ Fin P.g → ZMod k) →* (𝟙_ (Over S) ⟶ P.A)

  isKer : IsPullback
    (Sigma.desc fun v : Fin P.g ⊕ Fin P.g → ZMod k => hom (Multiplicative.ofAdd v) :
      constOver S (Fin P.g ⊕ Fin P.g → ZMod k) ⟶ P.A)
    (toUnit _) (mulBy P.A k) η[P.A]

  pairing : ∀ a b : Fin P.g ⊕ Fin P.g → ℤ,
    WeilIs P.A P.L (k : ℤ) (T := 𝟙_ (Over S))
      (hom (Multiplicative.ofAdd (reduce k a))) (hom (Multiplicative.ofAdd (reduce k b)))
      (ζ ^ stdForm a b : Γ(S, ⊤)ˣ)

namespace Level

variable {P : PolAV S} {k : ℕ} {ζ : Γ(S, ⊤)ˣ}

def pt (ℓ : Level P k ζ) (v : Fin P.g ⊕ Fin P.g → ZMod k) : 𝟙_ (Over S) ⟶ P.A :=
  ℓ.hom (Multiplicative.ofAdd v)

def ptOver (ℓ : Level P k ζ) (T : Over S) (v : Fin P.g ⊕ Fin P.g → ZMod k) : T ⟶ P.A :=
  toUnit T ≫ ℓ.pt v

def ptKer (ℓ : Level P k ζ) (v : Fin P.g ⊕ Fin P.g → ZMod k) :
    𝟙_ (Over S) ⟶ pullback (mulBy P.A k) η[P.A] :=
  Sigma.ι (fun _ : Fin P.g ⊕ Fin P.g → ZMod k => 𝟙_ (Over S)) v ≫ ℓ.isKer.isoPullback.hom

example (ℓ : Level P k ζ) (v : Fin P.g ⊕ Fin P.g → ZMod k) :
    ℓ.ptKer v ≫ pullback.fst _ _ = ℓ.pt v := by
  simp [ptKer, pt]

end Level

example {g : ℕ} (i : Fin g) :
    stdForm (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inr i) 1) = 1 := by
  simp [stdForm, Pi.single_apply]

example {g : ℕ} (a b : Fin g ⊕ Fin g → ℤ) : stdForm b a = -stdForm a b := by
  simp only [stdForm, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureForms
