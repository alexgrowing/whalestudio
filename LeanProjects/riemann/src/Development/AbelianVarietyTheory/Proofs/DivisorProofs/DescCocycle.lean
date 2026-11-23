import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LBDescent

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

abbrev Triple : Scheme.{0} := pullback (pullback.snd f f) (pullback.fst f f)

def pr13 : Triple f ⟶ pullback f f :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst f f) (pullback.snd _ _ ≫ pullback.snd f f) (by
    calc (pullback.fst _ _ ≫ pullback.fst f f) ≫ f = pullback.fst (pullback.snd f f) (pullback.fst f f) ≫
          pullback.snd f f ≫ f := by rw [Category.assoc, pullback.condition]
      _ = pullback.snd (pullback.snd f f) (pullback.fst f f) ≫ pullback.fst f f ≫ f := pullback.condition_assoc _
      _ = (pullback.snd _ _ ≫ pullback.snd f f) ≫ f := by rw [pullback.condition, Category.assoc])

def chart (L : LB X) (i j : L.ι) : (pullback f f).Opens :=
  pullback.fst f f ⁻¹ᵁ L.U i ⊓ pullback.snd f f ⁻¹ᵁ L.U j

def DescCompat (L : LB X) (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ) : Prop :=
  ∀ (z : ↥(pullback f f)) (i i' j j' : L.ι), pullback.fst f f z ∈ L.U i → pullback.fst f f z ∈ L.U i' →
    pullback.snd f f z ∈ L.U j → pullback.snd f f z ∈ L.U j' →
    gm (𝟙 _) z _ (φ i' j') =
      gm (pullback.fst f f) z _ (L.g i i') * gm (𝟙 _) z _ (φ i j) * gm (pullback.snd f f) z _ (L.g j' j)

def DescCocycle (L : LB X) (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ) : Prop :=
  ∀ (w : ↥(Triple f)) (i j k : L.ι), pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w) ∈ L.U i →
    pullback.snd f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w) ∈ L.U j → pullback.snd f f (pullback.snd (pullback.snd f f) (pullback.fst f f) w) ∈ L.U k →
    gm (pullback.fst (pullback.snd f f) (pullback.fst f f)) w _ (φ i j) *
      gm (pullback.snd (pullback.snd f f) (pullback.fst f f)) w _ (φ j k) = gm (pr13 f) w _ (φ i k)

end GlobalTheory.LBDescent
