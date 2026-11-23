import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.CompatH
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.IsFirstChernClassOfLineBundle
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.BetaPull

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ w₁ w₂ w₃ w₄

theorem pull_square {R : Type} [CommRing R]
    {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
    {C₃ : Type u₃} [Category.{v₃} C₃] {C₄ : Type u₄} [Category.{v₄} C₄]
    {F₁ : C₁ ⥤ ModuleCat.{w₁} R} {F₂ : C₂ ⥤ ModuleCat.{w₂} R} {F₃ : C₃ ⥤ ModuleCat.{w₃} R}
    {F₄ : C₄ ⥤ ModuleCat.{w₄} R}
    (m : CH.Mor F₁ F₂ (RingHom.id R)) (b : CH.Mor F₂ F₃ (RingHom.id R))
    (b' : CH.Mor F₁ F₄ (RingHom.id R)) (q : CH.Mor F₄ F₃ (RingHom.id R))
    (η : b.G ⋙ m.G ⟶ q.G ⋙ b'.G)
    (hτ : ∀ T x, q.τ T (b'.τ (q.G.obj T) ((F₁.map (η.app T)).hom x)) = b.τ T (m.τ (b.G.obj T) x))
    (n : ℕ) (x : CH.H F₁ n) : b.pull n (m.pull n x) = q.pull n (b'.pull n x) := by
  rw [← (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) m b n x).1,
    ← (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) b' q n x).1]
  exact CrystallineSemistableComparison.P.prism (m.comp b) (b'.comp q) η hτ n x

theorem pt_nat {P P' : CommRingCat.{0} ⥤ Type} (a : P ⟶ P') {B C : CommRingCat.{0}} (f : B ⟶ C)
    (g : C ⟶ C) (hg : g = 𝟙 C) (y : P.obj B) :
    P'.map g (a.app C (P.map f y)) = P'.map f (a.app B y) := by
  subst hg
  rw [P'.map_id]
  exact ConcreteCategory.congr_hom (a.naturality f) y

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F F' : Fn O} (κ : O →+* OC l)
  (u : Fn.Map F F') (k : Bool) (n : ℕ)

theorem units_pullback_empty_product_one {B B' : Type} [CommRing B] [CommRing B'] (i : B' →+* B) (a : B'ˣ) (ha : a = 1)
    (e : Empty → Bˣ) : (1 : Bˣ) =
      (∏ j, e j) * Units.map (RingHom.id B).toMonoidHom ((1 : Bˣ) ^ 1 * (Units.map i.toMonoidHom a)⁻¹) := by
  subst ha
  simp

def cmpHom (T : El (F.pt κ)) :
    (gT F κ k n ⋙ (pullMorC κ u k n).G).obj T ⟶ ((pullMor (u.pt κ) n).G ⋙ (βMor F' κ k n).G).obj T where
  φ := RingHom.id _
  u := fun j => j.elim
  comm _ := rfl
  dp := (DPMorphism.id _).isDPMorphism
  hle := fun _ h => h
  pt := by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)
    · exact pt_nat u.u (CommRingCat.ofHom (uJ k T.1.obj n))
        (CommRingCat.ofHom (Ideal.quotientMap _ (RingHom.id _) fun _ h => h))
        (CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl))) T.2.1
  hx := fun j => j.elim
  hs := units_pullback_empty_product_one _ _ rfl _
  hv := fun j => j.elim

def cmpNat : gT F κ k n ⋙ (pullMorC κ u k n).G ⟶ (pullMor (u.pt κ) n).G ⋙ (βMor F' κ k n).G where
  app T := cmpHom κ u k n T
  naturality T T' f := Thick.Hom.ext rfl (funext fun j => j.elim)

theorem beta_pull {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F F' : Fn O} (κ : O →+* OC l)
    (u : Fn.Map F F') (k : Bool) (n j : ℕ) (x : Hc F' κ k n j) :
    β F κ k n j (pullHc κ u k n j x) = (pullMor (u.pt κ) n).pull j (β F' κ k n j x) :=
  pull_square (pullMorC κ u k n) (βMor F κ k n) (βMor F' κ k n) (pullMor (u.pt κ) n)
    (cmpNat κ u k n) (fun _ _ => rfl) j x

end GlobalTheory.CompanionTheory.BetaPull
