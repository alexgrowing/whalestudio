import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IwLevel

structure IsStableFlag {T : Scheme.{0}} {O : Type} [Ring O] {A : Over T} [GrpObj A] (ρ : RingAct A O) {n : ℕ}
    (r : Fin (n + 1) → ℕ) (K : Fin (n + 1) → Over T) (_ : ∀ j, GrpObj (K j)) (i : ∀ j, K j ⟶ A) : Prop where
  hom : ∀ j, IsMonHom (i j)
  mono : ∀ j, Mono (i j)
  rank : ∀ j, IsIsogDeg (toUnit (K j)) (r j)
  stable : ∀ j, IsStable ρ (i j)
  incr : ∀ (j : Fin n) (T' : Over T) (x : T' ⟶ A), InSub (i j.castSucc) x → InSub (i j.succ) x

def FlagSubRep : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (O : Type) [Ring O] (G : Over S) [GrpObj G] [IsCommMonObj G]
    (ρ : RingAct G O) (n : ℕ) (r : Fin (n + 1) → ℕ), IsFinite G.hom → Flat G.hom →
    ∃ (Y : Scheme.{0}) (g : Y ⟶ S) (K : Fin (n + 1) → Over Y) (hK : ∀ j, GrpObj (K j))
      (i : ∀ j, K j ⟶ (Over.pullback g).obj G), IsProper g ∧ IsStableFlag (actPull ρ g) r K hK i ∧
      ∀ (T : Scheme.{0}) (t : T ⟶ S) (K' : Fin (n + 1) → Over T) (hK' : ∀ j, GrpObj (K' j))
        (i' : ∀ j, K' j ⟶ (Over.pullback t).obj G), IsStableFlag (actPull ρ t) r K' hK' i' →
        ∃! f : T ⟶ Y, f ≫ g = t ∧ ∃ u : ((Over.pullback t).obj G).left ⟶ ((Over.pullback g).obj G).left,
          u ≫ pullback.fst G.hom g = pullback.fst G.hom t ∧ u ≫ pullback.snd G.hom g = pullback.snd G.hom t ≫ f ∧
          ∀ j, ∃ v : (K' j).left ⟶ (K j).left, IsPullback (i' j).left v u (i j).left

end GlobalTheory.IwLevel

end
