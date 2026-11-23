import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

def addC (Q : ObjectProperty (Thick (smFun X q))) (ĝ : ∀ T : Q.FullSubcategory, T.obj.B) : CH.Cn (CH.modF (sP Q).A) 1 :=
  fun σ => (show (σ.obj (Fin.last 1)).obj.B from
    ĝ (σ.obj (Fin.last 1)) - (σ.map (homOfLE (Fin.zero_le (Fin.last 1)))).hom.φ (ĝ (σ.obj 0)))

def zeroC (Q : ObjectProperty (Thick (smFun X q))) (ĝ : ∀ T : Q.FullSubcategory, T.obj.B) : CH.Cn (CH.modF (sP Q).A) 0 :=
  fun σ => (show (σ.obj (Fin.last 0)).obj.B from ĝ (σ.obj (Fin.last 0)))

def xdtC (s : ℕ) (V : X.Opens) {d : ℕ} (t : Fin d → Γ(X, V)) (x : Γ(X, V)) : CH.Cn (CH.modF (sP (KS q s {V})).A) d :=
  (CH.mulP (sP (KS q s {V})).A).cupC (Nat.zero_add d)
    (zeroC _ fun T => liftV T.obj (ks_in q s V T.obj T.property) x)
    (cupListC (sP (KS q s {V})).A fun k => addC _ fun T => liftV T.obj (ks_in q s V T.obj T.property) (t k))

end CrystallineSemistableComparison.Pb
