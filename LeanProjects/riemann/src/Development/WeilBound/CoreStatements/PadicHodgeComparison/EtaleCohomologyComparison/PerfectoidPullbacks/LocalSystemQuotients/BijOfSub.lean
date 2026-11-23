import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ResVq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace CrystallineSemistableComparison.Pb.SubquotientResolution

variable {R : Type} [CommRing R] {D D' : Type 1} [Category.{0} D] [Category.{0} D'] {Θ : PDF R D} {Θ' : PDF R D'}
  {P : ObjectProperty D} {P' : ObjectProperty D'}

def rA (Θ : PDF R D) {P Q : ObjectProperty D} (h : Q ≤ P) :
    CH.Mor (CH.modF (Θ.res P.ι).A) (CH.modF (Θ.res Q.ι).A) (RingHom.id R) where
  G := ObjectProperty.ιOfLE h
  τ _ := LinearMap.id
  nat _ _ := rfl

def rQ (Θ : PDF R D) {P Q : ObjectProperty D} (h : Q ≤ P) (c : R) :
    CH.Mor (sq (IdF.top (Θ.res P.ι).A) (IdF.span (Θ.res P.ι).A c)) (sq (IdF.top (Θ.res Q.ι).A) (IdF.span (Θ.res Q.ι).A c))
      (RingHom.id R) where
  G := ObjectProperty.ιOfLE h
  τ _ := LinearMap.id
  nat _ _ := rfl

theorem bij_of_sub {c : R} (m : QMor (Θ.res P.ι) (Θ'.res P'.ι) (IdF.span _ c)) (Q : ObjectProperty D) (Q' : ObjectProperty D')
    (hQ : Q ≤ P) (hQ' : Q' ≤ P') (hG : ∀ T : Q'.FullSubcategory, Q (m.G.obj ⟨T.obj, hQ' _ T.property⟩).obj) (j : ℕ)
    (z0 : Function.Bijective ((rA Θ hQ).pull j)) (zq : Function.Bijective ((rQ Θ' hQ' c).pull j))
    (g : Function.Bijective (((subQ m Q Q' hQ' hG).o (IdF.span _ c) fun _ => le_rfl).pull j)) :
    Function.Bijective ((m.o (IdF.span _ c) fun _ => le_rfl).pull j) := by
  refine (Function.Bijective.of_comp_iff' zq _).1 ?_
  have e : ⇑((rQ Θ' hQ' c).pull j) ∘ ⇑((m.o (IdF.span _ c) fun _ => le_rfl).pull j) =
      ⇑(((subQ m Q Q' hQ' hG).o (IdF.span _ c) fun _ => le_rfl).pull j) ∘ ⇑((rA Θ hQ).pull j) := by
    funext x
    refine ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) (m.o (IdF.span _ c) fun _ => le_rfl) (rQ Θ' hQ' c) j x).1).symm.trans
      (Eq.trans ?_ ((CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) (rA Θ hQ)
        ((subQ m Q Q' hQ' hG).o (IdF.span _ c) fun _ => le_rfl) j x).1))
    rfl
  rw [e]
  exact g.comp z0

end CrystallineSemistableComparison.Pb.SubquotientResolution
