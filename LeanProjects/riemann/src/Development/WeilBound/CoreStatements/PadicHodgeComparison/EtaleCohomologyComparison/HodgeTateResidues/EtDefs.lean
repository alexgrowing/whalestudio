import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsEtaleFirstChernUntwisted

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.HT

open CH

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

structure EtP (e : E.EtFam l K) : Prop where
  good : e.Good
  one : ∀ (M : Model l K) (n : ℕ), e M n 0 (GlobalTheory.EtC.one (l ^ n) M.spc) = CH.oneH (AcrEl M.P n)
  one_ex : ∀ M : Model l K, ∃ v : M.T 0, ∀ k, v.lev k = GlobalTheory.EtC.one (l ^ k) M.spc
  first_chern_class_exists : ∀ (M : Model l K) (D : E.LineData M.X) (r : E.Roots l), ∃ v, IsEtaleFirstChernUntwisted r D v
  c1 : ∀ (M : Model l K) (D : E.LineData M.X) (r : E.Roots l) (v : M.T 2), IsEtaleFirstChernUntwisted r D v →
    ∀ (C : Type 1) [Category.{0} C] (G : C ⥤ El M.P) (Λ : E.Lift G D) (n : ℕ),
      ∃ (z : Cn (G ⋙ modF (AcrEl M.P n)) 2) (hz : d _ 2 z = 0), Λ.IsCoc n (E.tCo G n 2 z) ∧
        (cx _).cls z hz = (Mor.restrict (modF (AcrEl M.P n)) G).pull 2 (e M n 2 (v.lev n))

end CrystallineSemistableComparison.HT
