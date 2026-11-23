import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.Reduce

noncomputable section

namespace PI.CntNotIntW

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IntL : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      RowsOf u F0 what₂ → ∀ Λ ∈ what₂, ∀ (Z : MatZ D) (F' : LFlag (VS D) D.R.rS (Tn u')),
        F' ∈ EZ (Tn u') F0 Λ Z → ∀ p, (M p).split = none → ∀ a b, ZhatLoc M δ p Z a b ∈ (M p).L.O

def IntG : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      RowsOf u F0 what₂ → ∀ Λ ∈ what₂, ∀ (Z : MatZ D) (F' : LFlag (VS D) D.R.rS (Tn u')),
        F' ∈ EZ (Tn u') F0 Λ Z → ∀ p (g : Loc.SplitG (M p).L), (M p).split = some g →
          ∀ a b, ZZP (M := M) δ u u' p Z a b ∈ (M p).R

theorem intOnEZ_of (hL : IntL) (hG : IntG) : IntOnEZ := by
  intro D δ M hA u u' hT F0 what₂ hR Λ hΛ Z F' hF' p a b
  rcases hs : (M p).split with _ | g
  · have h1 := hL D δ M hA u u' hT F0 what₂ hR Λ hΛ Z F' hF' p hs a b
    simp only [ZZP, Loc.HermSp.ZZplusOf, Loc.Model.R, hs]
    exact h1
  · exact hG D δ M hA u u' hT F0 what₂ hR Λ hΛ Z F' hF' p g hs a b

theorem notIntAll_of_LG (hL : IntL) (hG : IntG) : PI.CntLocalParts.NotIntAll :=
  notIntAll_of (intOnEZ_of hL hG)

end PI.CntNotIntW
