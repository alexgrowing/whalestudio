import Mathlib
import Formalism.PeriodIntegrals.CntLocalParts

noncomputable section

namespace PI.CntNotIntW

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IntOnEZ : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      RowsOf u F0 what₂ → ∀ Λ ∈ what₂, ∀ (Z : MatZ D) (F' : LFlag (VS D) D.R.rS (Tn u')),
        F' ∈ EZ (Tn u') F0 Λ Z → ∀ p a b, ZZP (M := M) δ u u' p Z a b ∈ (M p).R

theorem cntE_eq_zero_of_empty {D : Formalism.BasicNotions.D7} {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (Z : MatZ D) (h : EZ T' F0 Λ Z = ∅) : cntE T' F0 Λ Z = 0 := by
  unfold cntE
  rw [h]
  simp

theorem nu_eq_zero_of_empty {D : Formalism.BasicNotions.D7} {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (Z : MatZ D) (h : ∀ Λ ∈ what₂, EZ T' F0 Λ Z = ∅) :
    Formalism.L2.SG.CntLocal.nu T' F0 what₂ Z = 0 := by
  unfold Formalism.L2.SG.CntLocal.nu
  rw [Finset.sum_eq_zero (fun Λ hΛ => by rw [cntE_eq_zero_of_empty T' F0 Λ Z (h Λ hΛ)]; simp), zero_div]

theorem notIntAll_of (h : IntOnEZ) : PI.CntLocalParts.NotIntAll := by
  intro D δ M hA _L u u' hT F0 what₂ hR Z hZ
  obtain ⟨p, a, b, hn⟩ := hZ
  refine nu_eq_zero_of_empty (Tn u') F0 what₂ Z fun Λ hΛ => ?_
  rw [Set.eq_empty_iff_forall_notMem]
  intro F' hF'
  exact hn (h D δ M hA u u' hT F0 what₂ hR Λ hΛ Z F' hF' p a b)

end PI.CntNotIntW
