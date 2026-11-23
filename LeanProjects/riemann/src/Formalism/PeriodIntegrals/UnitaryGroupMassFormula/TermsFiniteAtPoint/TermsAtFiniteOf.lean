import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.Development

noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sigOK_holds (D : D7) : (VS D).SigOK := D.sp.Y_sig 0

theorem termsAtFinite_of' (hR : ZhatReduce) (hF : FixedZhatFinite) (D : D7) (u u' : D.what₂.Word)
    (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hΛ : IsRowLat D F0 Λ) (w : Point D.host.E (D.R.rS + 1)) :
    {t : TermsOf D u' F0 Λ | AtPt Λ (lf D F0) (PD D Λ (lf D F0) u') t w}.Finite :=
  termsAtFinite_of hR hF D u u' (sigOK_holds D) F0 Λ hΛ w

theorem terms_nonempty (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : IsRowLat D F0 Λ) : Nonempty (TermsOf D u F0 Λ) := by
  obtain ⟨-, hfix, hX⟩ := hΛ
  obtain ⟨-, -, hlift, hconv⟩ := hfix
  have hP : PD D Λ (lf D F0) u (lf D F0) := by
    refine ⟨hlift, ⟨1, fun a b hab => Matrix.one_apply_ne hab.ne', fun a => Matrix.one_apply_eq a, fun b => ?_⟩,
      hconv, hX⟩
    intro P _
    convert Submodule.zero_mem _ using 1
    simp only [frameAct]
    rw [Finset.sum_eq_single b (fun a _ hab => by simp [Matrix.one_apply_ne hab])
      (fun h => absurd (Finset.mem_univ b) h)]
    simp
  exact ⟨Quot.mk _ ⟨lf D F0, hP⟩⟩

end PI.TermsAtPtFiniteW
