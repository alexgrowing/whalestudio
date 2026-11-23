import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Ia
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FractionalIdealEqOfLocalSpansEqStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagCoeffIdealOfLatticeFgAndMemIffStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeInfIsotropicEqSumFractionalIdealSmulStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanCoefficientIdealEqSpanFrameScaleStatement

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLatXS

theorem xlam_eq_span_scaled : ∀ (D : D7) (T : D.host.E) (G : LFlag (VS D) D.R.rS T) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ n ∈ (A p).N, ∃ L, (A p).IsInner L ∧ lattice₂ D Z.M p Λ = LocNG.img n ((A p).LamStd L)) → ∃ e' : Fin D.R.rS → (VS D).V, (∀ a, e' a - G.fl.e a ∈ G.fl.Xa a.val) ∧ XLam Λ G = Submodule.span (𝓞 D.host.E) {y | ∃ (a : Fin D.R.rS) (x : D.host.E), x ∈ (ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ∧ y = x • e' a} := by
  intro D T G Z A hA Λ hΛ hloc
  have hdd : ddS D ≠ 0 := by
    unfold ddS
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.map_eq_bot_iff_of_injective]
    · exact differentIdeal_ne_bot
    · exact FaithfulSMul.algebraMap_injective _ _
  have hJ : ∀ a : Fin D.R.rS, GlobalTheory.RowLatXS.Ia Λ G.fl a =
      ((ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E) := by
    intro a
    refine GlobalTheory.T.fractional_ideal_eq_of_local_spans_eq D Z _ _ (GlobalTheory.T.flagCoeffIdealOfLattice_fg_and_mem_iff _ _ _ G.fl Λ a hΛ.fg).1
      (FractionalIdeal.fg_of_isNoetherianRing le_rfl _) (fun p => ?_)
    rw [GlobalTheory.T.span_coefficientIdeal_eq_span_frameScale D T G Z A hA Λ hΛ hloc p a]
    have h := Formalism.L2.SG.Pf.locDiffC_holds D Z p a.castSucc
    simp only [Fin.coe_castSucc] at h
    exact h.symm
  obtain ⟨e', he, hX⟩ := GlobalTheory.T.lattice_inf_isotropic_eq_sum_fractionalIdeal_smul (VS D) D.R.rS T G Λ
    (fun a => ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ)))) (fun a => zpow_ne_zero _ hdd)
    (fun a x hx hxa => by
      have h1 : G.fl.coefX x a ∈ GlobalTheory.RowLatXS.Ia Λ G.fl a :=
        ((GlobalTheory.T.flagCoeffIdealOfLattice_fg_and_mem_iff _ _ _ G.fl Λ a hΛ.fg).2 _).2 ⟨x, hx, hxa, rfl⟩
      rw [hJ a] at h1
      exact h1)
    (fun a t ht => by
      have h1 : t ∈ GlobalTheory.RowLatXS.Ia Λ G.fl a := by rw [hJ a]; exact ht
      exact ((GlobalTheory.T.flagCoeffIdealOfLattice_fg_and_mem_iff _ _ _ G.fl Λ a hΛ.fg).2 t).1 h1)
  exact ⟨e', he, hX⟩

end GlobalTheory.RowLatXS
