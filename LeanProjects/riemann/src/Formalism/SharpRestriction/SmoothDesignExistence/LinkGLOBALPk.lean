import Formalism.SharpRestriction.GlobalSchurBounds.LinkPk
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLbud
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth

noncomputable section

namespace Formalism.MainNotions.Pk

open Formalism.BasicNotions Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory

theorem closed_CH (𝒞 : FamClass) : Closed 𝒞 fun _ CH => 0 < CH := by
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 1, fun _ => 0⟩, fun Fm CH _ hL => ?_⟩⟩
  have h : (1 : ℝ) ≤ CH := hL.2.2.1 CH (by simp [Formalism.MainNotions.FamP.cMid])
  linarith

theorem settingF_pk {eps : ℝ} (Fm : FamP eps) (hT : TuSize Fm) : SettingEventually Fm := by
  obtain ⟨x0, h⟩ := J.setting_fam Fm hT
    ⟨Fm.x1 + 1, fun x hx i => (Fm.sizes x (lt_of_lt_of_le (lt_add_one _) hx) i).2.2.2.2.2.2.1.2.2.2.2.2.1⟩
  exact ⟨x0, fun x hx _ i u => h x hx i u⟩

structure FamGL (𝒞 : FamClass) (C0 eL C3 crystallineComparison C22 : ℝ) : Prop where
  s59 : Closed 𝒞 fun Fm _ => ∀ x : ℝ, Fm.x1 < x → ∀ i : Fm.Ix x, UnusedSlot33.division_rows_rational_lattice (Fm.D x i)
  s22 : Closed 𝒞 fun Fm _ => TaylorLogMetric.StatementFamilyConstant Fm C22
  s23 : Closed 𝒞 fun Fm _ => flipTwoThree.KudlaFamilyStatement Fm
  s24 : Closed 𝒞 fun Fm _ => StandardLattice.KudlaFamilyStatement Fm C3
  s10 : Closed 𝒞 fun Fm _ => product_first_zeroth_parts.KudlaFamilyStatement Fm crystallineComparison
  provedFourF : Closed 𝒞 fun Fm _ => LocalQuadraticParts.SlopeLemmaFamily Fm
  provedFiveF : Closed 𝒞 fun Fm _ => LocalQuadraticParts.SlopeLossFamily Fm eL
  hF3 : Closed 𝒞 fun Fm _ => StandardLattice.FamilyTheoremThreeAdmitted Fm
  tVol : Closed 𝒞 fun Fm _ => StandardLattice.TiesF Fm
  tOm : Closed 𝒞 fun Fm _ => ∀ x (i : Fm.Ix x), ∃ δ : ℂ, TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice (Fm.D x i) (Fm.D x i).host.ccK δ ∧
      OmLink (Fm.D x i) (TaylorLogMetric.tor0 (Fm.D x i) (Fm.D x i).host.ccK δ)
  tFree : Closed 𝒞 fun Fm _ => ∀ x (i : Fm.Ix x), ThFree (Fm.D x i)
  tTh : Closed 𝒞 fun Fm _ => ∀ x (i : Fm.Ix x), ExistsTwelfthRootCharacterThetaFamily (Fm.D x i) C22
  t7 : Closed 𝒞 fun Fm _ => flipTwoThree.admF7 Fm
  tCV : Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u)
  t10 : Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word), IncidenceTransportConditions (Fm.D x i) u

theorem linkGLOBAL_pk (𝒞 : FamClass) (Cabs C0 eL C3 crystallineComparison C22 : ℝ) (hCabs : 0 ≤ Cabs) (heL : 0 ≤ eL) (hC0 : 1 ≤ C0)
    (h : FamGL 𝒞 C0 eL C3 crystallineComparison C22) :
    Closed 𝒞 fun Fm CH => Fm.CoverAll → TuSize Fm → DGamSize Fm → LinkGLOBAL Fm Cabs CH C0 Cabs eL :=
  ((closed_CH 𝒞).and (h.s59.and (h.s22.and (h.s23.and (h.s24.and (h.s10.and (h.provedFourF.and (h.provedFiveF.and (h.hF3.and (h.tVol.and (h.tOm.and (h.tFree.and (h.tTh.and (h.t7.and (h.tCV.and h.t10))))))))))))))).imp
    fun Fm CH _ ⟨hCH, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15⟩ hCov hT =>
      Formalism.MainNotions.linkGLOBAL_pk Fm Cabs CH C0 eL C3 crystallineComparison C22 hCabs hCH heL hC0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
        (settingF_pk Fm hT) b14 b15 hCov hT

theorem muRank_pk (𝒞 : FamClass) (C0 eL C3 crystallineComparison C22 : ℝ) (heL : 0 ≤ eL) (hC0 : 1 ≤ C0) (h : FamGL 𝒞 C0 eL C3 crystallineComparison C22) :
    Closed 𝒞 fun Fm CH => TuSize Fm → ChosenE Fm C0 CH → NuFullF Fm ∧ J.MuRank Fm :=
  ((closed_CH 𝒞).and (h.s59.and (h.s22.and (h.s23.and (h.s24.and (h.s10.and (h.provedFourF.and (h.provedFiveF.and (h.hF3.and (h.tVol.and (h.tOm.and (h.tFree.and (h.tTh.and (h.t7.and (h.tCV.and h.t10))))))))))))))).imp
    fun Fm CH _ ⟨hCH, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15⟩ hT =>
      Formalism.MainNotions.muRank_pk Fm 0 CH C0 eL C3 crystallineComparison C22 le_rfl hCH heL hC0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13
        (settingF_pk Fm hT) b14 b15 hT

end Formalism.MainNotions.Pk

end
