import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MemFormsLowCoeffsVanishIffFourierJacobiStatement
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.PoincarePointwiseStatement
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions GlobalTheory.ArcCM GlobalTheory.Shares

namespace GlobalTheory.MaxCuspRecord

theorem mem_MggK_of_rho_eq_zero {D : D7} (X : WeightFamilies.Prov D) (CR Tt cc : ℝ) (j : ℕ) (ka : WeightFamilies.Wt D j)
    (h0 : WeightFamilies.rho D j = 0) (F : X.Cusp j ka) : F ∈ WeightFamilies.MggK X CR Tt cc j ka := by
  unfold WeightFamilies.MggK
  simp only [Submodule.mem_iInf]
  rintro cu χ ⟨xi, -, hne, -⟩
  exact absurd (funext fun i => absurd i.isLt (by omega)) hne

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem tieMaxCusp : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ), InR D j → ∀ (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ), TieMaxCuspSt h j CR Tt cc ka := by
  intro D T h j hj ka CR Tt cc F
  rcases lt_or_eq_of_le hj.2 with hlt | hjm
  · exact (GlobalTheory.T.mem_forms_low_coeffs_vanish_iff_fourierJacobi D T.toCore h.toLawsCore j ka CR Tt cc hj hlt F).2
  · have h0 : WeightFamilies.rho D j = 0 := by
      show D.R.m - j = 0
      omega
    refine ⟨fun _ k => ?_, fun _ => mem_MggK_of_rho_eq_zero _ CR Tt cc j ka h0 F⟩
    have hU : IsUnf (T.U j T.σ₀) := h.unf j hj T.σ₀ T.good_σ₀
    have hq : (T.Q.Dw j).q = 0 := (h.pins.2.2.2 j hj).2.1.trans h0
    have hp0 : ((T.U j T.σ₀).X k).p0 = 0 := ((hU.2.1 k).1).trans hq
    have hFc : (F.1 : T.R j) ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA ka) ka.n := cutR_le T.C j ka F.2
    have hcusp := ((mem_cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA ka) ka.n F.1).1 hFc).2 T.σ₀ T.good_σ₀
    exact ⟨Formalism.L2.Pj.abelian₂.holSub_SS siegelSpaceAlgebra_holds _ _ hcusp k, fun ξ hξ =>
      absurd hξ (GlobalTheory.PoincareSeriesCompare.not_isIso_of_definite _ (Or.inl hp0) ξ)⟩

end GlobalTheory.MaxCuspRecord
