import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPageRunRecordSubFour
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSmallIffOpo
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsThresholdRunHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin GlobalTheory.FinalJoin2

namespace GlobalTheory.FinalJoin2

theorem hyp_concl_at_run : ∃ (CK : ℝ) (x₁ : ℝ), ∀ (D : D7) (T : Top D) (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ), (∀ j, InR D j → ParOK T EX p j) → ∀ (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D), SizesAt L → Pm.CnW = 10 → (∀ i, Real.log (D.host.g i) ≤ 9 * L.sc.L + 1) → 1000 ≤ Tp.CP → Tp.CP ^ 20 ≤ zBase L → x₁ ≤ L.sc.x → FieldSmall D L → (∀ (j : ℕ) (hj : InR D j), HypC L (recPJ h j hj) ⟨CK, 20, Tp.CP, Tp.eP, Tp.CP, Tp.eP, 7⟩ Tp.CP Tp.eP 7 0 L.Ct (scalOfP (recB (h).toLawsCore) hinj EX p (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO) (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO Tp.nP Tp.nWn (LevelStarExponents.h0 L - 4) (nusR h j (lR Tp hK j)) ∧ Concl (recPJ h j hj) (scalOfP (recB (h).toLawsCore) hinj EX p (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO) (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO (nusR h j (lR Tp hK j)) ((recPJ h j hj).rk (kaR Tp hK j) ((recB (h).toLawsCore).Mlat j (kaR Tp hK j)) * D.R.f * D.R.m * L.sc.b * L.de2)) := by
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.FinalJoin.runHolds_of_parOK
  obtain ⟨CK, hCK⟩ := GlobalTheory.FinalJoin.RecordRun.exists_pageRun_record_sub_four
  refine ⟨CK, max ((10 : ℝ) ^ 60) (x₀ 20 CK), ?_⟩
  intro D T h hinj EX p hpar L Pm Tp hK hS hC hg hCP hz hx hF j hj
  have hO : OPO L (recB h.toLawsCore) := (fieldSmall_iff_opo D T h L).1 hF
  have hP := hCK D L Pm Tp hK hS hC hg ((le_max_left _ _).trans hx) hCP hz _ _ j (recPJ h j hj) hj hO
  exact (hx₀ D T h hinj EX p hpar j hj L _ _ _ _ _ _ _ _ _ _ _ hP ((le_max_right _ _).trans hx)).2

end GlobalTheory.FinalJoin2
