import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.AssembleAlt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.TaylorSpanGeneratorsAlt

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.PoleLengthCount

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem coe_wfr (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (col : Fin G.N) :
    (PoleLengthBounds.wfr G la col : Lw X la G.w) =
      algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wL (G.w col))) * w0inv X la G.w := by
  simp only [PoleLengthBounds.wfr, coe_weightZeroFraction, frac_apply, pow_one]

theorem uSpec_wfr (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) :
    uSpec G la (fun col => toOsK X la G.w (PoleLengthBounds.wfr G la col)) :=
  fun col => ⟨PoleLengthBounds.wfr G la col, coe_wfr G la col, rfl⟩

theorem sum_T_wfr (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) :
    ∑ col, algebraMap (Kp X la G.N) ↥(Frac0 X la G.w)
      (algebraMap (Op X la G.N) (Kp X la G.N) (Tv X la G.N ((0 : Fin (WeightFamilies.dimY D j + 1)), col))) *
        PoleLengthBounds.wfr G la col = 1 := by
  apply Subtype.ext
  have h : ∀ col, ((algebraMap (Kp X la G.N) ↥(Frac0 X la G.w)
      (algebraMap (Op X la G.N) (Kp X la G.N) (Tv X la G.N ((0 : Fin (WeightFamilies.dimY D j + 1)), col))) *
        PoleLengthBounds.wfr G la col : ↥(Frac0 X la G.w)) : Lw X la G.w) =
      frac X la G.w 1 ((algebraMap (Op X la G.N) (Kp X la G.N) (Tv X la G.N ((0 : Fin (WeightFamilies.dimY D j + 1)), col))) •
        emb X la G.N (X.inc wL (G.w col))) := by
    intro col
    rw [LinearMap.map_smul, Algebra.smul_def]
    rfl
  rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_congr rfl fun col _ => h col, ← map_sum]
  show frac X la G.w 1 (sec X la G.w 0) = _
  rw [frac_apply, pow_one, section_mul_inverse_eq_one]
  rfl

theorem sum_T_u (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) :
    ∑ col, algebraMap (Op X la G.N) (OsK X la G.w) (Tv X la G.N ((0 : Fin (WeightFamilies.dimY D j + 1)), col)) *
      toOsK X la G.w (PoleLengthBounds.wfr G la col) = 1 := by
  have := congrArg (toOsK X la G.w) (sum_T_wfr G la)
  rw [map_one, map_sum] at this
  rw [← this]
  refine Finset.sum_congr rfl fun col _ => ?_
  rw [map_mul, AlgHom.commutes]
  rfl

theorem unitCols_of (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO))
    (hOrd : ∀ (ζ : PtsG G la) (col : Fin G.N), 0 ≤ ord (unifO X la G.N) ζ (toOsK X la G.w (PoleLengthBounds.wfr G la col))) :
    UnitCols G la :=
  ⟨fun col => toOsK X la G.w (PoleLengthBounds.wfr G la col), uSpec_wfr G la, sum_T_u G la, hOrd⟩

theorem unitCols_of_column (hCol : PoleLengthBounds.Column) (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la)
    (S : Scal B) (CRm : ℝ) (T : ℕ) (c : ℝ) (hOk : Q.Ok S CRm T c) (hw : ∀ k, G.w k ∈ X.WWc S.sW wL) :
    UnitCols G la :=
  unitCols_of G la fun ζ col => (hCol G la Q S CRm T c hOk hw ζ).1 col

end PI.PoleLengthCount
