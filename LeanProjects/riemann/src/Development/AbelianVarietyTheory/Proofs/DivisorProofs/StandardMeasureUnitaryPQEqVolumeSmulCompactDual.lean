import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.VolUFactProdMulLe
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.BridgeA
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MeasUpq
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

noncomputable section

namespace GlobalTheory.LowRow.CompactDualScale

theorem omegaDensity_smul {P Q : ℕ} {μ : Measure (UpqT P Q)} {c : ENNReal} (a : ENNReal) (ha : a ≠ ⊤)
    (h : OmegaDensity μ c) : OmegaDensity (a • μ) (a * c) := by
  obtain ⟨lam, hlam, hl⟩ := h
  refine ⟨lam, hlam, ?_⟩
  refine (ENNReal.Tendsto.const_mul hl (Or.inr ha)).congr fun r => ?_
  rw [Measure.smul_apply, smul_eq_mul, mul_div_assoc]

theorem omegaDensity_unique {P Q : ℕ} {μ : Measure (UpqT P Q)} {c c' : ENNReal}
    (h : OmegaDensity μ c) (h' : OmegaDensity μ c') : c = c' := by
  obtain ⟨lam, hlam, hl⟩ := h
  obtain ⟨lam', hlam', hl'⟩ := h'
  rw [Formalism.IndefR.Eqv.MU.omegaLeb_unique hlam hlam'] at hl'
  exact tendsto_nhds_unique hl hl'

theorem isMinf_eq_volU_smul_cd : ∀ (cd : CDHaar) (p q : ℕ) (m : Measure (UpqT p q)), Lev.IsMinf m →
    m = ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU (p + q)) • cd.cd p q := by
  intro cd p q m hm
  obtain ⟨c, hc0, hctop, hpq, hN⟩ := cd.trick p q
  haveI := cd.haar (p + q) 0
  haveI := cd.prob (p + q)
  haveI := cd.haar p q
  have hmain := ReciprocityTheory.ChartRestriction.DS.PolarCoordinateComparison.omegaDensity_main (N := p + q) (cd.cd (p + q) 0)
  have hc := omegaDensity_unique hN hmain
  have hV : 0 < ReciprocityTheory.ChartRestriction.DS.volU (p + q) := ReciprocityTheory.ChartRestriction.DS.PolarCoordinateComparison.volU_pos (p + q)
  have hκ : (0 : ℝ) < 2 ^ ((p + q) * (p + q - 1) / 2) := by positivity
  have hmul : ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU (p + q)) * c = Formalism.L2.Theta.minfDensity (p + q) := by
    rw [hc, ← ENNReal.ofReal_mul hV.le, Formalism.L2.Theta.minfDensity]
    have e : ReciprocityTheory.ChartRestriction.DS.volU (p + q) * (1 / (2 ^ ((p + q) * (p + q - 1) / 2) * ReciprocityTheory.ChartRestriction.DS.volU (p + q)))
        = ((2 : ℝ) ^ ((p + q) * (p + q - 1) / 2))⁻¹ := by
      field_simp
    rw [e, ENNReal.ofReal_inv_of_pos hκ, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  have hV0 : ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU (p + q)) ≠ 0 := (ENNReal.ofReal_pos.2 hV).ne'
  have hm' : Lev.IsMinf (ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU (p + q)) • cd.cd p q) := by
    refine ⟨Measure.IsHaarMeasure.smul _ hV0 ENNReal.ofReal_ne_top, ?_⟩
    rw [← hmul]
    exact omegaDensity_smul _ ENNReal.ofReal_ne_top hpq
  exact Formalism.IndefR.Eqv.MU.isMinf_unique hm' hm

end GlobalTheory.LowRow.CompactDualScale
