import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.AssembleAlt
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HassePresH
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HasseJidPow
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HasseJacobsonPowers.SfrMulMemJHfr

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps Finset.HasAntidiagonal

namespace PI.PoleLengthCount

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem mem_pow_smul_top_iff {N : ℕ} (la : HeightOneSpectrum (𝓞 B.KO)) (w : Fin N → B.Cusp j wL)
    {u : WeightFamilies.Wt D j} {a : ℕ} {x : ↥(HK X la w u)} :
    x ∈ Jid X la w ^ a • (⊤ : Submodule ↥(Frac0 X la w) ↥(HK X la w u)) ↔ (x : Lw X la w) ∈ JHfr X la w u a := by
  rw [mem_Jid_pow_smul_top X la w, mem_JHfr X la w]

theorem hasse_preserves_kernel (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : HKPres G la := fun β x hx =>
  (mem_HK X la G.w).2 (hasse_presentation X la G.w wF β x ((mem_HK X la G.w).1 hx))

theorem leading_coeff_eq_zero_of_jet {N : ℕ} (la : HeightOneSpectrum (𝓞 B.KO)) (w : Fin N → B.Cusp j wL)
    {u : WeightFamilies.Wt D j} (x : ↥(HK X la w u)) (hx : (x : Lw X la w) ∈ JHfr X la w u 1) : toA0K X la w u x = 0 := by
  rw [reduction_eq_zero_iff_mem_ideal_smul, ← pow_one (Jid X la w), mem_pow_smul_top_iff la w]
  exact hx

theorem vanishingOnQuadric (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Vanish G la := by
  intro k β x hx hβ
  unfold rD
  split_ifs with h
  · refine leading_coeff_eq_zero_of_jet la G.w _ ?_
    have h1 := hasse_jid_power X la G.w wF β k _ ((mem_pow_smul_top_iff la G.w).1 hx)
    exact PI.HJP.JHfr_anti X la G.w wF (by omega) h1
  · rfl

end PI.PoleLengthCount
