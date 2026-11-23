import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.TaylorSpanGeneratorsAlt
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HasseJidPow

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

theorem sumN_eq {σ : Type*} (β : σ →₀ ℕ) : (β.sum fun _ n => n) = Finsupp.degree β := rfl

theorem mem_Jid_smul_top_of_JHfr {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
    (la : HeightOneSpectrum (𝓞 B.KO)) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL) (u : WeightFamilies.Wt D j)
    {b : ℕ} (hb : 1 ≤ b) (y : ↥(HK X la w u)) (hy : (y : Lw X la w) ∈ JHfr X la w u b) :
    y ∈ Jid X la w • (⊤ : Submodule ↥(Frac0 X la w) ↥(HK X la w u)) := by
  have h1 : y ∈ Jid X la w ^ b • (⊤ : Submodule ↥(Frac0 X la w) ↥(HK X la w u)) :=
    (mem_Jid_pow_smul_top X la w).2 ((mem_JHfr X la w).1 hy)
  exact Submodule.smul_mono_left (Ideal.pow_le_self (by omega)) h1

theorem hasseVan_holds : HasseVan := by
  intro D B P j X ka wL wF G la a x hx β hβ h
  rw [reduction_eq_zero_iff_mem_ideal_smul]
  have hx' : (x : Lw X la G.w) ∈ JHfr X la G.w wF a :=
    (mem_JHfr X la G.w).2 ((mem_Jid_pow_smul_top X la G.w).1 hx)
  have h2 := hasse_jid_power X la G.w wF β a _ hx'
  exact mem_Jid_smul_top_of_JHfr X la G.w wF (b := a - β.sum fun _ n => n) (by omega) ⟨_, h⟩ h2

end PoleLengthBounds
