import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw

theorem isCv_of_subst_X_pow {C : Type} [Field C] (V : VF C) {σ : Type} {m : ℕ} (hm : 0 < m)
    (δ γ : σ → PowerSeries C) (hγ : IsCv V γ)
    (h : ∀ i, PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ m) (δ i) = γ i) : IsCv V δ := by
  intro i
  have hc : ∀ n, PowerSeries.coeff n (δ i) = PowerSeries.coeff (m * n) (γ i) := by
    intro n
    rw [← h i, Formalism.L2.FormalSeriesBounds.coeff_subst_X_pow hm]
  refine ⟨?_, fun n => ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hc, mul_zero,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (hγ i).1
  · rw [hc]
    exact (hγ i).2 _

theorem cvRoot_alongCv_comp {C : Type} [Field C] {σ τ : Type} [Finite σ] [Finite τ] {γ : τ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) {f : σ → MvPowerSeries τ C}
    (hf : ∀ i, MvPowerSeries.constantCoeff (f i) = 0) (F : MvPowerSeries σ C) :
    alongCv (fun i => alongCv γ (f i)) F = alongCv γ (MvPowerSeries.subst f F) := by
  unfold alongCv
  rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hf)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero hγ)]

theorem cvRoot_alongCv_X {C : Type} [Field C] {τ : Type} [Finite τ] {γ : τ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (i : τ) :
    alongCv γ (MvPowerSeries.X i : MvPowerSeries τ C) = γ i := by
  unfold alongCv
  exact MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hγ) i

theorem mem_Cv_of_subst_X_pow : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g (m : ℕ), 0 < m → ∀ a : ((κ → PowerSeries C) × (JJ I g → PowerSeries C)), ((fun i => PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ m) (a.1 i), fun q => PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ m) (a.2 q)) : ((κ → PowerSeries C) × (JJ I g → PowerSeries C))) ∈ Cv X V g → a ∈ Cv X V g := by
  intro C _ V d _ I _ κ _ X H g m hm a ha
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ := ha
  have hγ0 : ∀ i, PowerSeries.constantCoeff (γ i) = 0 := fun i => (hγ i).1
  have hτ : PowerSeries.constantCoeff ((PowerSeries.X : PowerSeries C) ^ m) = 0 := by simp [hm.ne']
  have hS := PowerSeries.HasSubst.of_constantCoeff_zero' hτ
  have hlg : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0 := by
    intro i
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, H.lin i 0 (by simp)]
    simp
  have h1' : ∀ i, alongCv γ (X.lg i) = PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ m) (a.1 i) := h1
  have h2' : ∀ q, PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ m) (a.2 q) =
      lam q - alongCv γ (X.sg (X.u (1 - g) q)) := h2
  have ha0 : ∀ i, PowerSeries.constantCoeff (a.1 i) = 0 := by
    intro i
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← Formalism.L2.FormalSeriesBounds.coeff_subst_X_pow hm, ← h1' i, mul_zero,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact Formalism.L2.FormalSeriesBounds.constantCoeff_subst_zero (τ := Unit) hγ0 (hlg i)
  have hsub : ∀ i, PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ m) (alongCv a.1 (X.ex i)) = γ i := by
    intro i
    rw [← alongCv_repar ha0 hτ]
    have : (fun i => PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ m) (a.1 i)) =
        fun i => alongCv γ (X.lg i) := funext fun i => (h1' i).symm
    rw [this, cvRoot_alongCv_comp hγ0 hlg, H.exlg, cvRoot_alongCv_X hγ0]
  have hcv : IsCv V (fun i => alongCv a.1 (X.ex i)) := isCv_of_subst_X_pow V hm _ γ hγ hsub
  refine ⟨fun i => alongCv a.1 (X.ex i),
    fun q => a.2 q + alongCv (fun i => alongCv a.1 (X.ex i)) (X.sg (X.u (1 - g) q)), hcv,
    isCv_of_subst_X_pow V hm _ lam hlam ?_, ?_, ?_⟩
  · intro q
    rw [PowerSeries.subst_add hS, h2', ← alongCv_repar (fun i => (hcv i).1) hτ, funext hsub, sub_add_cancel]
  · intro i
    rw [cvRoot_alongCv_comp ha0 H.exc, H.lgex, cvRoot_alongCv_X ha0]
  · intro q
    simp

end GlobalTheory.RowLaw
