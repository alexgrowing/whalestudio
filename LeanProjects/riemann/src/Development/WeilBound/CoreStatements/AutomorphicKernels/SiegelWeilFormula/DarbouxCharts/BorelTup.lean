import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DarbouxCharts.TChart
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnitaryChartEquiv.CEquivApply

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.Tunit

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

open PositivityTheory.SiegelWeilFormula.TBij.Adp PositivityTheory.SiegelWeilFormula.KTunit

local instance (priority := high) measTup' {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] :
    MeasurableSpace (κ → AF F) := borel _

local instance borelTup' {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] : BorelSpace (κ → AF F) := ⟨rfl⟩

private theorem integral_mul_star_eq_of_lintegral_norm_sq_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {u v u' v' : α → ℂ}
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) (hu' : MemLp u' 2 μ) (hv' : MemLp v' 2 μ)
    (h : ∀ k : ℂ, ∫⁻ x, ‖v x + k * u x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖v' x + k * u' x‖ₑ ^ 2 ∂μ) :
    ∫ x, u x * star (v x) ∂μ = ∫ x, u' x * star (v' x) ∂μ := by
  have hn : ∀ k : ℂ, ‖hv.toLp v + k • hu.toLp u‖ = ‖hv'.toLp v' + k • hu'.toLp u'‖ := by
    intro k
    rw [← MemLp.toLp_const_smul, ← MemLp.toLp_add, ← MemLp.toLp_const_smul, ← MemLp.toLp_add,
      Lp.norm_toLp, Lp.norm_toLp]
    congr 1
    rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num),
      eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
    congr 1
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact h k
  have hi : ∀ {a b : α → ℂ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ),
      ∫ x, a x * star (b x) ∂μ = inner ℂ (hb.toLp b) (ha.toLp a) := by
    intro a b ha hb
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x hxa hxb
    rw [hxa, hxb]
    simp [mul_comm]
  rw [hi hu hv, hi hu' hv', inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four]
  have e1 := hn 1
  have e2 := hn (-1)
  have e3 := hn (-RCLike.I)
  have e4 := hn RCLike.I
  simp only [one_smul, neg_smul, ← sub_eq_add_neg] at e1 e2 e3 e4
  rw [e1, e2, e3, e4]

theorem tUnit : TUnit := by
  intro F E _ _ _ _ _ σ d ν hν x Φ hΦ Φ' hΦ'
  obtain ⟨τ, S0, S0', C, hS, hT⟩ := T_chart d
  have hU := d.ok.dbl.weil.2.1
  have hom : ∀ Ψ ∈ d.sch, d.om x Ψ ∈ d.sch := fun Ψ hΨ => hU.pres x Ψ hΨ
  obtain ⟨hμ0, hmap⟩ := map_haar d τ ν hν
  set μ0 := Measure.map (cmap d τ) ν with hμ0def
  have key : ∀ Ψ ∈ d.sch, ∀ Ψ' ∈ d.sch, ∫ X, d.T Ψ X * star (d.T Ψ' X) ∂ν =
      ∫ y, (C * S0 Ψ y) * star (C * S0 Ψ' y) ∂μ0 := by
    intro Ψ hΨ Ψ' hΨ'
    rw [← hmap (fun y => (C * S0 Ψ y) * star (C * S0 Ψ' y))]
    refine integral_congr_ae (ae_of_all _ fun X => ?_)
    simp only [hT Ψ hΨ X, hT Ψ' hΨ' X]
    rfl
  have hN : ∀ Ψ ∈ d.sch, ∫⁻ y, ‖S0 (d.om x Ψ) y‖ₑ ^ 2 ∂μ0 = ∫⁻ y, ‖S0 Ψ y‖ₑ ^ 2 ∂μ0 := by
    obtain ⟨c, -, -, hc⟩ := hS.norm μ0 μ0 hμ0 hμ0
    intro Ψ hΨ
    rw [hc _ (hom Ψ hΨ), hc _ hΨ, hU.unit μ0 hμ0 x Ψ hΨ]
  have hL : ∀ Ψ ∈ d.sch, MemLp (fun y => C * S0 Ψ y) 2 μ0 := fun Ψ hΨ =>
    (schA_memLp_two F d.κ μ0 hμ0 _ (hS.pres Ψ hΨ)).const_mul C
  rw [key _ (hom Φ hΦ) _ (hom Φ' hΦ'), key _ hΦ _ hΦ']
  refine integral_mul_star_eq_of_lintegral_norm_sq_eq (hL _ (hom Φ hΦ)) (hL _ (hom Φ' hΦ')) (hL _ hΦ) (hL _ hΦ') fun k => ?_
  have hmem : Φ' + k • Φ ∈ d.sch := d.sch.add_mem hΦ' (d.sch.smul_mem k hΦ)
  have e1 : ∀ y, C * S0 (d.om x Φ') y + k * (C * S0 (d.om x Φ) y) = C * S0 (d.om x (Φ' + k • Φ)) y := by
    intro y
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have e2 : ∀ y, C * S0 Φ' y + k * (C * S0 Φ y) = C * S0 (Φ' + k • Φ) y := by
    intro y
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [e1, e2, enorm_mul, mul_pow]
  have hC : ‖C‖ₑ ^ 2 ≠ ⊤ := by simp
  rw [lintegral_const_mul' _ _ hC, lintegral_const_mul' _ _ hC, hN _ hmem]

end PositivityTheory.SiegelWeilFormula.Tunit

end
