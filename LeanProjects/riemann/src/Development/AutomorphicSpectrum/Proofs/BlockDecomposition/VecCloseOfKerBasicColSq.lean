import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.VecClose

open PositivityTheory.Rg.BcB.E1

noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.KernelColumns

theorem ker_sub_of_kerBasic (hK : KerBasic) (X : Ctx) {φ φ' : X.G → ℂ} (h : Tst φ) (h' : Tst φ')
    (x y : X.G) :
    ker X.Γ (fun z => φ z - φ' z) x y = ker X.Γ φ x y - ker X.Γ φ' x y := by
  unfold ker
  exact finsum_sub_distrib ((hK X φ h).1 x y) ((hK X φ' h').1 x y)

theorem enorm_sq_Lp_two {α : Type*} [MeasurableSpace α] (ν : Measure α) (f : Lp ℂ 2 ν) :
    ‖f‖ₑ ^ 2 = ∫⁻ z, ‖(f : α → ℂ) z‖ₑ ^ 2 ∂ν := by
  rw [Lp.enorm_def]
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := (f : α → ℂ)) (μ := ν) (p := 2) (by norm_num)
  simpa using h

theorem enorm_sq_piLp_two {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] (f : PiLp 2 E) :
    ‖f‖ₑ ^ 2 = ∑ l, ‖f l‖ₑ ^ 2 := by
  have h : ‖f‖₊ ^ 2 = ∑ l, ‖f l‖₊ ^ 2 := by
    apply NNReal.coe_injective
    push_cast
    simpa using PiLp.norm_sq_eq_of_L2 E f
  simp only [enorm_eq_nnnorm]
  exact_mod_cast congrArg (fun t : NNReal => (t : ℝ≥0∞)) h

theorem vecClose_of_kerBasic_colSq : KerBasic → ColSq → VecClose := by
  intro hK hC X ι _ Φ Φ' Ω ε y j k k' hΩ hΦ hk hk'
  set R : ℝ≥0∞ := ENNReal.ofReal ε ^ 2 * X.μ Ω⁻¹ * cnt X.Γ (Ω⁻¹ * Ω) y with hR
  have key : ∀ l, ‖(k - k') l‖ₑ ^ 2 ≤ R := by
    intro l
    obtain ⟨t, t', s, s', hd⟩ := hΦ l
    have hT : Tst (fun z => Φ l j z - Φ' l j z) :=
      ⟨t.1.sub t'.1, t.2.sub t'.2⟩
    have hS : Function.support (fun z => Φ l j z - Φ' l j z) ⊆ Ω := by
      intro z hz
      by_contra hn
      have h1 : Φ l j z = 0 := by
        by_contra h0
        exact hn (s h0)
      have h2 : Φ' l j z = 0 := by
        by_contra h0
        exact hn (s' h0)
      exact hz (by simp [h1, h2])
    have hcol := hC X (fun z => Φ l j z - Φ' l j z) ε Ω hT hd hΩ hS y
    have hae : ((k l - k' l : Lp ℂ 2 X.ν) : X.G → ℂ) =ᵐ[X.ν]
        fun z => ker X.Γ (fun w => Φ l j w - Φ' l j w) z y := by
      filter_upwards [Lp.coeFn_sub (k l) (k' l), hk l, hk' l] with z h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3, ker_sub_of_kerBasic hK X t t']
    have hsub : (k - k') l = k l - k' l := rfl
    rw [hsub, enorm_sq_Lp_two]
    calc ∫⁻ z, ‖((k l - k' l : Lp ℂ 2 X.ν) : X.G → ℂ) z‖ₑ ^ 2 ∂X.ν
        = ∫⁻ z, ‖ker X.Γ (fun w => Φ l j w - Φ' l j w) z y‖ₑ ^ 2 ∂X.ν :=
          lintegral_congr_ae (hae.mono fun z hz => congrArg (fun w : ℂ => ‖w‖ₑ ^ 2) hz)
      _ ≤ R := hcol
  rw [enorm_sq_piLp_two]
  calc ∑ l, ‖(k - k') l‖ₑ ^ 2 ≤ ∑ _l : ι, R := Finset.sum_le_sum fun l _ => key l
    _ = Fintype.card ι * R := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end GlobalTheory.CompanionTheory.KernelColumns

end
