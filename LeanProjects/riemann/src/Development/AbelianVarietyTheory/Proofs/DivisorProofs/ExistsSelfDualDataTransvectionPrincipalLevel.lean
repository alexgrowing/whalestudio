import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRankOneCuspLatticeDataOfPrincipal
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsIntegralLevelMulKappa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelArithmeticGroupsContainCongruenceStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishingStatement
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.LevGeo

theorem gam_keeps_L' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r)
    (A : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hA : A ≠ 0)
    (hΛ : X.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ A, ∃ u ∈ X.L', v = a • u}) :
    ∀ γ ∈ X.Γ, ∀ v ∈ X.L', (γ : Matrix (Fin r) (Fin r) E).mulVec v ∈ X.L' := by
  have hinv : A⁻¹ * A = 1 := inv_mul_cancel₀ hA
  have hA1 : ∀ b ∈ A⁻¹, ∀ x ∈ X.Λ, b • x ∈ X.L' := by
    intro b hb x hx
    rw [hΛ] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, u, hu, rfl⟩ := hx
      have hm : b * a ∈ A⁻¹ * A := FractionalIdeal.mul_mem_mul hb ha
      rw [hinv, FractionalIdeal.mem_one_iff] at hm
      obtain ⟨z, hz⟩ := hm
      rw [smul_smul, ← hz, algebraMap_smul]
      exact X.L'.smul_mem z hu
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_comm]; exact X.L'.smul_mem c hx
  intro γ hγ v hv
  have key : ∀ y ∈ ((A⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) *
      (A : Submodule (𝓞 E) E), (γ : Matrix (Fin r) (Fin r) E).mulVec (y • v) ∈ X.L' := by
    intro y hy
    refine Submodule.mul_induction_on hy (fun b hb a ha => ?_) (fun y1 y2 h1 h2 => ?_)
    · have hav : a • v ∈ X.Λ := by
        rw [hΛ]; exact Submodule.subset_span ⟨a, ha, v, hv, rfl⟩
      have h1 := ((X.Γ_stab γ hγ).2 (a • v)).1 hav
      rw [mul_smul, Matrix.mulVec_smul]
      exact hA1 b hb _ h1
    · rw [add_smul, Matrix.mulVec_add]; exact add_mem h1 h2
  have h1 : (1 : E) ∈ ((A⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) *
      (A : Submodule (𝓞 E) E) := by
    rw [← FractionalIdeal.coe_mul, hinv]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
  have := key 1 h1
  rwa [one_smul] at this

theorem level_mul_two_div (m n d : ℝ) (hn : 0 < n) (hd : 0 < d) :
    m * (n * d) * (2 * (1 / (n * Real.sqrt d))) = 2 * m * Real.sqrt d := by
  have key : ∀ s : ℝ, 0 < s → s * s = d → m * (n * d) * (2 * (1 / (n * s))) = 2 * m * s := by
    intro s hs hss
    subst hss
    field_simp
  exact key _ (Real.sqrt_pos.2 hd) (Real.mul_self_sqrt hd.le)

theorem exists_dataX_transv : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ k : (U σ).Comp, ∃ Xx : DataX D.host.E D.R.r, Xx.toData = (U σ).X k ∧ Xx.g = l.M ∧ Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xx.L', v = a • u} ∧ (∀ γ ∈ Xx.Γ, ∀ v ∈ Xx.L', (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v ∈ Xx.L') ∧ ∃ M : ℝ, 0 < M ∧ M * Xx.k0 = 2 * l.M * Real.sqrt D.host.d ∧ ∀ v ∈ Xx.L', herm Xx.Gm v v = 0 → ∀ b : D.host.E, cc b = b → IsIntegral ℤ b → ∃ γ ∈ Xx.Γ, ∀ τ : Xx.Ψ, (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 = Xx.flowMat v τ ((M : ℂ) * τ.1 b) := by
  intro D j H Dw l Xo c U dict h σ hσ k
  have hP := GlobalTheory.T.principalLevel_arithmeticGroups_contain_congruence D j H Dw l Xo c U dict h σ hσ
  have hN : 0 < Ideal.absNorm D.host.ccK :=
    Nat.pos_of_ne_zero fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hd : 0 < D.host.d := by have := D.host.qd_big.2; omega
  have hN' : (0 : ℝ) < Ideal.absNorm D.host.ccK := by exact_mod_cast hN
  have hd' : (0 : ℝ) < D.host.d := by exact_mod_cast hd
  have hs := Real.sqrt_pos.2 hd'
  have hx1 : xiR D ≤ 1 := by
    rw [GlobalTheory.TransvModel.xiR_eq]
    have h1 : (1 : ℝ) ≤ Ideal.absNorm D.host.ccK := by exact_mod_cast hN
    have h2 : (1 : ℝ) ≤ Real.sqrt D.host.d := by
      rw [Real.one_le_sqrt]; exact_mod_cast hd
    rw [div_le_one (by positivity)]
    nlinarith
  have habs := h.xiAbs σ hσ k
  have hperf := GlobalTheory.traceForm_integral_perfect_of_isUnf _ _ _ _ _ _ σ _ (Formalism.L2.PjFree.Unf.ofPj (U σ))
    ((Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf σ hσ)) k
  have hξ := GlobalTheory.eq_or_eq_neg_of_purelyImaginary_of_norm_eq _ D.host.xi0 ((U σ).X k).ξ0 D.host.φ₀
    (GlobalTheory.LatticeData.flagDomainConj_hostXi_eq_neg D) ((U σ).X k).ξ0_im (habs _).symm
  have hone : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) ((U σ).X k).ξ0 * D.host.AA *
      D.host.AAbar * (differentIdeal ℤ (𝓞 D.host.E) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) = 1 := by
    have h1 := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
    rcases hξ with e | e
    · rw [e]; exact h1
    · rw [e, show -D.host.xi0 = (-1 : (𝓞 D.host.E)ˣ) • D.host.xi0 by simp,
        ← (FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨-1, rfl⟩)]
      exact h1
  have hA : D.host.AA ≠ 0 := by
    intro e
    rw [e] at hone
    simp at hone
  have hM : 0 < l.M := by have := l.three_le; omega
  obtain ⟨Xx, h1, h2, h3⟩ := GlobalTheory.exists_dataX_of_perfect_traceForm _ _ ((U σ).X k) D.host.AA D.host.AAbar
    (xiR D) l.M
    (fun a => by
      rw [GlobalTheory.LatticeData.cc_eq_conj]
      exact ⟨conj_mem_AA D, fun ha => by simpa only [conj_conj] using conj_mem_AAbar D ha⟩)
    hone habs hx1 hperf.1 hperf.2 hM (hP k)
  let Xy : DataX D.host.E D.R.r := { Xx with
    k0 := 2 * xiR D
    minWeight_pos := by have := GlobalTheory.TransvModel.xiR_eq D; rw [this]; positivity
    k0_le := by linarith
    ξ0_abs := fun τ => by rw [show Xx.ξ0 = ((U σ).X k).ξ0 from congrArg _ h1, habs]; ring }
  have hΛ : Xy.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xy.L', v = a • u} := h3
  have hX0 : Xy.toData = (U σ).X k := h1
  have habs' : ∀ τ : D.host.E →+* ℂ,
      ‖τ Xy.ξ0‖ = 1 / ((Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d) := fun τ => by
    rw [← GlobalTheory.TransvModel.xiR_eq, ← habs τ, ← hX0]
  refine ⟨Xy, h1, h2, h3, gam_keeps_L' Xy _ hA hΛ, ((l.M * (Ideal.absNorm D.host.ccK * D.host.d) : ℕ) : ℝ),
    by positivity, ?_, fun v hv hiso b hb hbi => ?_⟩
  · change _ * (2 * xiR D) = _
    rw [GlobalTheory.TransvModel.xiR_eq]
    push_cast
    exact level_mul_two_div _ _ _ hN' hd'
  · have := GlobalTheory.TransvModel.transv_mem_of_span Xy (D.host.AA : Set D.host.E) hΛ (Ideal.absNorm D.host.ccK * D.host.d)
      (GlobalTheory.TransvModel.isIntegral_level_mul_kappa Xy.toData hN hd D.host.φ₀ (habs' _)) v hv hiso b hb hbi
    have hg : Xy.g = l.M := h2
    rwa [hg] at this

end GlobalTheory.LevGeo
