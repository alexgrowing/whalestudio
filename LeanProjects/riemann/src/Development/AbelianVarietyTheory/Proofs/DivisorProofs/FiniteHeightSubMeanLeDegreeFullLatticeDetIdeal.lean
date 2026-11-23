import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulDetSpanSupLeDetSpanLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaxIdealSmulMemOfLtOfRelIndexNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexSupSpanSingletonEqAbsNormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexIdealSmulFractionalIdealEqAbsNormNumberFStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasisDetIntegralSpanEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSpanCommonDenominatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermFamGramDetEqNormSqBasisDetMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLogFinitePlaceEqNegLogAbsNormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLogGaussAbsLeFractionalIdealIndexStatement
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HSShort.DetIdeal

theorem detSpan_relIndex_le : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (d : ℕ) (β : Module.Basis (Fin d) F V) (N₀ N : Submodule (𝓞 F) V), N₀ ≤ N → N₀.toAddSubgroup.relIndex N.toAddSubgroup ≠ 0 → Submodule.span (𝓞 F) {y | ∃ w : Fin d → V, (∀ i, w i ∈ N₀) ∧ y = β.det w} ≠ ⊥ → (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ y ∈ Submodule.span (𝓞 F) {y | ∃ w : Fin d → V, (∀ i, w i ∈ N) ∧ y = β.det w}, c • y ∈ (1 : Submodule (𝓞 F) F)) → (Submodule.span (𝓞 F) {y | ∃ w : Fin d → V, (∀ i, w i ∈ N₀) ∧ y = β.det w}).toAddSubgroup.relIndex (Submodule.span (𝓞 F) {y | ∃ w : Fin d → V, (∀ i, w i ∈ N) ∧ y = β.det w}).toAddSubgroup ≤ N₀.toAddSubgroup.relIndex N.toAddSubgroup := by
  intro F V _ _ _ _ _ _ d β N₀ N hle hidx hne hbdd
  classical
  set A : Submodule (𝓞 F) V → Submodule (𝓞 F) F :=
    fun P => Submodule.span (𝓞 F) {y | ∃ w : Fin d → V, (∀ i, w i ∈ P) ∧ y = β.det w} with hA
  have hmono : ∀ P P' : Submodule (𝓞 F) V, P ≤ P' → A P ≤ A P' := fun P P' h =>
    Submodule.span_mono fun y ⟨w, hw, hy⟩ => ⟨w, fun i => h (hw i), hy⟩
  show (A N₀).toAddSubgroup.relIndex (A N).toAddSubgroup ≤ N₀.toAddSubgroup.relIndex N.toAddSubgroup
  obtain ⟨c, hc0, hc⟩ := hbdd
  induction hn : N₀.toAddSubgroup.relIndex N.toAddSubgroup using Nat.strong_induction_on generalizing N₀ with
  | _ n ih =>
  rcases eq_or_lt_of_le hle with rfl | hlt
  · rw [AddSubgroup.relIndex_self]
    omega
  obtain ⟨u, p, hp, huN, hu0, hpu⟩ := GlobalTheory.T.exists_maximalIdeal_smul_mem_of_lt_of_relIndex_ne_zero F V N₀ N hlt hidx
  set N₁ := N₀ ⊔ Submodule.span (𝓞 F) {u} with hN₁
  have h01 : N₀ ≤ N₁ := le_sup_left
  have h1N : N₁ ≤ N := sup_le hle ((Submodule.span_singleton_le_iff_mem _ _).mpr huN)
  have hidx01 := GlobalTheory.T.relIndex_sup_span_singleton_eq_absNorm_of_isMaximal F V N₀ u p hp hu0 hpu
  have hmul := AddSubgroup.relIndex_mul_relIndex N₀.toAddSubgroup N₁.toAddSubgroup N.toAddSubgroup
    (Submodule.toAddSubgroup_mono h01) (Submodule.toAddSubgroup_mono h1N)
  rw [hidx01] at hmul
  have hpN : Ideal.absNorm p ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hmul; exact hidx hmul.symm
  have hp1 : 1 < Ideal.absNorm p := by
    rcases Nat.lt_or_ge 1 (Ideal.absNorm p) with h | h
    · exact h
    · exfalso
      have : Ideal.absNorm p = 1 := by omega
      exact hp.ne_top (Ideal.absNorm_eq_one_iff.mp this)
  have hidx1 : N₁.toAddSubgroup.relIndex N.toAddSubgroup ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hmul; exact hidx hmul.symm
  have hlt' : N₁.toAddSubgroup.relIndex N.toAddSubgroup < n := by
    rw [← hn, ← hmul]
    exact lt_mul_left (Nat.pos_of_ne_zero hidx1) hp1
  have hne1 : A N₁ ≠ ⊥ := fun h => hne (le_bot_iff.mp (h ▸ hmono _ _ h01))
  have ih' := ih _ hlt' N₁ h1N hidx1 hne1 rfl

  have hpA : p • A N₁ ≤ A N₀ := by
    rw [Submodule.smul_le]
    intro π hπ y hy
    exact GlobalTheory.T.smul_detSpan_sup_le_detSpan_lattice F V d β N₀ u π (hpu π hπ) y hy
  have hp0 : p ≠ ⊥ := by
    rintro rfl; exact hpN (by simp)
  have hfr := GlobalTheory.T.relIndex_ideal_smul_fractionalIdeal_eq_absNorm_numberField F (A N₁) p hp0 hne1 ⟨c, hc0, fun y hy => hc y (hmono _ _ h1N hy)⟩
  have hstep : (A N₀).toAddSubgroup.relIndex (A N₁).toAddSubgroup ≤ Ideal.absNorm p := by
    rw [← hfr]
    exact AddSubgroup.relIndex_le_of_le_left (Submodule.toAddSubgroup_mono hpA) (by rw [hfr]; exact hpN)
  have hmulA := AddSubgroup.relIndex_mul_relIndex (A N₀).toAddSubgroup (A N₁).toAddSubgroup (A N).toAddSubgroup
    (Submodule.toAddSubgroup_mono (hmono _ _ h01)) (Submodule.toAddSubgroup_mono (hmono _ _ h1N))
  rw [← hmulA, ← hn, ← hmul]
  exact Nat.mul_le_mul hstep ih'

theorem finPart_sub_mean_le_deg : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (nm : HermFam F V) (M : Submodule (𝓞 F) V) (d : ℕ) (b : Module.Basis (Fin d) F V), IsFull M → ∀ (τ : Type) (g : MvPolynomial τ F), g ≠ 0 → (∀ m, coeff m g ∈ Submodule.span (𝓞 F) {y | ∃ v : Fin d → V, (∀ i, v i ∈ M) ∧ y = b.det v}) → finPart g - mean F (fun σ => Real.log (nm.gram σ b).det.re) / 2 ≤ deg nm M := by
  intro F V _ _ _ _ _ _ nm M d b hM τ g hg hcoef
  classical
  have hfg := hM.fg
  have hsp := hM.span
  obtain ⟨r, v, hv⟩ : ∃ (r : ℕ) (v : Fin r → V), IsFrame F M v := ⟨_, exists_isFrame M hfg⟩
  have hspan : ⊤ ≤ Submodule.span F (Set.range v) := by
    rw [← hsp]
    exact Submodule.span_le.mpr hv.2.2
  let β : Module.Basis (Fin r) F V := Module.Basis.mk hv.2.1 hspan
  have hβ : ⇑β = v := Module.Basis.coe_mk _ _
  obtain rfl : r = d := by simpa using Fintype.card_congr (β.indexEquiv b)
  set δ := b.det v with hδ
  have hδ0 : δ ≠ 0 := by
    have := (b.isUnit_det β).ne_zero
    rwa [hβ] at this
  set L := Submodule.span (𝓞 F) (Set.range v) with hL
  set B := Submodule.span (𝓞 F) {y | ∃ w : Fin r → V, (∀ i, w i ∈ M) ∧ y = β.det w} with hB

  have hdet : ∀ w : Fin r → V, b.det w = δ * β.det w := fun w => by
    rw [hδ, ← hβ, Module.Basis.det_apply, Module.Basis.det_apply, Module.Basis.det_apply, ← Matrix.det_mul,
      Module.Basis.toMatrix_mul_toMatrix]
  have hcoef' : ∀ m, coeff m g / δ ∈ B := fun m => by
    let φ : F →ₗ[𝓞 F] F := (LinearMap.mulLeft F δ⁻¹).restrictScalars (𝓞 F)
    have hmap : (Submodule.span (𝓞 F) {y | ∃ v : Fin r → V, (∀ i, v i ∈ M) ∧ y = b.det v}).map φ ≤ B := by
      rw [Submodule.map_span_le]
      rintro _ ⟨w, hw, rfl⟩
      have : φ (b.det w) = β.det w := by
        simp only [φ, LinearMap.restrictScalars_apply, LinearMap.mulLeft_apply, hdet]
        field_simp
      rw [this]
      exact Submodule.subset_span ⟨w, hw, rfl⟩
    have := hmap (Submodule.mem_map_of_mem (f := φ) (hcoef m))
    simpa [φ, div_eq_inv_mul] using this
  have hLM : L ≤ M := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hv.1 i)
  have hidx : L.toAddSubgroup.relIndex M.toAddSubgroup ≠ 0 := hv.relIndex_ne_zero hfg
  have hbase := GlobalTheory.T.span_basis_det_integral_eq_one F V r β
  rw [hβ] at hbase
  have hbdd := GlobalTheory.T.exists_common_denominator_span_det F V r β M hfg
  have hind := detSpan_relIndex_le F V r β L M hLM hidx (by rw [hbase]; intro h; have h1 : (1 : F) ∈ (1 : Submodule (𝓞 F) F) := Submodule.one_le.mp le_rfl; rw [h] at h1; simp at h1) hbdd
  rw [hbase] at hind
  have h1B : (1 : Submodule (𝓞 F) F) ≤ B := by
    rw [← hbase]
    exact Submodule.span_mono fun y ⟨w, hw, hy⟩ => ⟨w, fun i => hLM (hw i), hy⟩
  have hgauss := GlobalTheory.T.finsum_log_gaussAbs_le_fractionalIdeal_index F τ g hg B δ hδ0 h1B hbdd hcoef'
  have hprod := GlobalTheory.T.finsum_log_finitePlace_eq_neg_log_abs_norm' F δ hδ0
  have hn : (0 : ℝ) < Module.finrank ℚ F := by exact_mod_cast Module.finrank_pos

  have hG : ∀ σ : F →+* ℂ, Real.log (nm.gram σ v).det.re = Real.log (Complex.normSq (σ δ)) + Real.log (nm.gram σ b).det.re := by
    intro σ
    rw [GlobalTheory.T.hermFam_gram_det_eq_normSq_basis_det_mul F V nm σ r b v, ← hδ]
    have hpos : 0 < (nm.gram σ ⇑b).det.re := by
      have := (nm.posDef σ r b b.linearIndependent).det_pos
      exact (Complex.pos_iff.mp this).1
    have hn0 : 0 < Complex.normSq (σ δ) := Complex.normSq_pos.mpr ((map_ne_zero σ).mpr hδ0)
    rw [Complex.re_ofReal_mul, Real.log_mul hn0.ne' hpos.ne']
  have hsum := ds_sum_log_normSq_embeddings δ hδ0
  rw [arakelovDegree_eq_degreeOfFamily nm hfg hv, degreeOfFamily, finPart, mean]
  simp only [hG, Finset.sum_add_distrib, hsum]
  have hlog : Real.log ((1 : Submodule (𝓞 F) F).toAddSubgroup.relIndex B.toAddSubgroup : ℝ) ≤ Real.log (L.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) := by
    rcases Nat.eq_zero_or_pos ((1 : Submodule (𝓞 F) F).toAddSubgroup.relIndex B.toAddSubgroup) with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hidx)
    · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hind)
  have hkey : ∑ᶠ q : FinitePlace F, Real.log (gaussAbs q g) ≤
      Real.log (L.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) - Real.log |((Algebra.norm ℚ δ : ℚ) : ℝ)| := by
    linarith
  calc _ = ((∑ᶠ q : FinitePlace F, Real.log (gaussAbs q g)) - (∑ σ : F →+* ℂ, Real.log (nm.gram σ ⇑b).det.re) / 2) /
        (Module.finrank ℚ F : ℝ) := by ring
    _ ≤ (Real.log (L.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) - 1 / 2 * (2 * Real.log |((Algebra.norm ℚ δ : ℚ) : ℝ)| +
        ∑ σ : F →+* ℂ, Real.log (nm.gram σ ⇑b).det.re)) / (Module.finrank ℚ F : ℝ) := by
      apply div_le_div_of_nonneg_right _ hn.le
      linarith
    _ = _ := by ring

end GlobalTheory.HSShort.DetIdeal
