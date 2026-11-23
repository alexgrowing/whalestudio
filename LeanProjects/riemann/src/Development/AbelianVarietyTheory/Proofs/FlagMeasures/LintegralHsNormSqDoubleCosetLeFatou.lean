import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFunctionalTwoSidedStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFolnerOverlapAverageTendstoFormStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HsNormSqIintLeLiminfStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormConvergesEquivariantHermitianStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompactStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsFolnerSequenceBesselStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselOpNormPowerIntegralLtTopClosedSubgroupStatement

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.FatouI

theorem lintegral_le_of_liminf {X : Type*} [MeasurableSpace X] (ν : Measure X) (F : X → ENNReal)
    (g : ℕ → X → ENNReal) (hg : ∀ j, Measurable (g j))
    (hF : ∀ᵐ γ ∂ν, F γ ≤ Filter.liminf (fun j => g j γ) Filter.atTop) (b : ℕ → ℝ) (L : ℝ)
    (hb : ∀ j, ∫⁻ γ, g j γ ∂ν = ENNReal.ofReal (b j))
    (hL : Filter.Tendsto b Filter.atTop (nhds L)) : ∫⁻ γ, F γ ∂ν ≤ ENNReal.ofReal L := by
  refine (lintegral_mono_ae hF).trans ((lintegral_liminf_le hg).trans ?_)
  simp_rw [hb]
  exact (ENNReal.tendsto_ofReal hL).liminf_eq.le

variable {k r : ℕ}

theorem measurable_besselTwoSidedAction_joint :
    Measurable fun q : Mt k r × (Mt k r × Mt k r) => act2 (Matrix.of q.1) q.2 := by
  let m : Mt k r × Mt k r → Mt k r := fun q => lmulM (Matrix.of q.1) q.2
  have hmul : Continuous m :=
    Continuous.matrix_mul (X := Mt k r × Mt k r) continuous_fst continuous_snd
  have hm : Measurable m := hmul.measurable
  have h1 : Measurable fun q : Mt k r × (Mt k r × Mt k r) => m (q.2.1, q.1) :=
    hm.comp (measurable_snd.fst.prodMk measurable_fst)
  have h2 : Measurable fun q : Mt k r × (Mt k r × Mt k r) => invM q.2.2 :=
    measurable_invM.comp measurable_snd.snd
  have h3 : Measurable fun q : Mt k r × (Mt k r × Mt k r) => m (m (q.2.1, q.1), invM q.2.2) :=
    hm.comp (h1.prodMk h2)
  exact h3

theorem hsNormSq_eq_sum {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) :
    hsNormSq A = ∑ i, ‖A (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

theorem DD_stable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (w : H) (hσ : IsURepOn (GG k r) σ) (hG : IsClosedSub k r (GG k r)) :
    ∀ g ∈ GG k r, ∀ v ∈ (DD σ w : Set H), σ g v ∈ (DD σ w : Set H) := by
  intro g hg v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨h, hh, rfl⟩ := hv
    have := mem_DD σ w (hG.2.2.2.1 g hg h hh)
    rw [hσ.1.2 g hg h hh] at this
    exact this
  | zero => simp
  | add u v _ _ hu hv => rw [map_add]; exact (DD σ w).add_mem hu hv
  | smul a v _ hv => rw [map_smul]; exact (DD σ w).smul_mem a hv

theorem integrable_coef {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (hσ : IsURepOn (GG k r) σ) {S : Set (Mat k r)} (hS : IsClosedSub k r S)
    {μ : Measure (Mt k r)} (hμ : IsHaarOn S μ) {a C : ℝ} (hfin : normInt μ a < ⊤) (u v : H)
    (hC : ∀ g ∈ GG k r, ‖coef σ u v g‖ ≤ C * opn g ^ (-a)) :
    Integrable (fun p : Mt k r => coef σ u v (Matrix.of p)) μ := by
  have hae : ∀ᵐ p ∂μ, (Matrix.of p : Mat k r) ∈ S := hμ.2.2.1
  have hSm : MeasurableSet {p : Mt k r | (Matrix.of p : Mat k r) ∈ S} :=
    IsClosed.measurableSet (α := Mt k r) hS.2.1
  refine ⟨?_, ?_⟩
  · have hc : ContinuousOn (fun p : Mt k r => coef σ u v (Matrix.of p))
        {p : Mt k r | (Matrix.of p : Mat k r) ∈ S} :=
      ContinuousOn.inner (𝕜 := ℂ) continuousOn_const ((hσ.2.2 u).mono hS.1)
    have := hc.aestronglyMeasurable (μ := μ) hSm
    rwa [Measure.restrict_eq_self_of_ae_mem (s := {p : Mt k r | (Matrix.of p : Mat k r) ∈ S}) hae] at this
  · refine lt_of_le_of_lt (b := ∫⁻ x, ENNReal.ofReal C * ENNReal.ofReal (opn (Matrix.of x) ^ (-a)) ∂μ)
      (lintegral_mono_ae ?_) ?_
    · filter_upwards [hae] with p hp
      rw [← ENNReal.ofReal_mul' (Real.rpow_nonneg (opn_nonneg _) _), ← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hC _ (hS.1 hp))
    · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

theorem dis_of_continuousOn {Ω S S' : Set (Mat k r)} {μG μS μS' ν : Measure (Mt k r)}
    (hG : IsClosedSub k r (GG k r)) (hS : IsClosedSub k r S) (hS' : IsClosedSub k r S')
    (hμG : IsHaarOn (GG k r) μG) (hμ : IsHaarOn S μS) (hμ' : IsHaarOn S' μS') (hΩ : Ω ⊆ GG k r)
    (hν : IsDis Ω μG μS μS' ν) (f : Mat k r → ℝ) (hf0 : ∀ g, 0 ≤ f g) (hf : ContinuousOn f (GG k r))
    (hfi : Integrable (fun g : Mt k r => f (Matrix.of g)) μG) :
    ∃ g : Mt k r → ENNReal, Measurable g ∧
      (∀ γ : Mt k r, Matrix.of γ ∈ Ω →
        g γ = ∫⁻ p, ENNReal.ofReal (f (Matrix.of (act2 (Matrix.of γ) p))) ∂(μS.prod μS')) ∧
      ∫⁻ γ, g γ ∂ν = ENNReal.ofReal (∫ g, f (Matrix.of g) ∂μG) := by
  classical
  haveI := hμ.1
  haveI := hμ'.1
  have hGm : MeasurableSet {p : Mt k r | (Matrix.of p : Mat k r) ∈ GG k r} :=
    IsClosed.measurableSet (α := Mt k r) hG.2.1
  let f0 : Mt k r → ℝ := {p : Mt k r | (Matrix.of p : Mat k r) ∈ GG k r}.piecewise
    (fun p => f (Matrix.of p)) (fun _ => 0)
  have hf0m : Measurable f0 :=
    ContinuousOn.measurable_piecewise (f := fun p : Mt k r => f (Matrix.of p)) hf continuousOn_const hGm
  have hf0e : ∀ p : Mt k r, Matrix.of p ∈ GG k r → f0 p = f (Matrix.of p) := fun p hp =>
    Set.piecewise_eq_of_mem _ _ _ hp
  have hF : Measurable fun p => ENNReal.ofReal (f0 p) := hf0m.ennreal_ofReal
  refine ⟨fun γ => ∫⁻ p, ENNReal.ofReal (f0 (act2 (Matrix.of γ) p)) ∂(μS.prod μS'), ?_, ?_, ?_⟩
  · exact (hF.comp measurable_besselTwoSidedAction_joint).lintegral_prod_right'
  · intro γ hγ
    have h1 : ∀ᵐ p ∂μS, (Matrix.of p : Mat k r) ∈ S := hμ.2.2.1
    have h2 : ∀ᵐ p ∂μS', (Matrix.of p : Mat k r) ∈ S' := hμ'.2.2.1
    have h1' := Measure.quasiMeasurePreserving_fst (μ := μS) (ν := μS') |>.ae h1
    have h2' := Measure.quasiMeasurePreserving_snd (μ := μS) (ν := μS') |>.ae h2
    refine lintegral_congr_ae ?_
    filter_upwards [h1', h2'] with p hp hp'
    rw [hf0e]
    exact hG.2.2.2.1 _ (hG.2.2.2.1 _ (hS.1 hp) _ (hΩ hγ)) _ (hG.2.2.2.2 _ (hS'.1 hp'))
  · rw [← hν.2.2 _ hF, ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall fun g => hf0 _)]
    have h1 : ∀ᵐ p ∂μG, (Matrix.of p : Mat k r) ∈ GG k r := hμG.2.2.1
    refine lintegral_congr_ae ?_
    filter_upwards [h1] with p hp
    rw [hf0e p hp]

end GlobalTheory.SgInf.FatouI

open GlobalTheory.SgInf.FatouI in

theorem GlobalTheory.SgInf.lintegral_hsNormSq_Iint_le : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (z' : Fin (2 * r + k + 1) → ℂ) (c' : Fin r → ℂ) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS' : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → Side z' π' μS' → ∀ ν : Measure (Mt k r), IsDis (Greg k r z z') μG μS μS' ν → ∀ x ∈ DD σ w, ∀ y ∈ DD σ w, ∀ (ξ : Wp) (ξ' : Wq), ∫⁻ γ, ENNReal.ofReal (hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π' μS μS' σ x y ξ ξ' (Matrix.of γ))) ∂ν ≤ ENNReal.ofReal (d⁻¹ * (⟪ξ, be (psiGen k r z c) π μS σ y y ξ⟫_ℂ).re * (⟪ξ', be (psiGen k r z' c') π' μS' σ x x ξ'⟫_ℂ).re) := by
  intro k r H _ _ _ Wp _ _ _ _ Wq _ _ _ _ σ w a μG d z c π μS z' c' π' μS' hStd hSd hSd' ν hν x hx y hy ξ ξ'
  obtain ⟨hG, -, -, hS, -⟩ := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hSd.1 hSd.2.1
  obtain ⟨-, -, -, hS', -⟩ := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z' hSd'.1 hSd'.2.1
  obtain ⟨Om, hOm⟩ := GlobalTheory.T.exists_isFolnerSequenceBessel k r z μS hSd.1 hSd.2.1 hSd.2.2.2.1
  obtain ⟨Om', hOm'⟩ := GlobalTheory.T.exists_isFolnerSequenceBessel k r z' μS' hSd'.1 hSd'.2.1 hSd'.2.2.2.1
  have hdec := hStd.2.2.2.2.2.2.2.1
  have ha : 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < a := by
    have h1 : (2 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by
      have := hStd.1
      exact_mod_cast (by omega : 2 ≤ 2 * r + k + 1)
    have h2 : ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < ((2 * r + k + 1 : ℕ) : ℝ) ^ 5 :=
      pow_lt_pow_right₀ (by linarith) (by norm_num)
    have := hStd.2.2.2.2.2.2.1
    linarith
  have hiy : Integrable (fun p : Mt k r => coef σ y y (Matrix.of p)) μS := by
    obtain ⟨C, hC⟩ := hdec y hy y hy
    exact integrable_coef σ hStd.2.1 hS hSd.2.2.2.1 (GlobalTheory.T.besselOpNormPowerIntegral_lt_top_closedSubgroup k r _ μS a hS hSd.2.2.2.1 ha) y y hC
  have hix : Integrable (fun p : Mt k r => coef σ x x (Matrix.of p)) μS' := by
    obtain ⟨C, hC⟩ := hdec x hx x hx
    exact integrable_coef σ hStd.2.1 hS' hSd'.2.2.2.1 (GlobalTheory.T.besselOpNormPowerIntegral_lt_top_closedSubgroup k r _ μS' a hS' hSd'.2.2.2.1 ha) x x hC
  have h62 := fun j => GlobalTheory.T.bessel_functional_two_sided k r σ w a μG d z c π μS z' c' π' μS' hStd hSd hSd' x y ξ ξ' (Om j) (Om' j)
    (hOm.1 j).1 (hOm'.1 j).1 (hOm.1 j).2.2.2.2 (hOm'.1 j).2.2.2.2 hiy hix
  have h63 := GlobalTheory.T.besselFolner_overlap_average_tendsto_form k r σ w a μG d z c π μS hStd hSd Om hOm y hy ξ
  have h63' := GlobalTheory.T.besselFolner_overlap_average_tendsto_form k r σ w a μG d z' c' π' μS' hStd hSd' Om' hOm' x hx ξ'
  have h64 := GlobalTheory.T.hsNormSq_Iint_le_liminf_alt k r σ w a μG d z c π μS z' c' π' μS' hStd hSd hSd' Om Om' hOm hOm' x hx y hy ξ ξ'
  have hadj := (GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSd (DD σ w) (DD_stable σ w hStd.2.1 hG) hdec
    y hy y hy).2.2.1
  have him : (⟪ξ, be (psiGen k r z c) π μS σ y y ξ⟫_ℂ).im = 0 := by
    rw [← Complex.conj_eq_iff_im, inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right, hadj]
  have hcont : Continuous (hsNormSq : (Wq →L[ℂ] Wp) → ℝ) := by
    have : (hsNormSq : (Wq →L[ℂ] Wp) → ℝ) = fun A => ∑ i, ‖A (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 :=
      funext hsNormSq_eq_sum
    rw [this]
    fun_prop
  have hnn : ∀ A : Wq →L[ℂ] Wp, 0 ≤ hsNormSq A := fun A => by
    rw [hsNormSq_eq_sum]; positivity
  have hdis := fun j => dis_of_continuousOn hG hS hS' hStd.2.2.2.2.1 hSd.2.2.2.1 hSd'.2.2.2.1
    (Greg_subset z z') hν (fun g => hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π'
      (μS.restrict (Om j)) (μS'.restrict (Om' j)) σ x y ξ ξ' g)) (fun g => hnn _)
      (hcont.comp_continuousOn (h62 j).1) (h62 j).2.1
  choose g hgm hge hgi using hdis
  have hpos : ∀ j, 0 < (μS (Om j)).toReal := fun j =>
    ENNReal.toReal_pos (hOm.1 j).2.2.2.1.ne' (hOm.1 j).2.2.2.2.ne
  have hpos' : ∀ j, 0 < (μS' (Om' j)).toReal := fun j =>
    ENNReal.toReal_pos (hOm'.1 j).2.2.2.1.ne' (hOm'.1 j).2.2.2.2.ne
  refine lintegral_le_of_liminf ν _ (fun j γ => g j γ / (μS (Om j) * μS' (Om' j)))
    (fun j => (hgm j).div_const _) ?_
    (fun j => (∫ g, hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π'
      (μS.restrict (Om j)) (μS'.restrict (Om' j)) σ x y ξ ξ' (Matrix.of g)) ∂μG) /
        ((μS (Om j)).toReal * (μS' (Om' j)).toReal)) _ ?_ ?_
  · have h1 : ∀ᵐ γ ∂ν, (Matrix.of γ : Mat k r) ∈ Greg k r z z' := hν.2.1
    filter_upwards [h1] with γ hγ
    simp_rw [fun j => hge j γ hγ]
    exact h64 _ hγ
  · intro j
    simp_rw [div_eq_mul_inv (g j _)]
    rw [lintegral_mul_const _ (hgm j), hgi j, ENNReal.ofReal_div_of_pos (mul_pos (hpos j) (hpos' j)),
      ENNReal.ofReal_mul (hpos j).le, ENNReal.ofReal_toReal (hOm.1 j).2.2.2.2.ne,
      ENNReal.ofReal_toReal (hOm'.1 j).2.2.2.2.ne, div_eq_mul_inv]
  · have hT := (Complex.continuous_re.tendsto _).comp ((h63.const_mul ((d : ℂ)⁻¹)).mul h63')
    convert hT using 2 with j
    · have e := (h62 j).2.2
      rw [Function.comp_apply, ← mul_div_assoc (d : ℂ)⁻¹, div_mul_div_comm, ← e]
      norm_cast
    · rw [← Complex.ofReal_inv, mul_assoc (_ : ℂ), Complex.re_ofReal_mul, Complex.mul_re, him]
      ring
