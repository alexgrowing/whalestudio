import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaMatrixCoeffRapidDecayRealFunctional
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff Topology

noncomputable section

namespace GlobalTheory.HeisTaylor

open GlobalTheory.OrientedHeis GlobalTheory.Size

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

def supN (φ : WO S T → ℂ) : ℝ≥0∞ := ⨆ w, ‖φ w‖ₑ

theorem enorm_le_supN (φ : WO S T → ℂ) (w : WO S T) : ‖φ w‖ₑ ≤ supN φ := le_iSup (fun w => ‖φ w‖ₑ) w

theorem supN_add_le (φ φ' : WO S T → ℂ) : supN (φ + φ') ≤ supN φ + supN φ' :=
  iSup_le fun w => (enorm_add_le _ _).trans (add_le_add (enorm_le_supN φ w) (enorm_le_supN φ' w))

theorem supN_smul (c : ℂ) (φ : WO S T → ℂ) : supN (c • φ) = ‖c‖ₑ * supN φ := by
  simp only [supN, Pi.smul_apply, smul_eq_mul, enorm_mul, ENNReal.mul_iSup]

theorem supN_heisO (hψ : IsStdChar D ψ (-1)) (u : WO S T) (φ : WO S T → ℂ) : supN (heisO ψ S T u φ) = supN φ := by
  unfold supN heisO
  have e : ∀ w, ‖ψ (symplOH S T w u) * φ (w + u)‖ₑ = ‖φ (w + u)‖ₑ := fun w => by
    rw [enorm_mul, ← ofReal_norm_eq_enorm (ψ _), hψ.1.2.1, ENNReal.ofReal_one, one_mul]
  simp only [e]
  exact (Equiv.addRight u).iSup_comp (g := fun w => ‖φ w‖ₑ)

theorem supN_ne_top (hψ : IsStdChar D ψ (-1)) {φ : WO S T → ℂ} (h : IsThetaFunO ψ S T φ) : supN φ ≠ ⊤ := by
  obtain ⟨C, hC⟩ := theta_bounded hψ h
  refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := C)) (iSup_le fun w => ?_)
  rw [← ofReal_norm_eq_enorm]
  exact ENNReal.ofReal_le_ofReal (hC w)

theorem heisO_add' (u : WO S T) (φ φ' : WO S T → ℂ) : heisO ψ S T u (φ + φ') = heisO ψ S T u φ + heisO ψ S T u φ' := by
  funext w; simp only [heisO, Pi.add_apply, mul_add]

theorem heisO_sub' (u : WO S T) (φ φ' : WO S T → ℂ) : heisO ψ S T u (φ - φ') = heisO ψ S T u φ - heisO ψ S T u φ' := by
  funext w; simp only [heisO, Pi.sub_apply, mul_sub]

theorem heisO_smul' (u : WO S T) (c : ℂ) (φ : WO S T → ℂ) : heisO ψ S T u (c • φ) = c • heisO ψ S T u φ := by
  funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring

theorem supN_le_ofReal {φ : WO S T → ℂ} {C : ℝ} (h : ∀ w, ‖φ w‖ ≤ C) : supN φ ≤ ENNReal.ofReal C :=
  iSup_le fun w => by
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (h w)

theorem tendsto_supN_heisO (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    Filter.Tendsto (fun u : WO S T => supN (heisO ψ S T u f - f)) (𝓝 0) (𝓝 0) := by
  obtain ⟨i1, -, -, -, -, K, hK, hc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have hcont : Continuous (Function.uncurry fun u w : WO S T => heisO ψ S T u f w) :=
    (hψ.1.1.comp (continuous_symplOH continuous_snd continuous_fst)).mul
      (hf.cont.comp (continuous_snd.add continuous_fst))
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  obtain ⟨r, -, hr0, hr⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  obtain ⟨v, hv, h⟩ := hK.mem_uniformity_of_prod (s := Set.univ) hcont.continuousOn (Set.mem_univ 0)
    (Metric.dist_mem_uniformity (ENNReal.ofReal_pos.1 hr0))
  rw [nhdsWithin_univ] at hv
  filter_upwards [hv] with u hu
  refine (supN_le_ofReal fun w => ?_).trans hr.le
  obtain ⟨γ, hγ, hw⟩ := hc w
  rw [← theta_norm_periodic hψ (theta_sub (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf u) hf) γ hγ w]
  have := h u hu _ hw
  rw [GlobalTheory.OrientedHeis.heisO_zero, Set.mem_setOf_eq, dist_eq_norm] at this
  exact this.le

def rem (ψ : AddChar (AF D.host.F) ℂ) (L : ℝ →+ WO S T) (t : ℝ) (f : WO S T → ℂ) : WO S T → ℂ :=
  (t⁻¹ : ℂ) • (heisO ψ S T (L t) f - f) - dLine ψ S T L f

theorem theta_rem (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) {L : ℝ →+ WO S T} (hL : IsRealDir T S L)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (t : ℝ) : IsThetaFunO ψ S T (rem ψ L t f) :=
  theta_sub (theta_smul _ (theta_sub (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf _) hf)) (theta_dLine hθ hψ hL hf)

theorem tendsto_supN_rem (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) {L : ℝ →+ WO S T} (hL : IsRealDir T S L)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    Filter.Tendsto (fun t : ℝ => supN (rem ψ L t f)) (𝓝[≠] 0) (𝓝 0) := by
  let L' : ℝ →+ WO S T := L.comp (negAddMonoidHom : ℝ →+ ℝ)
  have hL' : IsRealDir T S L' := ⟨hL.1.comp continuous_neg, fun t => hL.2 (-t)⟩
  have hd : dLine ψ S T L' f = -dLine ψ S T L f := by
    funext w
    have := deriv_comp_neg (fun t : ℝ => heisO ψ S T (L t) f w) 0
    rw [neg_zero] at this
    exact this
  obtain ⟨C, hC⟩ := quotient_bound hθ hψ hL hf
  obtain ⟨C', hC'⟩ := quotient_bound hθ hψ hL' hf
  have hb : ∀ t : ℝ, t ≠ 0 → ∀ w, ‖rem ψ L t f w‖ ≤ (|C| + |C'|) * |t| := by
    intro t ht w
    rcases lt_or_gt_of_ne ht with h | h
    · have h1 := hC' (-t) (neg_pos.2 h) w
      have e : (((-t : ℝ) : ℂ)⁻¹ • (heisO ψ S T (L' (-t)) f - f) - dLine ψ S T L' f) w = -rem ψ L t f w := by
        have e1 : L' (-t) = L t := congrArg L (neg_neg t)
        rw [hd, e1]
        simp only [rem, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Complex.ofReal_neg, inv_neg]
        ring
      rw [e, norm_neg] at h1
      rw [abs_of_neg h]
      nlinarith [le_abs_self C', abs_nonneg C]
    · have h1 := hC t h w
      rw [abs_of_pos h]
      refine h1.trans ?_
      nlinarith [le_abs_self C, abs_nonneg C']
  have hc : Continuous fun t : ℝ => ENNReal.ofReal ((|C| + |C'|) * |t|) :=
    ENNReal.continuous_ofReal.comp (by fun_prop)
  have ht := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  simp only [abs_zero, mul_zero, ENNReal.ofReal_zero] at ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht (.of_forall fun _ => zero_le)
    (eventually_nhdsWithin_of_forall fun t h => supN_le_ofReal (hb t h))

theorem eq_zero_of_tendsto (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) {L : ℝ →+ WO S T} (hL : IsRealDir T S L)
    {ι : Type} {l : Filter ι} [l.NeBot] {h : ι → WO S T → ℂ} (hh : ∀ i, IsThetaFunO ψ S T (h i)) {Λ : WO S T → ℂ}
    (h0 : Filter.Tendsto (fun i => supN (h i)) l (𝓝 0))
    (h1 : Filter.Tendsto (fun i => supN (dLine ψ S T L (h i) - Λ)) l (𝓝 0)) : Λ = 0 := by
  funext p
  have key := hasDerivAt_of_tendstoUniformly (l := l) (f := fun i s => heisO ψ S T (L s) (h i) p) (g := fun _ => 0)
    (f' := fun i s => heisO ψ S T (L s) (dLine ψ S T L (h i)) p) (g' := fun s => heisO ψ S T (L s) Λ p) ?_
    (.of_forall fun i s => hasDerivAt_heisO hθ hψ hL (hh i) p s) (fun s => ?_) 0
  · have := key.unique (hasDerivAt_const _ _)
    rwa [map_zero, GlobalTheory.OrientedHeis.heisO_zero] at this
  · refine EMetric.tendstoUniformly_iff.2 fun ε hε => ?_
    filter_upwards [h1.eventually (gt_mem_nhds hε)] with i hi s
    rw [edist_comm, edist_eq_enorm_sub]
    refine lt_of_le_of_lt ?_ hi
    rw [← supN_heisO hψ (L s), heisO_sub']
    exact enorm_le_supN _ p
  · refine tendsto_iff_edist_tendsto_0.2
      (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => zero_le) fun i => ?_)
    rw [edist_zero_right, ← supN_heisO hψ (L s)]
    exact enorm_le_supN _ p

def cc (θ : InfFam D) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (u : WO S T) : ℂ :=
  -(2 * Real.pi * Complex.I) * (GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt S T τ z (compAt θ τ u) : ℂ)

theorem continuous_cc (hθ : IsInfFam θ) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    Continuous (cc θ τ z : WO S T → ℂ) := by
  have h := GlobalTheory.RealWeil.continuous_compAt hθ τ T.rank S.rank
  refine continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul
    (Complex.continuous_re.comp (continuous_const.mul ?_))))
  exact (((continuous_const.matrix_mul h.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul
    continuous_const).matrix_trace

theorem cc_add (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (u v : WO S T) :
    cc θ τ z (u + v) = cc θ τ z u + cc θ τ z v := by
  have e : compAt θ τ (u + v) = compAt θ τ u + compAt θ τ v := by
    ext i j
    show θ τ (infPart D (u i j + v i j)) = θ τ (infPart D (u i j)) + θ τ (infPart D (v i j))
    rw [RingHom.map_add, RingHom.map_add]
  simp only [cc, GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt, GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.hermAt, e, conjTranspose_add, Matrix.mul_add, Matrix.add_mul,
    trace_add, mul_add, Complex.add_re, Complex.ofReal_add]

theorem cc_zero (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) : cc θ τ z (0 : WO S T) = 0 := by
  have := cc_add (θ := θ) τ z (0 : WO S T) 0
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem cc_line (hθ : IsInfFam θ) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {L : ℝ →+ WO S T}
    (hL : Continuous L) (t : ℝ) : cc θ τ z (L t) = t * cc θ τ z (L 1) := by
  have := map_real_smul ((AddMonoidHom.mk' (cc θ τ z : WO S T → ℂ) (cc_add τ z)).comp L)
    ((continuous_cc hθ τ z).comp hL) t 1
  rw [smul_eq_mul, mul_one, Complex.real_smul] at this
  exact this

theorem word_smul (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) (c : ℂ) (f : WO S T → ℂ) :
    wordAct (heisDer ψ θ) l (c • f) = c • wordAct (heisDer ψ θ) l f :=
  wordAct_rel (R := fun g g' => g = c • g') l (fun a _ _ _ e => e ▸ dRho_smul a.1 _ c _) rfl

theorem word_add (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool))
    {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
    wordAct (heisDer ψ θ) l (f + g) = wordAct (heisDer ψ θ) l f + wordAct (heisDer ψ θ) l g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [wordAct_cons, ih]
    exact dRho_add hψ hθ a.1 _ (theta_word hψ hθ l hf) (theta_word hψ hθ l hg)

theorem der_sub (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (a : D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)
    {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
    heisDer ψ θ a (f - g) = heisDer ψ θ a f - heisDer ψ θ a g := by
  have := word_add hψ hθ [a] (theta_sub hf hg) hg
  rw [sub_add_cancel] at this
  exact eq_sub_of_add_eq this.symm

def ccA (θ : InfFam D) (a : D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) (u : WO S T) : ℂ :=
  cc θ a.1 (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)) u

theorem der_heisO (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (a : D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)
    (u : WO S T) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    heisDer ψ θ a (heisO ψ S T u f) = heisO ψ S T u (heisDer ψ θ a f) + ccA θ a u • heisO ψ S T u f :=
  GlobalTheory.ThetaDecay.dRho_heisO hψ hθ a.1 _ u hf

theorem tendsto_word_heisO (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) : ∀ {f : WO S T → ℂ}, IsThetaFunO ψ S T f →
    Filter.Tendsto (fun u : WO S T => supN (wordAct (heisDer ψ θ) l (heisO ψ S T u f - f))) (𝓝 0) (𝓝 0) := by
  induction l using List.reverseRecOn with
  | nil => exact fun hf => tendsto_supN_heisO hψ hf
  | append_singleton l a ih =>
    intro f hf
    have ha : IsThetaFunO ψ S T (heisDer ψ θ a f) := theta_word hψ hθ [a] hf
    have hu := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf
    have hua := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ ha
    have hc : Filter.Tendsto (fun u : WO S T => ‖ccA θ a u‖ₑ) (𝓝 0) (𝓝 0) := by
      have := ((continuous_cc hθ a.1 (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1))).tendsto
        (0 : WO S T)).enorm
      rwa [cc_zero, enorm_zero] at this
    have ht := (ih ha).add (ENNReal.Tendsto.mul hc
      (Or.inr (by simpa using supN_ne_top hψ (theta_word hψ hθ l hf)))
      ((ih hf).add_const (supN (wordAct (heisDer ψ θ) l f))) (Or.inr ENNReal.zero_ne_top))
    rw [zero_mul, add_zero] at ht
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le) fun u => ?_
    have e : heisDer ψ θ a (heisO ψ S T u f - f) = (heisO ψ S T u (heisDer ψ θ a f) - heisDer ψ θ a f) +
        ccA θ a u • ((heisO ψ S T u f - f) + f) := by
      rw [der_sub hψ hθ a (hu u) hf, der_heisO hψ hθ a u hf, sub_add_cancel]
      abel
    beta_reduce
    rw [wordAct_append, wordAct_cons, wordAct_nil, e, word_add hψ hθ l (theta_sub (hua u) ha)
      (theta_smul _ (theta_add (theta_sub (hu u) hf) hf)), word_smul, word_add hψ hθ l (theta_sub (hu u) hf) hf]
    refine (supN_add_le _ _).trans ?_
    rw [supN_smul]
    gcongr
    exact supN_add_le _ _

theorem der_rem (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {L : ℝ →+ WO S T} (hL : IsRealDir T S L)
    (a : D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {t : ℝ} (ht : t ≠ 0) :
    heisDer ψ θ a (rem ψ L t f) - (ccA θ a (L 1) • f + dLine ψ S T L (heisDer ψ θ a f) - heisDer ψ θ a (dLine ψ S T L f)) =
      rem ψ L t (heisDer ψ θ a f) + ccA θ a (L 1) • (heisO ψ S T (L t) f - f) := by
  have hu := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf (L t)
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht
  have e : ccA θ a (L t) = t * ccA θ a (L 1) := cc_line hθ _ _ hL.1 t
  have e2 : ∀ (c : ℂ) (g : WO S T → ℂ), heisDer ψ θ a (c • g) = c • heisDer ψ θ a g := word_smul [a]
  unfold rem
  rw [der_sub hψ hθ a (theta_smul _ (theta_sub hu hf)) (theta_dLine hθ hψ hL hf), e2, der_sub hψ hθ a hu hf,
    der_heisO hψ hθ a _ hf, e]
  funext w
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem tendsto_word_rem (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {L : ℝ →+ WO S T} (hL : IsRealDir T S L)
    (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) : ∀ {f : WO S T → ℂ}, IsThetaFunO ψ S T f →
    Filter.Tendsto (fun t : ℝ => supN (wordAct (heisDer ψ θ) l (rem ψ L t f))) (𝓝[≠] 0) (𝓝 0) := by
  have hL0 : Filter.Tendsto L (𝓝[≠] 0) (𝓝 0) := by
    have := (hL.1.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    rwa [map_zero] at this
  have step : ∀ (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) (c : ℂ) {f g : WO S T → ℂ},
      IsThetaFunO ψ S T f → IsThetaFunO ψ S T g →
      Filter.Tendsto (fun t : ℝ => supN (wordAct (heisDer ψ θ) l (rem ψ L t g))) (𝓝[≠] 0) (𝓝 0) →
      Filter.Tendsto (fun t : ℝ => supN (wordAct (heisDer ψ θ) l (rem ψ L t g + c • (heisO ψ S T (L t) f - f))))
        (𝓝[≠] 0) (𝓝 0) := by
    intro l c f g hf hg h
    have ht := h.add (ENNReal.Tendsto.const_mul (a := ‖c‖ₑ) ((tendsto_word_heisO hψ hθ l hf).comp hL0)
      (Or.inr enorm_ne_top))
    rw [mul_zero, add_zero] at ht
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le) fun t => ?_
    beta_reduce
    rw [word_add hψ hθ l (theta_rem hθ hψ hL hg t)
      (theta_smul _ (theta_sub (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf _) hf)), word_smul]
    refine (supN_add_le _ _).trans ?_
    rw [supN_smul]
    rfl
  induction l using List.reverseRecOn with
  | nil => exact fun hf => tendsto_supN_rem hθ hψ hL hf
  | append_singleton l a ih =>
    intro f hf
    have ha : IsThetaFunO ψ S T (heisDer ψ θ a f) := theta_word hψ hθ [a] hf
    have h0 := eq_zero_of_tendsto hθ hψ (isRealDir_lineAt hθ a.1
      (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1))) (theta_rem hθ hψ hL hf)
      (tendsto_supN_rem hθ hψ hL hf)
      ((step [] (ccA θ a (L 1)) hf ha (tendsto_supN_rem hθ hψ hL ha)).congr'
        (eventually_nhdsWithin_of_forall fun t ht => congrArg supN (der_rem hψ hθ hL a hf ht).symm))
    refine (step l (ccA θ a (L 1)) hf ha (ih ha)).congr' (eventually_nhdsWithin_of_forall fun t ht => ?_)
    beta_reduce
    rw [← der_rem hψ hθ hL a hf ht, h0, sub_zero, wordAct_append]
    rfl

theorem tendsto_supSob {ι : Type} {l : Filter ι} {h : ι → WO S T → ℂ} (k : ℕ)
    (H : ∀ m, Filter.Tendsto (fun i => supN (wordAct (heisDer ψ θ) m (h i))) l (𝓝 0)) :
    Filter.Tendsto (fun i => supSob ψ θ k (h i)) l (𝓝 0) := by
  have := tendsto_finset_sum (Finset.range (k + 1)) fun j _ =>
    tendsto_finset_sum (Finset.univ : Finset (Fin j → D.what₂.Tau × Fin T.rank × Fin S.rank × Bool))
      fun a _ => H (List.ofFn a)
  simp only [Finset.sum_const_zero] at this
  exact this

theorem heisO_taylor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (k : ℕ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → Filter.Tendsto (fun u : WO S T => supSob ψ θ k (heisO ψ S T u f - f)) (nhds 0) (nhds 0) ∧ ∀ L : ℝ →+ WO S T, Continuous L → (∀ t, (L t).map (finPart D) = 0) → IsThetaFunO ψ S T (fun p => deriv (fun t : ℝ => heisO ψ S T (L t) f p) 0) ∧ Filter.Tendsto (fun t : ℝ => supSob ψ θ k ((t⁻¹ : ℂ) • (heisO ψ S T (L t) f - f) - fun p => deriv (fun t : ℝ => heisO ψ S T (L t) f p) 0)) (nhdsWithin 0 {0}ᶜ) (nhds 0) :=
  fun _ _ hψ _ hθ _ _ k _ hf => ⟨tendsto_supSob k fun m => tendsto_word_heisO hψ hθ m hf, fun _ h1 h2 =>
    ⟨theta_dLine hθ hψ ⟨h1, h2⟩ hf, tendsto_supSob k fun m => tendsto_word_rem hψ hθ ⟨h1, h2⟩ m hf⟩⟩

end GlobalTheory.HeisTaylor

end
