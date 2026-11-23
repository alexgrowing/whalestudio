import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.RealPlaceAnalysis.QuotientSettingHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhiCentreEigenfunctionDiscreteSeriesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiRestrictionHolomorphicNearOneStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiEntriesRealAnalyticStatement

open MeasureTheory Matrix Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.Dec.PsiEig

variable {n : ℕ}

local notation "Mt" => Matrix (Fin n) (Fin n) ℂ

section Linfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
  Matrix.linftyOpNormedSpace

theorem hasDerivAt_exp_entry (X : Mt) (s : ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℂ => (NormedSpace.exp (t • X)) i j) ((NormedSpace.exp (s • X) * X) i j) s := by
  let L : Mt →ₗ[ℂ] ℂ := (LinearMap.proj j).comp (LinearMap.proj (R := ℂ) (φ := fun _ : Fin n => Fin n → ℂ) i)
  have h := (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_exp_smul_const (𝕂 := ℂ) X s)
  exact h

end Linfty

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hasDerivAt_curve (g X : Mt) (s : ℂ) :
    HasDerivAt (fun t : ℂ => g * NormedSpace.exp (t • X)) (g * NormedSpace.exp (s • X) * X) s := by
  rw [Matrix.mul_assoc]
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
  show HasDerivAt (fun t : ℂ => ∑ k, g i k * NormedSpace.exp (t • X) k j) (∑ k, g i k * (NormedSpace.exp (s • X) * X) k j) s
  have := HasDerivAt.sum (u := Finset.univ) fun k _ => (hasDerivAt_exp_entry X s k j).const_mul (g i k)
  simpa only [Finset.sum_fn] using this

theorem hasDerivAt_curveR (g X : Mt) (s : ℝ) :
    HasDerivAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X))
      (g * NormedSpace.exp ((s : ℂ) • X) * X) s := by
  have h := (hasDerivAt_curve g X (s : ℂ)).scomp s (Complex.ofRealCLM.hasDerivAt (x := s))
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul] at h
  exact h

theorem analyticAt_curveR (g X : Mt) (s : ℝ) :
    AnalyticAt ℝ (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) s := by
  refine analyticAt_pi_iff.2 fun i => analyticAt_pi_iff.2 fun j => ?_
  show AnalyticAt ℝ (fun t : ℝ => ∑ k, g i k * NormedSpace.exp ((t : ℂ) • X) k j) s
  have hk : ∀ k, AnalyticAt ℝ (fun t : ℝ => g i k * NormedSpace.exp ((t : ℂ) • X) k j) s := by
    intro k
    have hd : Differentiable ℂ (fun t : ℂ => NormedSpace.exp (t • X) k j) :=
      fun t => (hasDerivAt_exp_entry X t k j).differentiableAt
    have h0 : AnalyticAt ℝ (fun t : ℝ => (t : ℂ)) s := Complex.ofRealCLM.analyticAt s
    have h1 : AnalyticAt ℝ (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) k j) s :=
      ((hd.analyticAt (s : ℂ)).restrictScalars (𝕜 := ℝ)).comp h0
    exact analyticAt_const.mul h1
  have := Finset.analyticAt_sum Finset.univ fun k _ => hk k
  simpa only [Finset.sum_fn] using this

theorem analyticAt_mul {𝕜 E : Type} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f g : E → Mt} {x : E}
    (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x) : AnalyticAt 𝕜 (fun y => f y * g y) x := by
  have he : ∀ (F : E → Mt), AnalyticAt 𝕜 F x → ∀ a b, AnalyticAt 𝕜 (fun y => F y a b) x := by
    intro F hF a b
    have ha : AnalyticAt 𝕜 (fun y => F y a) x := (analyticAt_pi_iff (f := fun a y => F y a)).1 hF a
    exact (analyticAt_pi_iff (f := fun b y => F y a b)).1 ha b
  refine analyticAt_pi_iff.2 fun i => analyticAt_pi_iff.2 fun j => ?_
  show AnalyticAt 𝕜 (fun y => ∑ k, f y i k * g y k j) x
  have hk : ∀ k, AnalyticAt 𝕜 (fun y => f y i k * g y k j) x := fun k => (he f hf i k).mul (he g hg k j)
  have := Finset.analyticAt_sum Finset.univ fun k _ => hk k
  simpa only [Finset.sum_fn] using this

def LocAn (ε : Fin n → Bool) (f : Mt → ℂ) : Prop :=
  ∀ g, inUJ ε g → ∃ F : Mt → ℂ, AnalyticAt ℝ F g ∧ ∀ᶠ z in 𝓝 g, inUJ ε z → f z = F z

theorem LocAn.smooth {ε : Fin n → Bool} {f : Mt → ℂ} (h : LocAn ε f) : SmoothOnG ε f := by
  intro g hg
  obtain ⟨F, hF, hev⟩ := h g hg
  obtain ⟨U, hU, hUo, hgU⟩ := mem_nhds_iff.1 (hF.eventually_analyticAt.and hev)
  exact ⟨U, F, hUo, hgU, fun z hz => (hU hz).1.contDiffAt.contDiffWithinAt, fun z hz hzJ => (hU hz).2 hzJ⟩

private theorem analyticAt_clm_apply {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {A : E → F →L[𝕜] G} {B : E → F} {x : E} (hA : AnalyticAt 𝕜 A x) (hB : AnalyticAt 𝕜 B x) :
    AnalyticAt 𝕜 (fun y => A y (B y)) x := by
  have h := (ContinuousLinearMap.apply 𝕜 G : F →L[𝕜] (F →L[𝕜] G) →L[𝕜] G).analyticAt_bilinear (B x, A x)
  have h2 : AnalyticAt 𝕜 (fun y => (B y, A y)) x := hB.prod hA
  exact AnalyticAt.comp (g := fun p : F × (F →L[𝕜] G) => (ContinuousLinearMap.apply 𝕜 G) p.1 p.2)
    (f := fun y => (B y, A y)) h h2

theorem LocAn.rd {ε : Fin n → Bool} {f : Mt → ℂ} (h : LocAn ε f) {X : Mt} (hX : inG ε X) :
    LocAn ε (Rd X f) := by
  intro g hg
  obtain ⟨F, hF, hev⟩ := h g hg
  obtain ⟨U, hU, hUo, hgU⟩ := mem_nhds_iff.1 (hF.eventually_analyticAt.and hev)
  have hCD : ContDiffOn ℝ ∞ F U := fun z hz => (hU hz).1.contDiffAt.contDiffWithinAt
  let L : Mt →ₗ[ℝ] Mt := LinearMap.mulRight ℝ X
  refine ⟨fun z => fderiv ℝ F z (z * X), ?_, ?_⟩
  · have h2 : AnalyticAt ℝ (fun z : Mt => z * X) g := (LinearMap.toContinuousLinearMap L).analyticAt g
    exact analyticAt_clm_apply (AnalyticAt.fderiv hF) h2
  · filter_upwards [hUo.mem_nhds hgU] with z hz hzJ
    exact Formalism.REAL.right_derivative_extends n ε f F U z X hUo hz hzJ hCD (fun w hw hwJ => (hU hw).2 hwJ) hX

theorem LocAn.add {ε : Fin n → Bool} {f f' : Mt → ℂ} (h : LocAn ε f) (h' : LocAn ε f') :
    LocAn ε (fun g => f g + f' g) := by
  intro g hg
  obtain ⟨F, hF, e⟩ := h g hg
  obtain ⟨F', hF', e'⟩ := h' g hg
  refine ⟨fun z => F z + F' z, hF.add hF', ?_⟩
  filter_upwards [e, e'] with z h1 h2 hz
  rw [h1 hz, h2 hz]

theorem LocAn.const_mul {ε : Fin n → Bool} {f : Mt → ℂ} (h : LocAn ε f) (c : ℂ) :
    LocAn ε (fun g => c * f g) := by
  intro g hg
  obtain ⟨F, hF, e⟩ := h g hg
  refine ⟨fun z => c * F z, analyticAt_const.mul hF, ?_⟩
  filter_upwards [e] with z h1 hz
  rw [h1 hz]

theorem LocAn.sum {ε : Fin n → Bool} {ι : Type} (s : Finset ι) {f : ι → Mt → ℂ}
    (h : ∀ i, LocAn ε (f i)) : LocAn ε (fun g => ∑ i ∈ s, f i g) := by
  intro g hg
  choose F hF e using fun i => h i g hg
  have hA : AnalyticAt ℝ (fun z => ∑ i ∈ s, F i z) g := by
    have := Finset.analyticAt_sum s fun i _ => hF i
    simpa only [Finset.sum_fn] using this
  refine ⟨fun z => ∑ i ∈ s, F i z, hA, ?_⟩
  have hs : ∀ᶠ z in 𝓝 g, ∀ i ∈ s, inUJ ε z → f i z = F i z :=
    (Filter.eventually_all_finset s).2 fun i _ => e i
  filter_upwards [hs] with z hz hzJ
  exact Finset.sum_congr rfl fun i hi => hz i hi hzJ

theorem LocAn.eword {ε : Fin n → Bool} {f : Mt → ℂ} (h : LocAn ε f) (w : List (Fin n × Fin n)) :
    LocAn ε (Eword ε w f) := by
  induction w with
  | nil => exact h
  | cons p w ih =>
    have c := Formalism.REAL.complex_parts_mem_lie_algebra_holds n ε (Matrix.single p.1 p.2 1)
    exact (ih.rd c.1).add ((ih.rd c.2.1).const_mul Complex.I)

theorem LocAn.gelf {ε : Fin n → Bool} {f : Mt → ℂ} (h : LocAn ε f) (m : ℕ) :
    LocAn ε (gelf ε m f) := LocAn.sum Finset.univ fun _ => h.eword _

theorem LocAn.propagate {ε : Fin n → Bool} {f : Mt → ℂ} (h : LocAn ε f) {g X : Mt} (hX : inG ε X)
    (h0 : ∀ᶠ z in 𝓝 g, inUJ ε z → f z = 0) :
    ∀ᶠ z in 𝓝 (g * NormedSpace.exp X), inUJ ε z → f z = 0 := by
  by_cases hg : inUJ ε g
  · obtain ⟨V, hV, hVo, hgV⟩ := mem_nhds_iff.1 h0
    have hexp : ∀ t : ℝ, inUJ ε (NormedSpace.exp ((t : ℂ) • X)) := Formalism.REAL.exp_indefinite_unitary_holds n ε X hX
    have hmul : ∀ a b : Mt, inUJ ε a → inUJ ε b → inUJ ε (a * b) := by
      intro a b ha hb
      have ha' : aᴴ * Formalism.REAL.Jm ε * a = Formalism.REAL.Jm ε := ha
      have hb' : bᴴ * Formalism.REAL.Jm ε * b = Formalism.REAL.Jm ε := hb
      show (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = Formalism.REAL.Jm ε
      rw [Matrix.conjTranspose_mul]
      calc bᴴ * aᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
            simp only [Matrix.mul_assoc]
        _ = Formalism.REAL.Jm ε := by rw [ha', hb']
    have hcurve : ∀ w : Mt, Continuous (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X) * w) := fun w =>
      (continuous_iff_continuousAt.2 fun t => (hasDerivAt_curveR g X t).continuousAt).matrix_mul continuous_const
    have core : ∀ w, inUJ ε w → g * w ∈ V → f (g * NormedSpace.exp X * w) = 0 := by
      intro w hw hgw
      have hp : ∀ t : ℝ, inUJ ε (g * NormedSpace.exp ((t : ℂ) • X) * w) := fun t =>
        hmul _ _ (hmul _ _ hg (hexp t)) hw
      have han : AnalyticOnNhd ℝ (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X) * w)) Set.univ := by
        intro t _
        obtain ⟨F, hF, hev⟩ := h _ (hp t)
        have hpa : AnalyticAt ℝ (fun s : ℝ => g * NormedSpace.exp ((s : ℂ) • X) * w) t :=
          analyticAt_mul (analyticAt_curveR g X t) analyticAt_const
        have hcomp : AnalyticAt ℝ (fun s : ℝ => F (g * NormedSpace.exp ((s : ℂ) • X) * w)) t :=
          AnalyticAt.comp (f := fun s : ℝ => g * NormedSpace.exp ((s : ℂ) • X) * w) hF hpa
        refine hcomp.congr ?_
        have := (hcurve w).continuousAt.eventually hev
        filter_upwards [this] with s hs
        exact (hs (hp s)).symm
      have hz : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X) * w)) =ᶠ[𝓝 0] 0 := by
        have hVn : V ∈ 𝓝 ((fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X) * w) 0) := by
          simpa using hVo.mem_nhds hgw
        have hV0 : ∀ᶠ s : ℝ in 𝓝 0, g * NormedSpace.exp ((s : ℂ) • X) * w ∈ V :=
          (hcurve w).continuousAt.preimage_mem_nhds hVn
        filter_upwards [hV0] with s hs
        exact hV hs (hp s)
      have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0) hz
        (Set.mem_univ 1)
      simpa using this
    set a := g * NormedSpace.exp X with ha_def
    have ha : inUJ ε a := hmul _ _ hg (by simpa using hexp 1)
    have ha' : aᴴ * Formalism.REAL.Jm ε * a = Formalism.REAL.Jm ε := ha
    have hJJ : ∀ M : Mt, Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * M) = M := fun M => by
      rw [← Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.one_mul]
    set B := Formalism.REAL.Jm ε * aᴴ * Formalism.REAL.Jm ε with hB_def
    have hleft : B * a = 1 := by
      rw [hB_def]
      calc Formalism.REAL.Jm ε * aᴴ * Formalism.REAL.Jm ε * a = Formalism.REAL.Jm ε * (aᴴ * Formalism.REAL.Jm ε * a) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [ha', Formalism.REAL.Jm_mul_self]
    have hright : a * B = 1 := mul_eq_one_comm.1 hleft
    have hBJB : Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε := by
      have e1 : Bᴴ = Formalism.REAL.Jm ε * a * Formalism.REAL.Jm ε := by
        rw [hB_def]; simp only [Matrix.conjTranspose_mul, Formalism.REAL.Jm_conjTranspose,
          Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [e1]
      have hr' : a * (Formalism.REAL.Jm ε * (aᴴ * Formalism.REAL.Jm ε)) = 1 := by
        rw [← hright, hB_def]; simp only [Matrix.mul_assoc]
      calc Formalism.REAL.Jm ε * a * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε * B
          = Formalism.REAL.Jm ε * (a * (Formalism.REAL.Jm ε * (aᴴ * Formalism.REAL.Jm ε))) := by
            rw [hB_def]; simp only [Matrix.mul_assoc, hJJ]
        _ = Formalism.REAL.Jm ε := by rw [hr', Matrix.mul_one]
    have hc : Continuous (fun q : Mt => g * (B * q)) := continuous_const.matrix_mul (continuous_const.matrix_mul continuous_id)
    have hnb : ∀ᶠ q in 𝓝 a, g * (B * q) ∈ V :=
      hc.continuousAt.preimage_mem_nhds (by rw [hleft, Matrix.mul_one]; exact hVo.mem_nhds hgV)
    filter_upwards [hnb] with q hq hqJ
    have hqJ' : qᴴ * Formalism.REAL.Jm ε * q = Formalism.REAL.Jm ε := hqJ
    have hw : inUJ ε (B * q) := by
      show (B * q)ᴴ * Formalism.REAL.Jm ε * (B * q) = Formalism.REAL.Jm ε
      rw [Matrix.conjTranspose_mul]
      calc qᴴ * Bᴴ * Formalism.REAL.Jm ε * (B * q) = qᴴ * (Bᴴ * Formalism.REAL.Jm ε * B) * q := by
            simp only [Matrix.mul_assoc]
        _ = Formalism.REAL.Jm ε := by rw [hBJB, hqJ']
    have := core _ hw hq
    rwa [← Matrix.mul_assoc, hright, Matrix.one_mul] at this
  · have hcl : IsClosed {z : Mt | inUJ ε z} := Formalism.REAL.indefinite_unitary_closed n ε
    have hne : ¬ inUJ ε (g * NormedSpace.exp X) := by
      intro hgx
      apply hg
      have hexp : inUJ ε (NormedSpace.exp (((-1 : ℝ) : ℂ) • X)) := Formalism.REAL.exp_indefinite_unitary_holds n ε X hX (-1)
      have e : g = g * NormedSpace.exp X * NormedSpace.exp (((-1 : ℝ) : ℂ) • X) := by
        rw [Matrix.mul_assoc, ← Matrix.exp_add_of_commute X _ ((Commute.refl X).smul_right _)]
        simp
      rw [e]
      have ha' : (g * NormedSpace.exp X)ᴴ * Formalism.REAL.Jm ε * (g * NormedSpace.exp X) = Formalism.REAL.Jm ε := hgx
      have hb' : (NormedSpace.exp (((-1 : ℝ) : ℂ) • X))ᴴ * Formalism.REAL.Jm ε * NormedSpace.exp (((-1 : ℝ) : ℂ) • X)
          = Formalism.REAL.Jm ε := hexp
      show (g * NormedSpace.exp X * NormedSpace.exp (((-1 : ℝ) : ℂ) • X))ᴴ * Formalism.REAL.Jm ε *
        (g * NormedSpace.exp X * NormedSpace.exp (((-1 : ℝ) : ℂ) • X)) = Formalism.REAL.Jm ε
      rw [Matrix.conjTranspose_mul]
      calc (NormedSpace.exp (((-1 : ℝ) : ℂ) • X))ᴴ * (g * NormedSpace.exp X)ᴴ * Formalism.REAL.Jm ε *
            (g * NormedSpace.exp X * NormedSpace.exp (((-1 : ℝ) : ℂ) • X))
          = (NormedSpace.exp (((-1 : ℝ) : ℂ) • X))ᴴ * ((g * NormedSpace.exp X)ᴴ * Formalism.REAL.Jm ε *
            (g * NormedSpace.exp X)) * NormedSpace.exp (((-1 : ℝ) : ℂ) • X) := by simp only [Matrix.mul_assoc]
        _ = Formalism.REAL.Jm ε := by rw [ha', hb']
    filter_upwards [hcl.isOpen_compl.mem_nhds hne] with z hz hzJ
    exact absurd hzJ hz

theorem LocAn.eq_zero {ε : Fin n → Bool} {f : Mt → ℂ} (h : LocAn ε f)
    (h0 : ∀ᶠ z in 𝓝 (1 : Mt), inUJ ε z → f z = 0) {g : Mt} (hg : inUJ ε g) : f g = 0 := by
  obtain ⟨Z, X, hZ, hX, rfl⟩ := Formalism.REAL.genExp _ _ _ hg
  have h1 : ∀ᶠ z in 𝓝 ((1 : Mt) * NormedSpace.exp Z), inUJ ε z → f z = 0 := h.propagate hZ.1 h0
  rw [one_mul] at h1
  exact (h.propagate hX.1 h1).self_of_nhds hg

theorem hasDerivAt_integral_compact {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K]
    [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] {F F' : ℝ → K → ℂ} {s : Set ℝ} (hs : s ∈ 𝓝 (0 : ℝ))
    (hF : ∀ t ∈ s, Continuous (F t)) (hF' : ContinuousOn (fun x : ℝ × K => F' x.1 x.2) (s ×ˢ Set.univ))
    (hd : ∀ k, ∀ t ∈ s, HasDerivAt (F · k) (F' t k) t) :
    HasDerivAt (fun t => ∫ k, F t k ∂μ) (∫ k, F' 0 k ∂μ) 0 := by
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.1 hs
  have hδ : (0 : ℝ) < r / 2 := by positivity
  have hcb : Metric.closedBall (0 : ℝ) (r / 2) ⊆ s := fun t ht =>
    hrs (Metric.closedBall_subset_ball (by linarith) ht)
  have hcomp : IsCompact (Metric.closedBall (0 : ℝ) (r / 2) ×ˢ (Set.univ : Set K)) :=
    (isCompact_closedBall 0 (r / 2)).prod isCompact_univ
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn (hF'.mono (Set.prod_mono hcb subset_rfl))
  have h0 : (0 : ℝ) ∈ s := mem_of_mem_nhds hs
  obtain ⟨C0, hC0⟩ := isCompact_univ.exists_bound_of_continuousOn (hF 0 h0).continuousOn
  have hF'0 : Continuous (F' 0) :=
    hF'.comp_continuous (continuous_const.prodMk continuous_id) fun k => ⟨h0, trivial⟩
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ)) (F := F) (F' := F')
    (bound := fun _ => C) (Metric.ball_mem_nhds 0 hδ)
    (by filter_upwards [hs] with t ht; exact (hF t ht).aestronglyMeasurable)
    (Integrable.of_bound (hF 0 h0).aestronglyMeasurable C0 (ae_of_all _ fun k => hC0 k trivial))
    hF'0.aestronglyMeasurable
    (ae_of_all _ fun k t ht => hC (t, k) ⟨Metric.ball_subset_closedBall ht, trivial⟩)
    (integrable_const C)
    (ae_of_all _ fun k t ht => hd k t (hcb (Metric.ball_subset_closedBall ht)))
  exact key.2

def Om3 (n : ℕ) : Set ((Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) × Matrix (Fin n) (Fin n) ℂ) :=
  {x | x.1.1 * x.2 * x.1.2 ∈ Omega n}

theorem analyticAt_leadMinor (l : ℕ) (hl : l ≤ n) (z : Mt) :
    AnalyticAt ℂ (fun y : Mt => leadMinor y l hl) z := by
  have he : ∀ a b, AnalyticAt ℂ (fun y : Mt => y a b) z := fun a b => by
    have ha : AnalyticAt ℂ (fun y : Mt => y a) z :=
      (analyticAt_pi_iff (f := fun a (y : Mt) => y a)).1 (analyticAt_id (𝕜 := ℂ) (z := z)) a
    exact (analyticAt_pi_iff (f := fun b (y : Mt) => y a b)).1 ha b
  show AnalyticAt ℂ (fun y : Mt => (y.submatrix (Fin.castLE hl) (Fin.castLE hl)).det) z
  simp only [Matrix.det_apply, Matrix.submatrix_apply, Units.smul_def, zsmul_eq_mul]
  have hp : ∀ σ : Equiv.Perm (Fin l), AnalyticAt ℂ
      (fun y : Mt => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, y (Fin.castLE hl (σ i)) (Fin.castLE hl i)) z := by
    intro σ
    have := Finset.analyticAt_prod (Finset.univ : Finset (Fin l))
      (f := fun i (y : Mt) => y (Fin.castLE hl (σ i)) (Fin.castLE hl i)) fun i _ => he _ _
    exact analyticAt_const.mul (by simpa only [Finset.prod_fn] using this)
  have := Finset.analyticAt_sum Finset.univ fun σ _ => hp σ
  simpa only [Finset.sum_fn] using this

theorem isOpen_Omega : IsOpen (Omega n) := by
  have hc : ∀ i : Fin n, Continuous (fun y : Mt => leadMinor y (i.val + 1) i.isLt) := fun i =>
    continuous_iff_continuousAt.2 fun y => (analyticAt_leadMinor _ _ y).continuousAt
  have : Omega n = ⋂ i : Fin n, (fun y : Mt => leadMinor y (i.val + 1) i.isLt) ⁻¹' {0}ᶜ := by
    ext y; simp [Omega]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_compl_singleton.preimage (hc i)

theorem isOpen_leadingMinorsNonzeroTripleSet : IsOpen (Om3 n) := isOpen_Omega.preimage ((continuous_fst.fst.matrix_mul continuous_snd).matrix_mul continuous_fst.snd)

theorem analyticOn_leadingMinorPowerProduct_triple (lam : Fin n → ℝ) :
    AnalyticOnNhd ℂ (fun x : (Mt × Mt) × Mt => Phi lam (x.1.1 * x.2 * x.1.2)) (Om3 n) := by
  intro x hx
  have h11 : AnalyticAt ℂ (fun x : (Mt × Mt) × Mt => x.1.1) x := AnalyticAt.comp analyticAt_fst analyticAt_fst
  have h12 : AnalyticAt ℂ (fun x : (Mt × Mt) × Mt => x.1.2) x := AnalyticAt.comp analyticAt_snd analyticAt_fst
  have h2 : AnalyticAt ℂ (fun x : (Mt × Mt) × Mt => x.2) x := analyticAt_snd
  have hm : AnalyticAt ℂ (fun x : (Mt × Mt) × Mt => x.1.1 * x.2 * x.1.2) x :=
    analyticAt_mul (analyticAt_mul h11 h2) h12
  show AnalyticAt ℂ (fun x : (Mt × Mt) × Mt => ∏ i : Fin n,
    leadMinor (x.1.1 * x.2 * x.1.2) (i.val + 1) i.isLt ^ (-(sInt lam i))) x
  have hi : ∀ i : Fin n, AnalyticAt ℂ (fun x : (Mt × Mt) × Mt =>
      leadMinor (x.1.1 * x.2 * x.1.2) (i.val + 1) i.isLt ^ (-(sInt lam i))) x := fun i =>
    by exact ((analyticAt_leadMinor _ _ _).comp hm).zpow (hx i)
  have := Finset.analyticAt_prod Finset.univ fun i _ => hi i
  simpa only [Finset.prod_fn] using this

private theorem analyticAt_clm_apply' {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {A : E → F →L[𝕜] G} {B : E → F} {x : E} (hA : AnalyticAt 𝕜 A x) (hB : AnalyticAt 𝕜 B x) :
    AnalyticAt 𝕜 (fun y => A y (B y)) x := by
  have h := (ContinuousLinearMap.apply 𝕜 G : F →L[𝕜] (F →L[𝕜] G) →L[𝕜] G).analyticAt_bilinear (B x, A x)
  have h2 : AnalyticAt 𝕜 (fun y => (B y, A y)) x := hB.prod hA
  exact AnalyticAt.comp (g := fun p : F × (F →L[𝕜] G) => (ContinuousLinearMap.apply 𝕜 G) p.1 p.2)
    (f := fun y => (B y, A y)) h h2

def Dz (Z : Mt) (G : (Mt × Mt) × Mt → ℂ) : (Mt × Mt) × Mt → ℂ :=
  fun x => fderiv ℂ G x (0, x.2 * Z)

def Dw (w : List (Fin n × Fin n)) (G : (Mt × Mt) × Mt → ℂ) : (Mt × Mt) × Mt → ℂ :=
  w.foldr (fun p G => Dz (Matrix.single p.1 p.2 1) G) G

theorem analytic_Dz {G : (Mt × Mt) × Mt → ℂ} (hG : AnalyticOnNhd ℂ G (Om3 n)) (Z : Mt) :
    AnalyticOnNhd ℂ (Dz Z G) (Om3 n) := by
  intro x hx
  have h2 : AnalyticAt ℂ (fun x : (Mt × Mt) × Mt => ((0 : Mt × Mt), x.2 * Z)) x :=
    analyticAt_const.prod (analyticAt_mul analyticAt_snd analyticAt_const)
  exact analyticAt_clm_apply' (AnalyticAt.fderiv (hG x hx)) h2

theorem analytic_Dw {G : (Mt × Mt) × Mt → ℂ} (hG : AnalyticOnNhd ℂ G (Om3 n))
    (w : List (Fin n × Fin n)) : AnalyticOnNhd ℂ (Dw w G) (Om3 n) := by
  induction w with
  | nil => exact hG
  | cons p w ih => exact analytic_Dz ih _

theorem hasDerivAt_slice {G : (Mt × Mt) × Mt → ℂ} (hG : AnalyticOnNhd ℂ G (Om3 n)) (p : Mt × Mt)
    (z X : Mt) (s : ℂ) (hs : (p, z * NormedSpace.exp (s • X)) ∈ Om3 n) :
    HasDerivAt (fun t : ℂ => G (p, z * NormedSpace.exp (t • X)))
      (Dz X G (p, z * NormedSpace.exp (s • X))) s := by
  have h := (hG _ hs).differentiableAt.hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_const s p).prodMk (hasDerivAt_curve z X s))
  exact h

theorem rholW_eq {G : (Mt × Mt) × Mt → ℂ} (hG : AnalyticOnNhd ℂ G (Om3 n)) (p : Mt × Mt)
    (w : List (Fin n × Fin n)) (z : Mt) (hz : (p, z) ∈ Om3 n) :
    RholW w (fun y => G (p, y)) z = Dw w G (p, z) := by
  induction w generalizing z with
  | nil => rfl
  | cons q w ih =>
    show deriv (fun t : ℂ => RholW w (fun y => G (p, y)) (z * NormedSpace.exp (t • Matrix.single q.1 q.2 (1 : ℂ)))) 0
      = Dz (Matrix.single q.1 q.2 1) (Dw w G) (p, z)
    have hcu : Continuous (fun t : ℂ => z * NormedSpace.exp (t • Matrix.single q.1 q.2 (1 : ℂ))) :=
      continuous_iff_continuousAt.2 fun t => (hasDerivAt_curve z _ t).continuousAt
    have hc : Continuous (fun t : ℂ => (p, z * NormedSpace.exp (t • Matrix.single q.1 q.2 (1 : ℂ)))) :=
      continuous_const.prodMk hcu
    have hev : ∀ᶠ t in 𝓝 (0 : ℂ), (p, z * NormedSpace.exp (t • Matrix.single q.1 q.2 (1 : ℂ))) ∈ Om3 n := by
      apply hc.continuousAt.preimage_mem_nhds
      simpa using isOpen_leadingMinorsNonzeroTripleSet.mem_nhds hz
    have heq : (fun t : ℂ => RholW w (fun y => G (p, y)) (z * NormedSpace.exp (t • Matrix.single q.1 q.2 (1 : ℂ))))
        =ᶠ[𝓝 0] fun t => Dw w G (p, z * NormedSpace.exp (t • Matrix.single q.1 q.2 (1 : ℂ))) :=
      hev.mono fun t ht => ih _ ht
    rw [heq.deriv_eq]
    have hd := hasDerivAt_slice (analytic_Dw hG w) p z (Matrix.single q.1 q.2 1) 0 (by simpa using hz)
    simpa using hd.deriv

def pk {ε : Fin n → Bool} (k : KG ε) : Mt × Mt := ((toMK k)⁻¹, toMK k)

theorem continuous_toMK (ε : Fin n → Bool) : Continuous (fun k : KG ε => toMK k) := (Units.continuous_val.comp continuous_subtype_val).comp continuous_subtype_val

theorem continuous_pk (ε : Fin n → Bool) : Continuous (pk (ε := ε)) := by
  have e : (pk (ε := ε)) = fun k : KG ε =>
      (((((k : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Mt), toMK k) := by
    funext k; simp [pk, Matrix.coe_units_inv]
  rw [e]
  exact (Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_subtype_val)).prodMk (continuous_toMK ε)

theorem pk_mem {ε : Fin n → Bool} {z : Mt} (hz : z ∈ U1 ε) (k : KG ε) : (pk k, z) ∈ Om3 n := hz _ ((Formalism.REAL.mem_KG ε _).1 k.2)

def intK {ε : Fin n → Bool} (c : KG ε → ℂ) (G : (Mt × Mt) × Mt → ℂ) (z : Mt) : ℂ :=
  ∫ k, G (pk k, z) * c k ∂(muK ε)

theorem continuous_slice {ε : Fin n → Bool} {c : KG ε → ℂ} (hc : Continuous c)
    {G : (Mt × Mt) × Mt → ℂ} (hG : AnalyticOnNhd ℂ G (Om3 n)) {z : Mt} (hz : z ∈ U1 ε) :
    Continuous (fun k : KG ε => G (pk k, z) * c k) := by
  have h1 : Continuous (fun k : KG ε => G (pk k, z)) := continuous_iff_continuousAt.2 fun k =>
    ContinuousAt.comp (f := fun k : KG ε => (pk k, z)) (hG _ (pk_mem hz k)).continuousAt
      ((continuous_pk ε).prodMk (continuous_const (y := z))).continuousAt
  exact h1.mul hc

private theorem compactSpace_KG' (ε : Fin n → Bool) : CompactSpace (KG ε) := by
  have hKc : IsCompact (Kset ε) := (Formalism.REAL.maximal_compact_facts n ε).2.1
  have hrange : Set.range (fun k : KG ε => toMK k) = Kset ε := by
    ext M
    constructor
    · rintro ⟨k, rfl⟩
      exact (Formalism.REAL.mem_KG ε _).1 k.2
    · intro hM
      exact ⟨⟨⟨⟨M, star M, Matrix.mem_unitaryGroup_iff.1 hM.1, Matrix.mem_unitaryGroup_iff'.1 hM.1⟩,
        (Formalism.REAL.maximal_compact_facts n ε).1 M hM⟩, (Formalism.REAL.mem_KG ε _).2 hM⟩, rfl⟩
  have h1 : Topology.IsInducing (fun k : KG ε => Units.embedProduct Mt ((k : UJ ε) : Mtˣ)) :=
    Units.isEmbedding_embedProduct.isInducing.comp
      (Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal)
  have hg : Continuous (fun M : Mt => (M, MulOpposite.op Mᴴ)) :=
    continuous_id.prodMk (MulOpposite.continuous_op.comp continuous_id.matrix_conjTranspose)
  have hind : Topology.IsInducing (fun k : KG ε => toMK k) := by
    refine Topology.IsInducing.of_comp (continuous_toMK ε) hg ?_
    convert h1 using 1
    funext k
    have hu : toMK k ∈ Matrix.unitaryGroup (Fin n) ℂ := ((Formalism.REAL.mem_KG ε _).1 k.2).1
    have hs : toMK k * (toMK k)ᴴ = 1 := by
      rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.1 hu
    simp only [Function.comp_apply, Units.embedProduct_apply]
    exact Prod.ext rfl (congrArg MulOpposite.op (Units.eq_inv_of_mul_eq_one_left hs))
  have hc : IsCompact (Set.univ : Set (KG ε)) := by
    rw [hind.isCompact_iff, Set.image_univ, hrange]; exact hKc
  exact isCompact_univ_iff.1 hc

theorem integrable_slice {ε : Fin n → Bool} {c : KG ε → ℂ} (hc : Continuous c)
    {G : (Mt × Mt) × Mt → ℂ} (hG : AnalyticOnNhd ℂ G (Om3 n)) {z : Mt} (hz : z ∈ U1 ε) :
    Integrable (fun k : KG ε => G (pk k, z) * c k) (muK ε) := by
  have := compactSpace_KG' ε
  have : IsProbabilityMeasure (muK ε) := (Formalism.REAL.kHaar n ε).1
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (continuous_slice hc hG hz).continuousOn
  exact Integrable.of_bound (continuous_slice hc hG hz).aestronglyMeasurable C (ae_of_all _ fun k => hC k trivial)

private theorem compactSpace_KG'' (ε : Fin n → Bool) : CompactSpace (KG ε) := by
  have hKc : IsCompact (Kset ε) := (Formalism.REAL.maximal_compact_facts n ε).2.1
  have hrange : Set.range (fun k : KG ε => toMK k) = Kset ε := by
    ext M
    constructor
    · rintro ⟨k, rfl⟩
      exact (Formalism.REAL.mem_KG ε _).1 k.2
    · intro hM
      exact ⟨⟨⟨⟨M, star M, Matrix.mem_unitaryGroup_iff.1 hM.1, Matrix.mem_unitaryGroup_iff'.1 hM.1⟩,
        (Formalism.REAL.maximal_compact_facts n ε).1 M hM⟩, (Formalism.REAL.mem_KG ε _).2 hM⟩, rfl⟩
  have h1 : Topology.IsInducing (fun k : KG ε => Units.embedProduct Mt ((k : UJ ε) : Mtˣ)) :=
    Units.isEmbedding_embedProduct.isInducing.comp
      (Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal)
  have hg : Continuous (fun M : Mt => (M, MulOpposite.op Mᴴ)) :=
    continuous_id.prodMk (MulOpposite.continuous_op.comp continuous_id.matrix_conjTranspose)
  have hind : Topology.IsInducing (fun k : KG ε => toMK k) := by
    refine Topology.IsInducing.of_comp (continuous_toMK ε) hg ?_
    convert h1 using 1
    funext k
    have hu : toMK k ∈ Matrix.unitaryGroup (Fin n) ℂ := ((Formalism.REAL.mem_KG ε _).1 k.2).1
    have hs : toMK k * (toMK k)ᴴ = 1 := by
      rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.1 hu
    simp only [Function.comp_apply, Units.embedProduct_apply]
    exact Prod.ext rfl (congrArg MulOpposite.op (Units.eq_inv_of_mul_eq_one_left hs))
  have hc : IsCompact (Set.univ : Set (KG ε)) := by
    rw [hind.isCompact_iff, Set.image_univ, hrange]; exact hKc
  exact isCompact_univ_iff.1 hc

private theorem inUJ_mul_flag_measures {ε : Fin n → Bool} {a b : Mt} (ha : inUJ ε a) (hb : inUJ ε b) :
    inUJ ε (a * b) := by
  have ha' : aᴴ * Formalism.REAL.Jm ε * a = Formalism.REAL.Jm ε := ha
  have hb' : bᴴ * Formalism.REAL.Jm ε * b = Formalism.REAL.Jm ε := hb
  show (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = Formalism.REAL.Jm ε
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [ha', hb']

theorem rd_intK {ε : Fin n → Bool} {c : KG ε → ℂ} (hc : Continuous c)
    {G : (Mt × Mt) × Mt → ℂ} (hG : AnalyticOnNhd ℂ G (Om3 n)) {f : Mt → ℂ} {z X : Mt} (hz : inUJ ε z)
    (hX : inG ε X) (h : ∀ᶠ y in 𝓝 z, inUJ ε y → y ∈ U1 ε ∧ f y = intK c G y) :
    Rd X f z = intK c (Dz X G) z := by
  have hcK := compactSpace_KG'' ε
  have hP : IsProbabilityMeasure (muK ε) := (Formalism.REAL.kHaar n ε).1
  have hexp : ∀ t : ℝ, inUJ ε (NormedSpace.exp ((t : ℂ) • X)) := Formalism.REAL.exp_indefinite_unitary_holds n ε X hX
  have hpJ : ∀ t : ℝ, inUJ ε (z * NormedSpace.exp ((t : ℂ) • X)) := fun t => inUJ_mul_flag_measures hz (hexp t)
  have hcurve : Continuous (fun t : ℝ => z * NormedSpace.exp ((t : ℂ) • X)) :=
    continuous_iff_continuousAt.2 fun t => (hasDerivAt_curveR z X t).continuousAt
  set S := (fun t : ℝ => z * NormedSpace.exp ((t : ℂ) • X)) ⁻¹'
    {y | inUJ ε y → y ∈ U1 ε ∧ f y = intK c G y} with hS_def
  have hn : {y | inUJ ε y → y ∈ U1 ε ∧ f y = intK c G y} ∈
      𝓝 ((fun t : ℝ => z * NormedSpace.exp ((t : ℂ) • X)) 0) := by
    have e : (fun t : ℝ => z * NormedSpace.exp ((t : ℂ) • X)) 0 = z := by simp
    rw [e]; exact h
  have hs : S ∈ 𝓝 (0 : ℝ) := hcurve.continuousAt.preimage_mem_nhds hn
  have hU1 : ∀ t ∈ S, z * NormedSpace.exp ((t : ℂ) • X) ∈ U1 ε := fun t ht => (ht (hpJ t)).1
  have hF : ∀ t ∈ S, Continuous (fun k : KG ε => G (pk k, z * NormedSpace.exp ((t : ℂ) • X)) * c k) :=
    fun t ht => continuous_slice hc hG (hU1 t ht)
  have hDz := analytic_Dz hG X
  have hq : Continuous (fun x : ℝ × KG ε => (pk x.2, z * NormedSpace.exp ((x.1 : ℂ) • X))) :=
    ((continuous_pk ε).comp continuous_snd).prodMk (hcurve.comp continuous_fst)
  have hF' : ContinuousOn (fun x : ℝ × KG ε => Dz X G (pk x.2, z * NormedSpace.exp ((x.1 : ℂ) • X)) * c x.2)
      (S ×ˢ Set.univ) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    have hm : (pk x.2, z * NormedSpace.exp ((x.1 : ℂ) • X)) ∈ Om3 n := pk_mem (hU1 x.1 hx.1) x.2
    exact (ContinuousAt.comp (f := fun x : ℝ × KG ε => (pk x.2, z * NormedSpace.exp ((x.1 : ℂ) • X)))
      (hDz _ hm).continuousAt hq.continuousAt).mul (hc.comp continuous_snd).continuousAt
  have hd : ∀ k, ∀ t ∈ S, HasDerivAt (fun t : ℝ => G (pk k, z * NormedSpace.exp ((t : ℂ) • X)) * c k)
      (Dz X G (pk k, z * NormedSpace.exp ((t : ℂ) • X)) * c k) t := by
    intro k t ht
    have h1 := hasDerivAt_slice hG (pk k) z X (t : ℂ) (pk_mem (hU1 t ht) k)
    exact h1.comp_ofReal.mul_const (c k)
  have key := hasDerivAt_integral_compact (muK ε)
    (F := fun t k => G (pk k, z * NormedSpace.exp ((t : ℂ) • X)) * c k)
    (F' := fun t k => Dz X G (pk k, z * NormedSpace.exp ((t : ℂ) • X)) * c k) hs hF hF' hd
  show deriv (fun t : ℝ => f (z * NormedSpace.exp ((t : ℂ) • X))) 0 = intK c (Dz X G) z
  have heq : (fun t : ℝ => f (z * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0]
      fun t => ∫ k, G (pk k, z * NormedSpace.exp ((t : ℂ) • X)) * c k ∂(muK ε) := by
    filter_upwards [hs] with t ht
    exact (ht (hpJ t)).2
  rw [heq.deriv_eq, key.deriv]
  simp [intK]

theorem eword_intK {ε : Fin n → Bool} {c : KG ε → ℂ} (hc : Continuous c)
    {G : (Mt × Mt) × Mt → ℂ} (hG : AnalyticOnNhd ℂ G (Om3 n)) {f : Mt → ℂ} {z : Mt}
    (h : ∀ᶠ y in 𝓝 z, inUJ ε y → y ∈ U1 ε ∧ f y = intK c G y) (w : List (Fin n × Fin n)) :
    ∀ᶠ y in 𝓝 z, inUJ ε y → y ∈ U1 ε ∧ Eword ε w f y = intK c (Dw w G) y := by
  induction w with
  | nil => exact h
  | cons p w ih =>
    have cm := Formalism.REAL.complex_parts_mem_lie_algebra_holds n ε (Matrix.single p.1 p.2 1)
    filter_upwards [ih.eventually_nhds] with y hy hyJ
    have hU : y ∈ U1 ε := (hy.self_of_nhds hyJ).1
    refine ⟨hU, ?_⟩
    show Formalism.REAL.Rd (Formalism.REAL.cpart1 ε (Matrix.single p.1 p.2 1)) (Eword ε w f) y +
        Complex.I * Formalism.REAL.Rd (Formalism.REAL.cpart2 ε (Matrix.single p.1 p.2 1)) (Eword ε w f) y =
      intK c (Dz (Matrix.single p.1 p.2 1) (Dw w G)) y
    rw [rd_intK hc (analytic_Dw hG w) hyJ cm.1 hy, rd_intK hc (analytic_Dw hG w) hyJ cm.2.1 hy]
    have hDz : ∀ x : (Mt × Mt) × Mt, Dz (Matrix.single p.1 p.2 1) (Dw w G) x =
        Dz (Formalism.REAL.cpart1 ε (Matrix.single p.1 p.2 1)) (Dw w G) x +
          Complex.I * Dz (Formalism.REAL.cpart2 ε (Matrix.single p.1 p.2 1)) (Dw w G) x := by
      intro x
      have e : ((0 : Mt × Mt), x.2 * Matrix.single p.1 p.2 1) =
          ((0 : Mt × Mt), x.2 * Formalism.REAL.cpart1 ε (Matrix.single p.1 p.2 1)) +
            Complex.I • ((0 : Mt × Mt), x.2 * Formalism.REAL.cpart2 ε (Matrix.single p.1 p.2 1)) := by
        conv_lhs => rw [cm.2.2.1]
        simp [Matrix.mul_add]
      simp only [Dz]
      rw [e, map_add, map_smul, smul_eq_mul]
    have hA := integrable_slice hc (analytic_Dz (analytic_Dw hG w) (Formalism.REAL.cpart1 ε (Matrix.single p.1 p.2 1))) hU
    have hB := integrable_slice hc (analytic_Dz (analytic_Dw hG w) (Formalism.REAL.cpart2 ε (Matrix.single p.1 p.2 1))) hU
    simp only [intK]
    rw [← integral_const_mul, ← integral_add hA (hB.const_mul _)]
    congr 1
    funext k
    rw [hDz]
    ring

theorem continuous_tau {ε : Fin n → Bool} {abelian₂ : Fin n → ℝ} {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {τ : Mt → (W →L[ℂ] W)} {w : W} (h : IsTau ε abelian₂ τ w) (v : W) :
    Continuous (fun k : KG ε => τ (toMK k) v) := by
  obtain ⟨hfd, -, hdiff, -⟩ := h
  have := hfd
  let b := stdOrthonormalBasis ℂ W
  have hK : ∀ k : KG ε, toMK k ∈ KC ε := fun k =>
    ⟨Units.isUnit _, ((Formalism.REAL.mem_KG ε _).1 k.2).2⟩
  have hc : ∀ i, Continuous (fun k : KG ε => ⟪b i, τ (toMK k) v⟫_ℂ) := fun i =>
    (hdiff (b i) v).continuousOn.comp_continuous (continuous_toMK ε) fun k => hK k
  have e : (fun k : KG ε => τ (toMK k) v) = fun k => ∑ i, ⟪b i, τ (toMK k) v⟫_ℂ • b i := by
    funext k; exact (b.sum_repr' _).symm
  rw [e]
  exact continuous_finsetSum _ fun i _ => (hc i).smul continuous_const

private theorem compactSpace_KG''' (ε : Fin n → Bool) : CompactSpace (KG ε) := by
  have hKc : IsCompact (Kset ε) := (Formalism.REAL.maximal_compact_facts n ε).2.1
  have hrange : Set.range (fun k : KG ε => toMK k) = Kset ε := by
    ext M
    constructor
    · rintro ⟨k, rfl⟩
      exact (Formalism.REAL.mem_KG ε _).1 k.2
    · intro hM
      exact ⟨⟨⟨⟨M, star M, Matrix.mem_unitaryGroup_iff.1 hM.1, Matrix.mem_unitaryGroup_iff'.1 hM.1⟩,
        (Formalism.REAL.maximal_compact_facts n ε).1 M hM⟩, (Formalism.REAL.mem_KG ε _).2 hM⟩, rfl⟩
  have h1 : Topology.IsInducing (fun k : KG ε => Units.embedProduct Mt ((k : UJ ε) : Mtˣ)) :=
    Units.isEmbedding_embedProduct.isInducing.comp
      (Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal)
  have hg : Continuous (fun M : Mt => (M, MulOpposite.op Mᴴ)) :=
    continuous_id.prodMk (MulOpposite.continuous_op.comp continuous_id.matrix_conjTranspose)
  have hind : Topology.IsInducing (fun k : KG ε => toMK k) := by
    refine Topology.IsInducing.of_comp (continuous_toMK ε) hg ?_
    convert h1 using 1
    funext k
    have hu : toMK k ∈ Matrix.unitaryGroup (Fin n) ℂ := ((Formalism.REAL.mem_KG ε _).1 k.2).1
    have hs : toMK k * (toMK k)ᴴ = 1 := by
      rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.1 hu
    simp only [Function.comp_apply, Units.embedProduct_apply]
    exact Prod.ext rfl (congrArg MulOpposite.op (Units.eq_inv_of_mul_eq_one_left hs))
  have hc : IsCompact (Set.univ : Set (KG ε)) := by
    rw [hind.isCompact_iff, Set.image_univ, hrange]; exact hKc
  exact isCompact_univ_iff.1 hc

theorem inner_ps {ε : Fin n → Bool} (lam : Fin n → ℝ) {abelian₂ : Fin n → ℝ} {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {τ : Mt → (W →L[ℂ] W)} {w : W} (h : IsTau ε abelian₂ τ w) (u v : W) {z : Mt}
    (hz : z ∈ U1 ε) :
    ⟪u, ps ε lam τ w z v⟫_ℂ =
      intK (fun k : KG ε => (Module.finrank ℂ W : ℂ) * (⟪τ (toMK k) w, v⟫_ℂ * ⟪u, τ (toMK k) w⟫_ℂ))
        (fun x : (Mt × Mt) × Mt => Phi lam (x.1.1 * x.2 * x.1.2)) z := by
  have hcK := compactSpace_KG''' ε
  have hP : IsProbabilityMeasure (muK ε) := (Formalism.REAL.kHaar n ε).1
  have hfd : FiniteDimensional ℂ W := h.1
  have hPhi : Continuous (fun k : KG ε => Phi lam ((toMK k)⁻¹ * z * toMK k)) :=
    continuous_iff_continuousAt.2 fun k => by
      exact ContinuousAt.comp (f := fun k : KG ε => (pk k, z)) ((analyticOn_leadingMinorPowerProduct_triple lam) _ (pk_mem hz k)).continuousAt
        ((continuous_pk ε).prodMk (continuous_const (y := z))).continuousAt
  have hT : Continuous (fun k : KG ε => τ (toMK k) w) := continuous_tau h w
  have hL : Continuous (fun k : KG ε => innerSL ℂ (τ (toMK k) w)) := (innerSL ℂ).continuous.comp hT
  have hS : Continuous (fun k : KG ε => (innerSL ℂ (τ (toMK k) w)).smulRight (τ (toMK k) w)) := by
    have := ((ContinuousLinearMap.smulRightL ℂ W W).continuous.comp hL).clm_apply hT
    exact this
  have hA : Continuous (fun k : KG ε => Phi lam ((toMK k)⁻¹ * z * toMK k) •
      (innerSL ℂ (τ (toMK k) w)).smulRight (τ (toMK k) w)) := hPhi.smul hS
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hA.continuousOn
  have hInt := Integrable.of_bound (μ := muK ε) hA.aestronglyMeasurable C (ae_of_all _ fun k => hC k trivial)
  have hInt' := hInt.apply_continuousLinearMap v
  show ⟪u, ((Module.finrank ℂ W : ℂ) • ∫ k : KG ε, Phi lam ((toMK k)⁻¹ * z * toMK k) •
      (innerSL ℂ (τ (toMK k) w)).smulRight (τ (toMK k) w) ∂(muK ε)) v⟫_ℂ = _
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.integral_apply hInt, inner_smul_right,
    ← integral_inner hInt']
  simp only [intK]
  rw [← integral_const_mul]
  congr 1
  funext k
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    inner_smul_right, pk]
  ring

private theorem eventually_nhds_one_inUJ_of_eventually_umat {ε : Fin n → Bool} {P : Matrix (Fin n) (Fin n) ℂ → Prop}
    (h : ∀ᶠ g : Formalism.REAL.UJ ε in 𝓝 1, P (umat g)) : ∀ᶠ z in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), inUJ ε z → P z := by
  have hind : Topology.IsInducing (fun g : Formalism.REAL.UJ ε => Units.embedProduct (Matrix (Fin n) (Fin n) ℂ) (g : (Matrix (Fin n) (Fin n) ℂ)ˣ)) :=
    Units.isEmbedding_embedProduct.isInducing.comp Topology.IsInducing.subtypeVal
  rw [hind.nhds_eq_comap] at h
  obtain ⟨O, hO, hOS⟩ := Filter.mem_comap.1 h
  have hφ : Continuous (fun z : Matrix (Fin n) (Fin n) ℂ => (z, MulOpposite.op (Formalism.REAL.Jm ε * zᴴ * Formalism.REAL.Jm ε))) :=
    continuous_id.prodMk (MulOpposite.continuous_op.comp
      ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const))
  have h1 : (fun z : Matrix (Fin n) (Fin n) ℂ => (z, MulOpposite.op (Formalism.REAL.Jm ε * zᴴ * Formalism.REAL.Jm ε))) 1 =
      Units.embedProduct (Matrix (Fin n) (Fin n) ℂ) ((1 : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) := by
    simp [Formalism.REAL.Jm_mul_self]
  have hO' : O ∈ 𝓝 ((fun z : Matrix (Fin n) (Fin n) ℂ => (z, MulOpposite.op (Formalism.REAL.Jm ε * zᴴ * Formalism.REAL.Jm ε))) 1) := by
    rw [h1]; exact hO
  filter_upwards [hφ.continuousAt.preimage_mem_nhds hO'] with z hz hzJ
  have hz' : zᴴ * Formalism.REAL.Jm ε * z = Formalism.REAL.Jm ε := hzJ
  have hl : Formalism.REAL.Jm ε * zᴴ * Formalism.REAL.Jm ε * z = 1 := by
    calc Formalism.REAL.Jm ε * zᴴ * Formalism.REAL.Jm ε * z = Formalism.REAL.Jm ε * (zᴴ * Formalism.REAL.Jm ε * z) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hz', Formalism.REAL.Jm_mul_self]
  have hr : z * (Formalism.REAL.Jm ε * zᴴ * Formalism.REAL.Jm ε) = 1 := mul_eq_one_comm.1 hl
  let u : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨z, Formalism.REAL.Jm ε * zᴴ * Formalism.REAL.Jm ε, hr, hl⟩
  let g : Formalism.REAL.UJ ε := ⟨u, hzJ⟩
  exact hOS (show Units.embedProduct (Matrix (Fin n) (Fin n) ℂ) (g : (Matrix (Fin n) (Fin n) ℂ)ˣ) ∈ O from hz)

theorem psiEigen_of (h1 : PhiEigen) (h2 : PsLocal) (h3 : PsiAnalytic) : PsiEigen := by
  intro n ε lam W _ _ τ w hlam htau u v
  set f : Matrix (Fin n) (Fin n) ℂ → ℂ := fun g => ⟪u, Psi ε lam τ w g v⟫_ℂ with hf
  have hLoc : LocAn ε f := by
    intro g hg
    obtain ⟨F, hF, hev⟩ := h3 n ε lam W τ w hlam htau u v g hg
    exact ⟨F, hF, hev⟩
  have hsm : SmoothOnG ε f := hLoc.smooth
  refine ⟨hsm, ?_⟩
  unfold IsZEigen
  refine ⟨hsm, fun m g hg => ?_⟩
  set c0 : ℂ := gelfVal (fun a => -(lam a : ℂ)) (m + 1) with hc0
  have hD : LocAn ε (fun g => gelf ε m f g + (-c0) * f g) := (hLoc.gelf m).add (hLoc.const_mul (-c0))
  suffices hz : ∀ᶠ z in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), inUJ ε z → gelf ε m f z + (-c0) * f z = 0 by
    have := hD.eq_zero hz hg
    linear_combination this
  have hloc := eventually_nhds_one_inUJ_of_eventually_umat (P := fun z => z ∈ U1 ε ∧ Psi ε lam τ w z = ps ε lam τ w z)
    (h2 n ε lam W τ w hlam htau)
  set cK : KG ε → ℂ := fun k =>
    (Module.finrank ℂ W : ℂ) * (⟪τ (toMK k) w, v⟫_ℂ * ⟪u, τ (toMK k) w⟫_ℂ) with hcK_def
  set G0 : (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) × Matrix (Fin n) (Fin n) ℂ → ℂ := fun x => Phi lam (x.1.1 * x.2 * x.1.2) with hG0_def
  have hT := continuous_tau htau w
  have hcK : Continuous cK := continuous_const.mul ((hT.inner continuous_const).mul (continuous_const.inner hT))
  have hG0 : AnalyticOnNhd ℂ G0 (Om3 n) := analyticOn_leadingMinorPowerProduct_triple lam
  have hbase : ∀ᶠ y in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), inUJ ε y → y ∈ U1 ε ∧ f y = intK cK G0 y := by
    filter_upwards [hloc] with y hy hyJ
    obtain ⟨hU, hPs⟩ := hy hyJ
    refine ⟨hU, ?_⟩
    show ⟪u, Psi ε lam τ w y v⟫_ℂ = _
    rw [hPs]
    exact inner_ps lam htau u v hU
  have hw : ∀ a : Fin (m + 1) → Fin n, ∀ᶠ y in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), inUJ ε y →
      y ∈ U1 ε ∧ Eword ε (cycWord a) f y = intK cK (Dw (cycWord a) G0) y :=
    fun a => eword_intK hcK hG0 hbase _
  filter_upwards [Filter.eventually_all.2 hw, hbase] with y hy hyb hyJ
  obtain ⟨hU, hfy⟩ := hyb hyJ
  show ∑ a, Eword ε (cycWord a) f y + (-c0) * f y = 0
  rw [Finset.sum_congr rfl fun a _ => (hy a hyJ).2, hfy]
  simp only [intK]
  rw [← integral_finsetSum _ (fun a _ => integrable_slice hcK (analytic_Dw hG0 _) hU)]
  have key : ∀ k : KG ε, ∑ a : Fin (m + 1) → Fin n, Dw (cycWord a) G0 (pk k, y) * cK k =
      c0 * (G0 (pk k, y) * cK k) := by
    intro k
    rw [← Finset.sum_mul]
    have e1 : ∀ a : Fin (m + 1) → Fin n, Dw (cycWord a) G0 (pk k, y) =
        RholW (cycWord a) (fun y' => G0 (pk k, y')) y := fun a =>
      (rholW_eq hG0 (pk k) (cycWord a) y (pk_mem hU k)).symm
    simp only [e1]
    have e2 := h1 n lam hlam (toMK k) y (Units.isUnit _) (pk_mem hU k) m
    have e3 : ∑ a : Fin (m + 1) → Fin n, RholW (cycWord a) (fun y' => G0 (pk k, y')) y =
        gelfH m (fun y' => Phi lam ((toMK k)⁻¹ * y' * toMK k)) y := rfl
    rw [e3, e2]
    simp only [hG0_def, pk]
    ring
  simp only [key]
  rw [integral_const_mul]
  ring

theorem psiEigen : PsiEigen := psiEigen_of GlobalTheory.T.phi_centre_eigenfunction_discrete_series GlobalTheory.T.psi_restriction_holomorphic_near_one GlobalTheory.T.psi_entries_real_analytic

end GlobalTheory.Dec.PsiEig
