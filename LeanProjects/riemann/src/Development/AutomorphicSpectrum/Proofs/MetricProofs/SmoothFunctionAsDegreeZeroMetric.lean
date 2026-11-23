import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHermExtend
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedB
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ContDiff

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Manifold

local notation "𝕟" => ((⊤ : ℕ∞) : WithTop ℕ∞)

namespace SmoothExt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def deproj (p : (k : K) → ι k) (M : (Σ k, ι k × ι k) → ℂ) : (Σ k, ι k) → ℂ :=
  fun q => M ⟨q.1, (q.2, p q.1)⟩ / M ⟨q.1, (p q.1, p q.1)⟩

theorem proj_diag_ne {p : (k : K) → ι k} {z : (Σ k, ι k) → ℂ} (hz : ∀ k, z ⟨k, p k⟩ ≠ 0) (k : K) :
    HermExtend.proj z ⟨k, (p k, p k)⟩ ≠ 0 := by
  have hb : z ∈ HermExtend.blocksNe ι := fun k => ⟨p k, hz k⟩
  have hn : ((HermExtend.blkSq z k : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (HermExtend.blkSq_pos hb k).ne'
  exact mul_ne_zero (mul_ne_zero (hz k) ((map_ne_zero _).2 (hz k))) (inv_ne_zero hn)

theorem deproj_proj {p : (k : K) → ι k} {z : (Σ k, ι k) → ℂ} (hz : ∀ k, z ⟨k, p k⟩ ≠ 0) :
    deproj p (HermExtend.proj z) = affCoord p z := by
  funext q
  obtain ⟨k, i⟩ := q
  have hb : z ∈ HermExtend.blocksNe ι := fun k => ⟨p k, hz k⟩
  have hn : ((HermExtend.blkSq z k : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (HermExtend.blkSq_pos hb k).ne'
  have hc : starRingEnd ℂ (z ⟨k, p k⟩) ≠ 0 := (map_ne_zero _).2 (hz k)
  have h1 := hz k
  simp only [deproj, HermExtend.proj, affCoord]
  field_simp

theorem contDiffAt_deproj (p : (k : K) → ι k) {M : (Σ k, ι k × ι k) → ℂ}
    (hM : ∀ k, M ⟨k, (p k, p k)⟩ ≠ 0) : ContDiffAt ℝ 𝕟 (deproj p) M := by
  refine contDiffAt_pi.2 fun q => ?_
  simp only [deproj, div_eq_mul_inv]
  exact (contDiff_apply ℝ ℂ _).contDiffAt.mul
    (ContDiffAt.inv (contDiff_apply ℝ ℂ _).contDiffAt (hM q.1))

theorem proj_eq_of_sameOrbit {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    HermExtend.proj z = HermExtend.proj z' := by
  obtain ⟨c, hc, rfl⟩ := h
  exact HermExtend.proj_smul c hc z'

theorem exists_localLeftInverse {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {a : E → F} {y₀ : E} (ha : AnalyticAt ℂ a y₀) (hk : (fderiv ℂ a y₀).ker = ⊥) :
    ∃ r : F → E, (∀ᶠ w in 𝓝 (a y₀), AnalyticAt ℂ r w) ∧ r (a y₀) = y₀ ∧
      ∀ᶠ y in 𝓝 y₀, r (a y) = y := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℂ E
  haveI : CompleteSpace F := FiniteDimensional.complete ℂ F
  have hT : HasFDerivAt a (fderiv ℂ a y₀) y₀ := ha.differentiableAt.hasFDerivAt
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective
    ((fderiv ℂ a y₀ : E →L[ℂ] F) : E →ₗ[ℂ] F) hk
  let Lc : F →L[ℂ] E := LinearMap.toContinuousLinearMap L
  have hLT : Lc.comp (fderiv ℂ a y₀) = ((ContinuousLinearEquiv.refl ℂ E : E ≃L[ℂ] E) : E →L[ℂ] E) := by
    ext v
    exact LinearMap.congr_fun hL v
  have hψ : AnalyticAt ℂ (fun y => Lc (a y)) y₀ := Lc.analyticAt _ |>.comp ha
  have hd : HasFDerivAt (fun y => Lc (a y))
      ((ContinuousLinearEquiv.refl ℂ E : E ≃L[ℂ] E) : E →L[ℂ] E) y₀ := by
    rw [← hLT]
    exact Lc.hasFDerivAt.comp y₀ hT
  have hc : ContDiffAt ℂ ω (fun y => Lc (a y)) y₀ := hψ.contDiffAt
  have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  have hg := hc.to_localInverse hd hn
  refine ⟨fun w => hc.localInverse hd hn (Lc w), ?_, hc.localInverse_apply_image hd hn,
    (hc.hasStrictFDerivAt' hd hn).eventually_left_inverse⟩
  have hga : AnalyticAt ℂ (hc.localInverse hd hn) (Lc (a y₀)) := hg.analyticAt
  have ht : Filter.Tendsto Lc (𝓝 (a y₀)) (𝓝 (Lc (a y₀))) := Lc.continuous.tendsto _
  filter_upwards [ht.eventually hga.eventually_analyticAt] with w hw
  exact hw.comp (Lc.analyticAt w)

theorem exists_ext_of_local {X : Type} [TopologicalSpace X] [CompactSpace X] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {g : X → F}
    (hg : Continuous g) (hinj : Function.Injective g) {u : X → ℝ}
    (hloc : ∀ x₀, ∃ f : F → ℝ, (∀ᶠ w in 𝓝 (g x₀), ContDiffAt ℝ 𝕟 f w) ∧
      ∀ᶠ y in 𝓝 x₀, f (g y) = u y) :
    ∃ v : F → ℝ, ContDiff ℝ 𝕟 v ∧ ∀ x, v (g x) = u x := by
  classical
  let t : F → Set ℝ := fun w => {v | ∀ x, g x = w → v = u x}
  have ht : ∀ w, Convex ℝ (t w) := by
    intro w a ha b hb s r hs hr hsr x hx
    show s • a + r • b = u x
    rw [ha x hx, hb x hx, ← add_smul, hsr, one_smul]
  have Hloc : ∀ w, ∃ U ∈ 𝓝 w, ∃ f : F → ℝ, ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, ℝ) 𝕟 f U ∧
      ∀ y ∈ U, f y ∈ t y := by
    intro w
    by_cases hw : w ∈ Set.range g
    · obtain ⟨x₀, rfl⟩ := hw
      obtain ⟨f, hf, hfu⟩ := hloc x₀
      have hN : x₀ ∈ interior {y | f (g y) = u y} := mem_interior_iff_mem_nhds.2 hfu
      have hC : IsClosed (g '' (interior {y | f (g y) = u y})ᶜ) :=
        (isOpen_interior.isClosed_compl.isCompact.image hg).isClosed
      have hx : g x₀ ∉ g '' (interior {y | f (g y) = u y})ᶜ := by
        rintro ⟨y, hy, e⟩
        exact hy (hinj e ▸ hN)
      refine ⟨{w | ContDiffAt ℝ 𝕟 f w} ∩ (g '' (interior {y | f (g y) = u y})ᶜ)ᶜ,
        Filter.inter_mem hf (hC.isOpen_compl.mem_nhds hx), f, ?_, ?_⟩
      · exact contMDiffOn_iff_contDiffOn.2 fun w hw => (show ContDiffAt ℝ 𝕟 f w from hw.1).contDiffWithinAt
      · rintro w ⟨_, hw⟩ x rfl
        have hxN : x ∈ interior {y | f (g y) = u y} := by
          by_contra h
          exact hw ⟨x, h, rfl⟩
        exact (interior_subset hxN : x ∈ {y | f (g y) = u y})
    · refine ⟨(Set.range g)ᶜ, (isCompact_range hg).isClosed.isOpen_compl.mem_nhds hw, fun _ => 0,
        contMDiffOn_const, ?_⟩
      rintro w hw x rfl
      exact absurd ⟨x, rfl⟩ hw
  obtain ⟨v, hv⟩ := exists_contMDiffMap_forall_mem_convex_of_local 𝓘(ℝ, F) (n := (⊤ : ℕ∞)) ht Hloc
  exact ⟨v, contMDiff_iff_contDiff.1 v.contMDiff, fun x => hv (g x) x rfl⟩

variable {P : Ideal (MRing ι)} {D : ℕ}

theorem not_mem_mcPts_top (z : (Σ k, ι k) → ℂ) : z ∉ mcPts (⊤ : Ideal (MRing ι)) := by
  intro h
  have := h.2 1 trivial
  simp at this

theorem continuous_diag (R : AnLogRes P ⊤ D) :
    Continuous fun x => HermExtend.proj (R.lift x x) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  have hU : R.U x₀ ∈ 𝓝 x₀ := (R.isOpen_U x₀).mem_nhds (R.mem_U x₀)
  have hl : ContinuousAt (fun y => R.lift x₀ y) x₀ :=
    continuousAt_pi.2 fun q => (continuousOn_lift R x₀ q).continuousAt hU
  have hb : R.lift x₀ x₀ ∈ HermExtend.blocksNe ι := (R.mem x₀ x₀ (R.mem_U x₀)).1
  have hp : ContinuousAt HermExtend.proj (R.lift x₀ x₀) :=
    HermExtend.contDiffOn_proj.continuousOn.continuousAt (HermExtend.isOpen_blocksNe.mem_nhds hb)
  have hc : ContinuousAt (fun y => HermExtend.proj (R.lift x₀ y)) x₀ :=
    ContinuousAt.comp (f := fun y => R.lift x₀ y) hp hl
  refine hc.congr ?_
  filter_upwards [hU] with y hy
  exact (proj_eq_of_sameOrbit (R.compat y x₀ y ⟨R.mem_U y, hy⟩)).symm

theorem injective_diag (R : AnLogRes P ⊤ D) :
    Function.Injective fun x => HermExtend.proj (R.lift x x) := by
  intro x x' h
  obtain ⟨c, hc, e⟩ := HermExtend.eq_smul_of_proj_eq (R.mem x' x' (R.mem_U x')).1 h
  exact (R.inj x' x (not_mem_mcPts_top _) ⟨c, hc, e⟩).symm

theorem local_ext (R : AnLogRes P ⊤ D) {u : R.X → ℝ} (hu : R.A.Smooth u) (x₀ : R.X) :
    ∃ f : ((Σ k, ι k × ι k) → ℂ) → ℝ,
      (∀ᶠ w in 𝓝 (HermExtend.proj (R.lift x₀ x₀)), ContDiffAt ℝ 𝕟 f w) ∧
      ∀ᶠ y in 𝓝 x₀, f (HermExtend.proj (R.lift y y)) = u y := by
  classical
  have hz₀ : R.lift x₀ x₀ ∈ mcPts P := R.mem x₀ x₀ (R.mem_U x₀)
  choose p hp using hz₀.1
  obtain ⟨j, hj⟩ := R.A.cover x₀
  have hy₀ : R.A.chart j x₀ ∈ (R.A.chart j).target := (R.A.chart j).map_source hj
  have hsy : (R.A.chart j).symm (R.A.chart j x₀) = x₀ := (R.A.chart j).left_inv hj
  have hyT : R.A.chart j x₀ ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x₀ :=
    ⟨hy₀, by rw [Set.mem_preimage, hsy]; exact R.mem_U x₀⟩
  have ha : AnalyticAt ℂ (fun y => affCoord p (R.lift x₀ ((R.A.chart j).symm y)))
      (R.A.chart j x₀) := by
    refine analyticAt_pi_iff.2 fun q => ?_
    have h1 := R.holo x₀ q j _ hyT
    have h2 := R.holo x₀ ⟨q.1, p q.1⟩ j _ hyT
    refine AnalyticAt.div h1 h2 ?_
    simpa [hsy] using hp q.1
  have hk := R.immersion x₀ (not_mem_mcPts_top _) p hp j hj
  obtain ⟨r, hr, hr0, hrl⟩ := exists_localLeftInverse ha hk
  have ha0 : deproj p (HermExtend.proj (R.lift x₀ x₀)) =
      affCoord p (R.lift x₀ ((R.A.chart j).symm (R.A.chart j x₀))) := by
    rw [deproj_proj hp, hsy]
  refine ⟨fun w => u ((R.A.chart j).symm (r (deproj p w))), ?_, ?_⟩
  · have hdp := contDiffAt_deproj p (proj_diag_ne hp)
    have hopen : ∀ᶠ w : (Σ k, ι k × ι k) → ℂ in 𝓝 (HermExtend.proj (R.lift x₀ x₀)),
        ∀ k, w ⟨k, (p k, p k)⟩ ≠ 0 :=
      Filter.eventually_all.2 fun k =>
        ((continuous_apply (⟨k, (p k, p k)⟩ : Σ k, ι k × ι k)).continuousAt).eventually_ne
          (proj_diag_ne hp k)
    have hcont : Filter.Tendsto (deproj p) (𝓝 (HermExtend.proj (R.lift x₀ x₀)))
        (𝓝 (affCoord p (R.lift x₀ ((R.A.chart j).symm (R.A.chart j x₀))))) := by
      rw [← ha0]
      exact hdp.continuousAt.tendsto
    have htar : ∀ᶠ w' in 𝓝 (affCoord p (R.lift x₀ ((R.A.chart j).symm (R.A.chart j x₀)))),
        r w' ∈ (R.A.chart j).target :=
      hr.self_of_nhds.continuousAt.tendsto.eventually_mem
        ((R.A.chart j).open_target.mem_nhds (by rw [hr0]; exact hy₀))
    filter_upwards [hopen, hcont.eventually hr, hcont.eventually htar] with w h1 h2 h3
    have hus : ContDiffAt ℝ 𝕟 (u ∘ (R.A.chart j).symm) (r (deproj p w)) := by
      refine (hu j).contDiffAt ?_
      have : (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' Set.univ = (R.A.chart j).target := by simp
      rw [this]
      exact (R.A.chart j).open_target.mem_nhds h3
    have hrw : ContDiffAt ℝ 𝕟 r (deproj p w) := h2.contDiffAt.restrict_scalars ℝ
    exact ContDiffAt.comp (g := u ∘ (R.A.chart j).symm) w hus (hrw.comp w (contDiffAt_deproj p h1))
  · have hl : ∀ᶠ y in 𝓝 x₀, r (affCoord p (R.lift x₀ ((R.A.chart j).symm (R.A.chart j y)))) =
        R.A.chart j y := ((R.A.chart j).continuousAt hj).tendsto.eventually hrl
    have hU : R.U x₀ ∈ 𝓝 x₀ := (R.isOpen_U x₀).mem_nhds (R.mem_U x₀)
    have hnz : ∀ᶠ y in 𝓝 x₀, ∀ k, R.lift x₀ y ⟨k, p k⟩ ≠ 0 :=
      Filter.eventually_all.2 fun k =>
        ((continuousOn_lift R x₀ ⟨k, p k⟩).continuousAt hU).eventually_ne (hp k)
    filter_upwards [hl, hnz, hU, (R.A.chart j).open_source.mem_nhds hj] with y h1 h2 h3 h4
    have hs : (R.A.chart j).symm (R.A.chart j y) = y := (R.A.chart j).left_inv h4
    rw [hs] at h1
    show u ((R.A.chart j).symm (r (deproj p (HermExtend.proj (R.lift y y))))) = u y
    rw [proj_eq_of_sameOrbit (R.compat y x₀ y ⟨R.mem_U y, h3⟩), deproj_proj h2, h1, hs]

end SmoothExt

theorem exists_hermLine_log_eq_of_smooth :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ)
      (R : AnLogRes P ⊤ D) (u : R.X → ℝ), R.A.Smooth u →
      ∃ B : HermLine ι, B.a = 0 ∧ IsSmoothHerm B ∧ ∀ x, Real.log (B.h (R.lift x x)) = u x := by
  intro K _ ι _ P D R u hu
  obtain ⟨v, hv, hvu⟩ := SmoothExt.exists_ext_of_local (SmoothExt.continuous_diag R)
    (SmoothExt.injective_diag R) (SmoothExt.local_ext R hu)
  refine ⟨{ a := 0, h := fun z => Real.exp (v (HermExtend.proj z)), pos := fun _ _ => Real.exp_pos _,
            smul := fun c z hc => ?_ }, rfl, ?_, fun x => ?_⟩
  · have e : HermExtend.proj (fun p : Σ k, ι k => c p.1 * z p) = HermExtend.proj z :=
      HermExtend.proj_smul c hc z
    simp [e]
  · exact (hv.comp_contDiffOn HermExtend.contDiffOn_proj).exp
  · show Real.log (Real.exp (v (HermExtend.proj (R.lift x x)))) = u x
    rw [Real.log_exp]
    exact hvu x

end GlobalTheory.CompanionTheory.Ar.PB
