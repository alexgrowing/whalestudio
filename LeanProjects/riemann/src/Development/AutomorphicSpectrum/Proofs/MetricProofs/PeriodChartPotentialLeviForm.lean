import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.AnalyticForms.LeviForms.HomDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsOpenFlagDomainNondegenerateMinorsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetComparableGramBoundStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GramLogUnitaryTriangularInvarianceStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalBruhatCellAnalyticCoordinatesStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPotentialLeviFormCellStatement

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

namespace PerDiag

variable {e N : ℕ}

def PlurRe (z0 : Fin e → ℂ) (f : (Fin e → ℂ) → ℝ) : Prop :=
  ∃ H : (Fin e → ℂ) → ℂ, AnalyticAt ℂ H z0 ∧ f =ᶠ[𝓝 z0] fun w => (H w).re

theorem PlurRe.zero (z0 : Fin e → ℂ) : PlurRe z0 fun _ => 0 :=
  ⟨fun _ => 0, analyticAt_const, by simp⟩

theorem PlurRe.congr {z0 : Fin e → ℂ} {f f' : (Fin e → ℂ) → ℝ} (h : PlurRe z0 f)
    (hf : f' =ᶠ[𝓝 z0] f) : PlurRe z0 f' := by
  obtain ⟨H, hH, hev⟩ := h
  exact ⟨H, hH, hf.trans hev⟩

theorem PlurRe.add {z0 : Fin e → ℂ} {f f' : (Fin e → ℂ) → ℝ} (h : PlurRe z0 f)
    (h' : PlurRe z0 f') : PlurRe z0 fun w => f w + f' w := by
  obtain ⟨H, hH, hev⟩ := h
  obtain ⟨H', hH', hev'⟩ := h'
  refine ⟨fun w => H w + H' w, hH.fun_add hH', ?_⟩
  filter_upwards [hev, hev'] with w h1 h2
  simp [h1, h2]

theorem PlurRe.sub {z0 : Fin e → ℂ} {f f' : (Fin e → ℂ) → ℝ} (h : PlurRe z0 f)
    (h' : PlurRe z0 f') : PlurRe z0 fun w => f w - f' w := by
  obtain ⟨H, hH, hev⟩ := h
  obtain ⟨H', hH', hev'⟩ := h'
  refine ⟨fun w => H w - H' w, hH.fun_sub hH', ?_⟩
  filter_upwards [hev, hev'] with w h1 h2
  simp [h1, h2]

theorem PlurRe.sum {z0 : Fin e → ℂ} {ι : Type} [Fintype ι] {f : ι → (Fin e → ℂ) → ℝ}
    (h : ∀ a, PlurRe z0 (f a)) : PlurRe z0 fun w => ∑ a, f a w := by
  choose H hH hev using h
  refine ⟨fun w => ∑ a, H a w, Finset.analyticAt_fun_sum _ fun a _ => hH a, ?_⟩
  filter_upwards [eventually_all.2 hev] with w hw
  simp [hw]

theorem plurRe_log_norm {z0 : Fin e → ℂ} {B : (Fin e → ℂ) → ℂ} (hB : AnalyticAt ℂ B z0)
    (h0 : B z0 ≠ 0) : PlurRe z0 fun w => Real.log ‖B w‖ := by
  have hq : AnalyticAt ℂ (fun w => B w / B z0) z0 := hB.fun_div analyticAt_const h0
  have hs : (fun w => B w / B z0) z0 ∈ Complex.slitPlane := by
    simp [h0]
  refine ⟨fun w => Complex.log (B w / B z0) + Complex.log (B z0),
    (hq.clog hs).fun_add analyticAt_const, ?_⟩
  filter_upwards [hB.continuousAt.eventually_ne h0] with w hw
  simp only [Complex.add_re, Complex.log_re, norm_div]
  rw [Real.log_div (norm_ne_zero_iff.2 hw) (norm_ne_zero_iff.2 h0)]
  ring

def diagLog (b : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) : ℝ :=
  ∑ a : Fin N, if (a : ℕ) < k then Real.log ‖b a a‖ else 0

theorem plurRe_diagLog {z0 : Fin e → ℂ} {b : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ}
    (hb : ∀ a, AnalyticAt ℂ (fun w => b w a a) z0) (h0 : ∀ a, b z0 a a ≠ 0) (k : ℕ) :
    PlurRe z0 fun w => diagLog (b w) k := by
  refine PlurRe.sum fun a => ?_
  by_cases h : (a : ℕ) < k
  · simpa [h] using plurRe_log_norm (hb a) (h0 a)
  · simpa [h] using PlurRe.zero z0

def stepCorr (N j : ℕ) (i : Fin N) (b : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  if (i : ℕ) + 1 ≤ j then diagLog b (N - j + ((i : ℕ) + 1)) - diagLog b (N - j)
  else diagLog b N - diagLog b (N - j) + diagLog b ((i : ℕ) + 1 - j)

theorem plurRe_stepCorr {z0 : Fin e → ℂ} {b : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ}
    (hb : ∀ a, AnalyticAt ℂ (fun w => b w a a) z0) (h0 : ∀ a, b z0 a a ≠ 0) (j : ℕ) (i : Fin N) :
    PlurRe z0 fun w => stepCorr N j i (b w) := by
  have h := plurRe_diagLog hb h0
  by_cases hi : (i : ℕ) + 1 ≤ j
  · simpa [stepCorr, hi] using (h _).sub (h _)
  · simpa [stepCorr, hi] using ((h _).sub (h _)).add (h _)

theorem stepPot_unitary_mul {j : ℕ} {u : Matrix (Fin N) (Fin N) ℂ}
    (hu : gramOf (sigForm N j) u = diagonal fun i => ((sigForm N j i : ℝ) : ℂ))
    (i : Fin N) (g : Matrix (Fin N) (Fin N) ℂ) : stepPot N j i (u * g) = stepPot N j i g := by
  have h k := (GlobalTheory.T.gram_log_unitary_triangular_invariance N (sigForm N j) k g u 1).1 hu
  unfold stepPot
  simp only [h]

theorem stepPot_mul_triangular {j : ℕ} (hj : j ≤ N) {c b : Matrix (Fin N) (Fin N) ℂ}
    (hc : InFlagDomain N j c) (hb : b.BlockTriangular id) (hu : IsUnit b.det) (i : Fin N) :
    stepPot N j i (c * b) = stepPot N j i c + stepCorr N j i b := by
  have h k := (GlobalTheory.T.gram_log_unitary_triangular_invariance N (sigForm N j) k c 1 b).2 hb hu ((GlobalTheory.T.isOpen_flag_domain_nondegenerate_minors N j hj).2 c hc k)
  unfold stepPot stepCorr diagLog
  split_ifs <;> simp only [h] <;> ring

theorem inFlagDomain_base {j : ℕ} : InFlagDomain N j 1 := by
  refine ⟨by simp, ?_⟩
  have h : -gramHead (sigForm N j) (N - j) (1 : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    ext ⟨a, ha⟩ ⟨b, hb⟩
    by_cases hab : a = b
    · subst hab
      simp [gramHead, gramOf, sigForm, ha]
    · have : (⟨a, ha⟩ : {a : Fin N // (a : ℕ) < N - j}) ≠ ⟨b, hb⟩ := fun h => hab (congrArg Subtype.val h)
      simp [gramHead, gramOf, Matrix.one_apply, hab, this]
  rw [h]
  exact Matrix.PosDef.one

theorem continuous_cellMat (N : ℕ) : Continuous (cellMat N) := by
  unfold cellMat
  refine continuous_finset_sum _ fun k _ => (continuous_const_smul _).comp (Continuous.pow ?_ k)
  refine continuous_finset_sum _ fun p _ => ?_
  refine continuous_matrix fun a b => ?_
  simp only [Matrix.single_apply]
  split_ifs
  · exact continuous_apply p
  · exact continuous_const

theorem exists_cell_coords {j : ℕ} (hj : j ≤ N) (gc : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (z0 : Fin e → ℂ) (han : ∀ a b, AnalyticAt ℂ (fun w => gc w a b) z0)
    (hdom : ∀ᶠ w in 𝓝 z0, InFlagDomain N j (gc w)) :
    ∃ z : (Fin e → ℂ) → Pairs N → ℂ, AnalyticAt ℂ z z0 ∧ z z0 = 0 ∧
      (∀ i, PlurRe z0 fun w => stepPot N j i (gc w) - stepPot N j i (cellMat N (z w))) ∧
      ∀ v, fderiv ℂ z z0 v = 0 ↔
        ((gc z0)⁻¹ * Matrix.of fun a b => fderiv ℂ (fun w => gc w a b) z0 v).BlockTriangular id := by
  obtain ⟨u, b₀, hu, hb₀, hdet, hub⟩ := GlobalTheory.T.flag_domain_unitary_triangular N j hj (gc z0) hdom.self_of_nhds
  have hgu : IsUnit (gc z0).det := hdom.self_of_nhds.1
  have huu : IsUnit u.det := by
    have : u.det * (gc z0).det = b₀.det := by rw [← Matrix.det_mul, hub]
    rw [← this] at hdet
    exact isUnit_of_mul_isUnit_left hdet
  have han' : ∀ a b, AnalyticAt ℂ (fun w => (u * gc w) a b) z0 := by
    intro a b
    simp only [Matrix.mul_apply]
    exact Finset.analyticAt_fun_sum _ fun c _ => analyticAt_const.fun_mul (han c b)
  obtain ⟨z, b, hz, hb, hz0, hev, hiff⟩ := GlobalTheory.T.local_bruhat_cell_analytic_coordinates e N (fun w => u * gc w) z0 han'
    (by simpa only [hub] using hb₀) (by simpa only [hub] using hdet)
  refine ⟨z, hz, hz0, fun i => ?_, fun v => ?_⟩
  · have hcell : ∀ᶠ w in 𝓝 z0, InFlagDomain N j (cellMat N (z w)) := by
      have hc : ContinuousAt (fun w => cellMat N (z w)) z0 :=
        (continuous_cellMat N).continuousAt.comp hz.continuousAt
      have hm : {g : Matrix (Fin N) (Fin N) ℂ | InFlagDomain N j g} ∈ 𝓝 (cellMat N (z z0)) := by
        rw [hz0, cellMat_zero N]
        exact (GlobalTheory.T.isOpen_flag_domain_nondegenerate_minors N j hj).1.mem_nhds inFlagDomain_base
      exact hc hm
    obtain ⟨ht, hdb, -⟩ := hev.self_of_nhds
    have hd0 : ∀ a, b z0 a a ≠ 0 := by
      intro a h
      rw [Matrix.det_of_upperTriangular ht] at hdb
      exact hdb.ne_zero (Finset.prod_eq_zero (Finset.mem_univ a) h)
    refine (plurRe_stepCorr (fun a => hb a a) hd0 j i).congr ?_
    filter_upwards [hev, hcell] with w ⟨h1, h2, h3⟩ hw
    rw [← stepPot_unitary_mul hu i (gc w), h3, stepPot_mul_triangular hj hw h1 h2 i]
    ring
  · have hD : (Matrix.of fun a b => fderiv ℂ (fun w => (u * gc w) a b) z0 v) =
        u * Matrix.of fun a b => fderiv ℂ (fun w => gc w a b) z0 v := by
      ext a b
      have h1 : HasFDerivAt (fun w => ∑ c, u a c * gc w c b)
          (∑ c, u a c • fderiv ℂ (fun w => gc w c b) z0) z0 :=
        HasFDerivAt.fun_sum fun c _ => ((han c b).differentiableAt.hasFDerivAt).const_mul (u a c)
      simp only [Matrix.of_apply, Matrix.mul_apply]
      rw [h1.fderiv]
      simp
    rw [hiff v, hD, Matrix.mul_inv_rev]
    have : (gc z0)⁻¹ * u⁻¹ * (u * Matrix.of fun a b => fderiv ℂ (fun w => gc w a b) z0 v) =
        (gc z0)⁻¹ * Matrix.of fun a b => fderiv ℂ (fun w => gc w a b) z0 v := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc u⁻¹, Matrix.nonsing_inv_mul _ huu, Matrix.one_mul]
    rw [this]

def rel (N j : ℕ) (a : Fin N) : ℕ := if (a : ℕ) < N - j then j + a else a - (N - j)

theorem levi_of_cell {j : ℕ} (hj : j ≤ N) (i : Fin N) {z0 : Fin e → ℂ} {f : (Fin e → ℂ) → ℝ}
    {z : (Fin e → ℂ) → Pairs N → ℂ} (hz : AnalyticAt ℂ z z0) (hz0 : z z0 = 0)
    (hf : PlurRe z0 fun w => f w - stepPot N j i (cellMat N (z w))) :
    ContDiffAt ℝ 2 f z0 ∧ ∀ v, levi f z0 v = ∑ p : Pairs N,
      if min (rel N j p.1.1) (rel N j p.1.2) ≤ (i : ℕ) ∧ (i : ℕ) < max (rel N j p.1.1) (rel N j p.1.2)
      then (1 / 2 : ℝ) * ‖fderiv ℂ z z0 v p‖ ^ 2 else 0 := by
  obtain ⟨H, hH, hev⟩ := hf
  let φ : (Pairs N → ℂ) → ℝ := fun y => stepPot N j i (cellMat N y)
  have hφ : ContDiffAt ℝ 2 φ 0 := (GlobalTheory.T.flag_potential_levi_form_cell N j hj i 0).1
  have hφ' : ContDiffAt ℝ 2 φ (z z0) := by rwa [hz0]
  have hzR : ContDiffAt ℝ 2 z z0 := (hz.restrictScalars (𝕜 := ℝ)).contDiffAt
  have hc : ContDiffAt ℝ 2 (φ ∘ z) z0 := hφ'.comp z0 hzR
  have hHR : ContDiffAt ℝ 2 (fun w => (H w).re) z0 :=
    Complex.reCLM.contDiff.contDiffAt.comp z0 ((hH.restrictScalars (𝕜 := ℝ)).contDiffAt)
  have hfe : f =ᶠ[𝓝 z0] fun w => (φ ∘ z) w + 1 * (H w).re := by
    filter_upwards [hev] with w hw
    simp only [Function.comp_apply, φ, one_mul]
    linarith
  refine ⟨(hc.add (contDiffAt_const.mul hHR)).congr_of_eventuallyEq hfe, fun v => ?_⟩
  rw [levi_congr hfe v, levi_add_smul 1 hc hHR v, levi_comp v hz hφ', levi_re_analytic hH v, hz0,
    (GlobalTheory.T.flag_potential_levi_form_cell N j hj i (fderiv ℂ z z0 v)).2]
  simp [rel]

theorem rel_lt {j : ℕ} (hj : j ≤ N) (a : Fin N) : rel N j a < N := by
  have := a.2
  unfold rel
  split_ifs <;> omega

def relF {j : ℕ} (hj : j ≤ N) (a : Fin N) : Fin N := ⟨rel N j a, rel_lt hj a⟩

theorem relF_injective {j : ℕ} (hj : j ≤ N) : Function.Injective (relF (N := N) hj) := by
  intro a b h
  have h' : rel N j a = rel N j b := congrArg Fin.val h
  have ha := a.2
  have hb := b.2
  unfold rel at h'
  ext
  split_ifs at h' <;> omega

def pairMap (σ : Fin N → Fin N) (hσ : Function.Injective σ) (p : Pairs N) : Pairs N :=
  ⟨(min (σ p.1.1) (σ p.1.2), max (σ p.1.1) (σ p.1.2)), min_lt_max.2 (hσ.ne p.2.ne)⟩

theorem pairMap_injective (σ : Fin N → Fin N) (hσ : Function.Injective σ) :
    Function.Injective (pairMap σ hσ) := by
  rintro ⟨⟨p₁, p₂⟩, hp⟩ ⟨⟨q₁, q₂⟩, hq⟩ h
  have h1 : min (σ p₁) (σ p₂) = min (σ q₁) (σ q₂) := congrArg (fun t : Pairs N => t.1.1) h
  have h2 : max (σ p₁) (σ p₂) = max (σ q₁) (σ q₂) := congrArg (fun t : Pairs N => t.1.2) h
  have hp' : p₁ < p₂ := hp
  have hq' : q₁ < q₂ := hq
  rcases le_total (σ p₁) (σ p₂) with a | a <;> rcases le_total (σ q₁) (σ q₂) with c | c
  · rw [min_eq_left a, min_eq_left c] at h1
    rw [max_eq_right a, max_eq_right c] at h2
    obtain rfl := hσ h1
    obtain rfl := hσ h2
    rfl
  · rw [min_eq_left a, min_eq_right c] at h1
    rw [max_eq_right a, max_eq_left c] at h2
    obtain rfl := hσ h1
    obtain rfl := hσ h2
    exact absurd hp' (not_lt.2 hq'.le)
  · rw [min_eq_right a, min_eq_left c] at h1
    rw [max_eq_left a, max_eq_right c] at h2
    obtain rfl := hσ h1
    obtain rfl := hσ h2
    exact absurd hp' (not_lt.2 hq'.le)
  · rw [min_eq_right a, min_eq_right c] at h1
    rw [max_eq_left a, max_eq_left c] at h2
    obtain rfl := hσ h1
    obtain rfl := hσ h2
    rfl

def pairEquiv {j : ℕ} (hj : j ≤ N) : Pairs N ≃ Pairs N :=
  Equiv.ofBijective (pairMap (relF hj) (relF_injective hj))
    (pairMap_injective _ _).bijective_of_finite

theorem pairEquiv_fst_le {j : ℕ} (hj : j ≤ N) (p : Pairs N) (i : Fin N) :
    (pairEquiv hj p).1.1 ≤ i ↔ min (rel N j p.1.1) (rel N j p.1.2) ≤ (i : ℕ) := by
  change min (relF hj p.1.1) (relF hj p.1.2) ≤ i ↔ _
  rw [min_le_iff, min_le_iff]
  rfl

theorem pairEquiv_lt_snd {j : ℕ} (hj : j ≤ N) (p : Pairs N) (i : Fin N) :
    i < (pairEquiv hj p).1.2 ↔ (i : ℕ) < max (rel N j p.1.1) (rel N j p.1.2) := by
  change i < max (relF hj p.1.1) (relF hj p.1.2) ↔ _
  rw [lt_max_iff, lt_max_iff]
  rfl

end PerDiag

open PerDiag in

theorem levi_diagonal_of_isPeriodChart :
    ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ), j ≤ N → ∀ (pot : Ψ × Fin N → LocPot X) (x : X) (V : Set X) (g : Ψ → X → Matrix (Fin N) (Fin N) ℂ), IsPeriodChart A j pot x V g → ∀ k, x ∈ (A.chart k).source → ∃ Lm : (Fin e → ℂ) →ₗ[ℂ] (Ψ × Pairs N → ℂ), (∀ p, ContDiffAt ℝ 2 ((pot p).φ x ∘ (A.chart k).symm) (A.chart k x)) ∧ (∀ (p : Ψ × Fin N) v, levi ((pot p).φ x ∘ (A.chart k).symm) (A.chart k x) v = ∑ q : Pairs N, if q.1.1 ≤ p.2 ∧ p.2 < q.1.2 then (1 / 2 : ℝ) * ‖Lm v (p.1, q)‖ ^ 2 else 0) ∧ (IsFlagImmersionAt A g x → Function.Injective Lm) := by
  intro e X _ A Ψ _ _ N j hj pot x V g hP k hx
  obtain ⟨hV, hxV, hhol, hdom, hpot⟩ := hP
  have hsx : (A.chart k).symm (A.chart k x) = x := (A.chart k).left_inv hx
  have hmem : A.chart k x ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' V :=
    ⟨(A.chart k).map_source hx, by simpa [hsx] using hxV⟩
  have hnhds : (A.chart k).target ∩ (A.chart k).symm ⁻¹' V ∈ 𝓝 (A.chart k x) :=
    ((A.chart k).isOpen_inter_preimage_symm hV).mem_nhds hmem
  have hcell := fun τ => exists_cell_coords hj (fun w => g τ ((A.chart k).symm w)) (A.chart k x)
    (fun a b => hhol τ a b k _ hmem)
    (by filter_upwards [hnhds] with w hw using hdom τ _ hw.2)
  choose z hz hz0 hstep hiff using hcell
  have key := fun p : Ψ × Fin N => levi_of_cell (f := (pot p).φ x ∘ (A.chart k).symm) hj p.2 (hz p.1)
    (hz0 p.1) (by
      obtain ⟨G, hG, hφ⟩ := hpot p
      have h1 : PlurRe (A.chart k x) fun w => (pot p).φ x ((A.chart k).symm w) -
          stepPot N j p.2 (g p.1 ((A.chart k).symm w)) := by
        refine ⟨G ∘ (A.chart k).symm, hG k _ hmem, ?_⟩
        filter_upwards [hnhds] with w hw
        rw [hφ _ hw.2]
        simp
      refine (h1.add (hstep p.1 p.2)).congr (Eventually.of_forall fun w => ?_)
      simp)
  let ρ := pairEquiv (N := N) hj
  let Lm : (Fin e → ℂ) →ₗ[ℂ] (Ψ × Pairs N → ℂ) :=
    { toFun := fun v q => fderiv ℂ (z q.1) (A.chart k x) v (ρ.symm q.2)
      map_add' := fun v w => by ext q; simp
      map_smul' := fun c v => by ext q; simp }
  refine ⟨Lm, fun p => (key p).1, fun p v => ?_, fun hI => ?_⟩
  · rw [(key p).2 v]
    refine Eq.trans ?_ (Equiv.sum_comp ρ _)
    refine Finset.sum_congr rfl fun q _ => ?_
    have e3 : Lm v (p.1, ρ q) = fderiv ℂ (z p.1) (A.chart k x) v q := by simp [Lm]
    simp only [e3, pairEquiv_fst_le, ρ, pairEquiv_lt_snd]
  · refine (injective_iff_map_eq_zero Lm).2 fun v hv => ?_
    refine hI k hx v fun τ => ?_
    have h0 : fderiv ℂ (z τ) (A.chart k x) v = 0 := by
      funext q
      have := congrFun hv (τ, ρ q)
      simpa [Lm] using this
    have := (hiff τ v).1 h0
    rwa [hsx] at this

end GlobalTheory.CompanionTheory.Ar.PB
