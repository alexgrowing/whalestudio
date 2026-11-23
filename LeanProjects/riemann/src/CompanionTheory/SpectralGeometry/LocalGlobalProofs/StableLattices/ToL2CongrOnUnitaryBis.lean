import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HaarExists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.InfChar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RightDerivativeToL2
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NilpotentRightRule

noncomputable section

open Finset Matrix MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GlobalTheory.CompanionTheory.PackEmb

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.L ReciprocityTheory.ChartRestriction.DS GlobalTheory.CompanionTheory.RightRule

variable {n : ℕ} {ε : Fin n → Bool}

def ContOK (ε : Fin n → Bool) (X : GMod n) (c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) : Prop :=
  ∀ u, ContinuousOn (c u) {g | Formalism.REAL.inUJ ε g}

theorem tens_cont {X : GMod n} {c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)} (h : ContOK ε X c) (j : Fin n) :
    ContOK ε (tens X) (tensCoef X c j) := by
  intro u
  show ContinuousOn (fun g : Matrix (Fin n) (Fin n) ℂ => ∑ i, g j i * c (u i) g) _
  refine continuousOn_finset_sum _ fun i _ => ContinuousOn.mul ?_ (h (u i))
  exact (continuous_id.matrix_elem j i).continuousOn

theorem step_cont {X : GMod n} {c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)} (h : ContOK ε X c) (z : ℂ) (j : Fin n) :
    ContOK ε (step X z) (stepCoef X z c j) :=
  fun u => tens_cont h j ((stepSub X z).subtype u)

theorem path_cont : ∀ (ss : List (Fin n)) (X : GMod n)
    (c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (χ : Fin n → ℂ) (js : List (Fin n)),
    ContOK ε X c → ContOK ε (path X χ ss) (pathCoef X c χ ss js)
  | [], _, _, _, _, h => h
  | s :: ss, X, c, χ, js, h => path_cont ss (step X (χ s)) (stepCoef X (χ s) c (js.headD s)) (χ + Pi.single s 1) js.tail
      (step_cont h _ _)

theorem base_cont {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hE : Formalism.REAL.GlRel E) (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (ξ : H) :
    ContOK ε ⟨D, E, hE⟩ (baseCoef σ D ξ) := by
  intro u
  exact (innerSL ℂ ξ).continuous.comp_continuousOn (hσ.2.2 (u : H))

theorem path_sep : ∀ (ss : List (Fin n)) (X : GMod n) (χ : Fin n → ℂ)
    (C : Set (X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ))), (∀ x : X.V, x ≠ 0 → ∃ c ∈ C, c x 1 ≠ 0) →
    ∀ u : (path X χ ss).V, u ≠ 0 → ∃ c ∈ C, ∃ js, pathCoef X c χ ss js u 1 ≠ 0
  | [], X, χ, C, h, u, hu => by
      obtain ⟨c, hc, h1⟩ := h u hu
      exact ⟨c, hc, [], h1⟩
  | s :: ss, X, χ, C, h, u, hu => by
      have hC : ∀ x : (step X (χ s)).V, x ≠ 0 → ∃ c' ∈ {c' | ∃ c ∈ C, ∃ j, c' = stepCoef X (χ s) c j}, c' x 1 ≠ 0 := by
        intro x hx
        let S : (step X (χ s)).V →ₗ[ℂ] (Fin n → X.V) := (stepSub X (χ s)).subtype
        have hinj : Function.Injective S := Submodule.injective_subtype _
        have hx' : ∃ j, S x j ≠ 0 := by
          by_contra hcon
          push_neg at hcon
          exact hx (hinj ((funext hcon).trans (map_zero S).symm))
        obtain ⟨j, hj⟩ := hx'
        obtain ⟨c, hc, h1⟩ := h _ hj
        refine ⟨stepCoef X (χ s) c j, ⟨c, hc, j, rfl⟩, ?_⟩
        show ∑ i, (1 : Matrix (Fin n) (Fin n) ℂ) j i * c (S x i) 1 ≠ 0
        simpa [Matrix.one_apply] using h1
      obtain ⟨c', ⟨c, hc, j, rfl⟩, js, h1⟩ := path_sep ss (step X (χ s)) (χ + Pi.single s 1) _ hC u hu
      exact ⟨c, hc, j :: js, h1⟩

theorem eab_of_rightOK {X : GMod n} {c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)} (hR : RightOK ε X c)
    (a b : Fin n) (u : X.V) {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.Eab ε a b (c u) g = c (X.E a b u) g := by
  obtain ⟨h1, h2, h3, -⟩ := Formalism.REAL.complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b (1 : ℂ))
  set P := Formalism.REAL.cpart1 ε (Matrix.single a b (1 : ℂ)) with hP
  set Q := Formalism.REAL.cpart2 ε (Matrix.single a b (1 : ℂ)) with hQ
  have e1 : Formalism.REAL.Rd P (c u) g = c (∑ p, ∑ q, P p q • X.E p q u) g := (hR u P h1 g hg).deriv
  have e2 : Formalism.REAL.Rd Q (c u) g = c (∑ p, ∑ q, Q p q • X.E p q u) g := (hR u Q h2 g hg).deriv
  have e3 : Formalism.REAL.Eab ε a b (c u) g = Formalism.REAL.Rd P (c u) g + Complex.I * Formalism.REAL.Rd Q (c u) g := rfl
  have e4 : X.E a b u = (∑ p, ∑ q, P p q • X.E p q u) + Complex.I • ∑ p, ∑ q, Q p q • X.E p q u := by
    have e5 : ∀ p q, (Matrix.single a b (1 : ℂ)) p q = P p q + Complex.I * Q p q := fun p q => by
      conv_lhs => rw [h3]
      simp
    have e6 : X.E a b u = ∑ p, ∑ q, (Matrix.single a b (1 : ℂ)) p q • X.E p q u := by
      simp [Matrix.single_apply, ite_and, Finset.sum_ite_eq]
    rw [e6, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine sum_congr rfl fun p _ => ?_
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    refine sum_congr rfl fun q _ => ?_
    rw [e5, add_smul, mul_smul]
  rw [e3, e1, e2, e4, map_add, map_smul]
  rfl

section Log

open Filter Topology
open scoped Matrix.Norms.Operator

theorem exp_cont : Continuous (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) :=
  NormedSpace.exp_continuous

theorem exp_flip {Y m : Matrix (Fin n) (Fin n) ℂ} (hr : NormedSpace.exp Y = m) (hu : Formalism.REAL.inUJ ε m) :
    NormedSpace.exp (-(Formalism.REAL.Jm ε * Yᴴ * Formalism.REAL.Jm ε)) = m := by
  have h1 : -(Formalism.REAL.Jm ε * Yᴴ * Formalism.REAL.Jm ε) = Formalism.REAL.Jm ε * (-Yᴴ) * (Formalism.REAL.Jm ε)⁻¹ := by
    rw [Formalism.REAL.f1alg_inv_J, Matrix.mul_neg, Matrix.neg_mul]
  have hB : NormedSpace.exp (-Yᴴ) * mᴴ = 1 := by
    rw [← hr, ← Matrix.exp_conjTranspose, ← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Yᴴ)),
      neg_add_cancel, NormedSpace.exp_zero]
  have hu' : mᴴ * Formalism.REAL.Jm ε * m = Formalism.REAL.Jm ε := hu
  rw [h1, Matrix.exp_conj _ _ (Formalism.REAL.f1alg_isUnit_J ε), Formalism.REAL.f1alg_inv_J]
  calc Formalism.REAL.Jm ε * NormedSpace.exp (-Yᴴ) * Formalism.REAL.Jm ε
      = Formalism.REAL.Jm ε * NormedSpace.exp (-Yᴴ) * (mᴴ * Formalism.REAL.Jm ε * m) := by rw [hu']
    _ = Formalism.REAL.Jm ε * (NormedSpace.exp (-Yᴴ) * mᴴ) * Formalism.REAL.Jm ε * m := by simp only [Matrix.mul_assoc]
    _ = m := by rw [hB, Matrix.mul_one, Formalism.REAL.Jm_mul_self, Matrix.one_mul]

theorem logcurve (n : ℕ) (ε : Fin n → Bool) (m : ℝ → Matrix (Fin n) (Fin n) ℂ) (Y₀ : Matrix (Fin n) (Fin n) ℂ) (s₀ : ℝ)
    (hm : ∀ i j, HasDerivAt (fun s => m s i j) (Y₀ i j) s₀) (h1 : m s₀ = 1)
    (hU : ∀ᶠ s in nhds s₀, Formalism.REAL.inUJ ε (m s)) :
    ∃ Y : ℝ → Matrix (Fin n) (Fin n) ℂ, (∀ i j, HasDerivAt (fun s => Y s i j) (Y₀ i j) s₀) ∧ Y s₀ = 0 ∧
      ∀ᶠ s in nhds s₀, Formalism.REAL.inG ε (Y s) ∧ NormedSpace.exp (Y s) = m s := by
  have hS : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      ((ContinuousLinearEquiv.refl ℝ (Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ ≃L[ℝ] Matrix (Fin n) (Fin n) ℂ) :
        Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) 0 :=
    hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Matrix (Fin n) (Fin n) ℂ)
  have hLd := hS.to_localInverse
  have hLl := hS.eventually_left_inverse
  have hLr := hS.eventually_right_inverse
  set L := hS.localInverse _ _ _ with hL
  rw [NormedSpace.exp_zero] at hLd hLr
  have hmd : HasDerivAt m Y₀ s₀ := by
    have e : m = fun s => ∑ i, ∑ j, m s i j • Matrix.single i j (1 : ℂ) := by
      funext s
      conv_lhs => rw [Matrix.matrix_eq_sum_single (m s)]
      simp [Matrix.smul_single]
    have e2 : Y₀ = ∑ i, ∑ j, Y₀ i j • Matrix.single i j (1 : ℂ) := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single Y₀]
      simp [Matrix.smul_single]
    rw [e, e2]
    exact HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => (hm i j).smul_const _
  have hYd : HasDerivAt (fun s => L (m s)) Y₀ s₀ := by
    exact hLd.hasFDerivAt.comp_hasDerivAt_of_eq s₀ hmd h1.symm
  have hY0 : L (m s₀) = 0 := by
    have h := hLl.self_of_nhds
    rw [NormedSpace.exp_zero] at h
    rw [h1]
    exact h
  have hYt : Tendsto (fun s => L (m s)) (𝓝 s₀) (𝓝 0) := by
    have h := hYd.continuousAt.tendsto
    rwa [hY0] at h
  have hmt : Tendsto m (𝓝 s₀) (𝓝 1) := by
    have h := hmd.continuousAt.tendsto
    rwa [h1] at h
  have hflip : Continuous (fun Z : Matrix (Fin n) (Fin n) ℂ => -(Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε)) :=
    ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const).neg
  have hYt' : Tendsto (fun s => -(Formalism.REAL.Jm ε * (L (m s))ᴴ * Formalism.REAL.Jm ε)) (𝓝 s₀) (𝓝 0) := by
    have h : Tendsto (fun s => -(Formalism.REAL.Jm ε * (L (m s))ᴴ * Formalism.REAL.Jm ε)) (𝓝 s₀)
        (𝓝 (-(Formalism.REAL.Jm ε * (0 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε))) := (hflip.tendsto 0).comp hYt
    simpa using h
  refine ⟨fun s => L (m s), fun i j => ?_, hY0, ?_⟩
  · exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)).hasFDerivAt.comp_hasDerivAt s₀ hYd
  · filter_upwards [hYt'.eventually hLl, hmt.eventually hLr, hU] with s h2 hr hu
    refine ⟨?_, hr⟩
    have hEq : -(Formalism.REAL.Jm ε * (L (m s))ᴴ * Formalism.REAL.Jm ε) = L (m s) := by
      have h3 := exp_flip hr hu
      rw [h3] at h2
      exact h2.symm
    show (L (m s))ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * L (m s) = 0
    have h4 : Formalism.REAL.Jm ε * L (m s) = -((L (m s))ᴴ * Formalism.REAL.Jm ε) := by
      calc Formalism.REAL.Jm ε * L (m s) = Formalism.REAL.Jm ε * -(Formalism.REAL.Jm ε * (L (m s))ᴴ * Formalism.REAL.Jm ε) := by rw [hEq]
        _ = -((L (m s))ᴴ * Formalism.REAL.Jm ε) := by
          rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.one_mul]
    rw [h4, add_neg_cancel]

end Log

section Smooth

open Filter Topology Asymptotics Set
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem frechet (n : ℕ) (ε : Fin n → Bool) (X : GMod n) (c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ))
    (hR : RightOK ε X c) (hC : ContOK ε X c) (u : X.V)
    (g : Matrix (Fin n) (Fin n) ℂ) (hg : Formalism.REAL.inUJ ε g) (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Y : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.inG ε Y → (∀ i j, ‖Y i j‖ < δ) →
      ‖c u (g * NormedSpace.exp Y) - c u g - c (∑ a, ∑ b, Y a b • X.E a b u) g‖ ≤ η * ∑ a, ∑ b, ‖Y a b‖ := by
  have hΨ : Tendsto (fun Z : Matrix (Fin n) (Fin n) ℂ => g * NormedSpace.exp Z) (𝓝 0) (𝓝 g) := by
    have h : Continuous (fun Z : Matrix (Fin n) (Fin n) ℂ => g * NormedSpace.exp Z) :=
      continuous_const.matrix_mul exp_cont
    have h2 := h.tendsto 0
    simpa [NormedSpace.exp_zero] using h2
  have hQ : ∀ᶠ x in 𝓝[{g | Formalism.REAL.inUJ ε g}] g, ∀ a b, ‖c (X.E a b u) x - c (X.E a b u) g‖ < η := by
    refine eventually_all.mpr fun a => eventually_all.mpr fun b => ?_
    have h := Metric.tendsto_nhds.mp ((hC (X.E a b u)) g hg) η hη
    simpa [dist_eq_norm] using h
  obtain ⟨U, hU, hUs⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hQ
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hΨ hU)
  refine ⟨r, hr, fun Y hY hYs => ?_⟩
  set T : ℂ := c (∑ a, ∑ b, Y a b • X.E a b u) g with hT
  have hder : ∀ s : ℝ, HasDerivAt (fun t : ℝ => c u (g * NormedSpace.exp ((t : ℂ) • Y)))
      (c (∑ a, ∑ b, Y a b • X.E a b u) (g * NormedSpace.exp ((s : ℂ) • Y))) s := by
    intro s
    have hgs : Formalism.REAL.inUJ ε (g * NormedSpace.exp ((s : ℂ) • Y)) :=
      slm_inUJ_mul hg (Formalism.REAL.exp_indefinite_unitary_holds n ε Y hY s)
    have h0 := hR u Y hY _ hgs
    have h0' : HasDerivAt (fun t : ℝ => c u (g * NormedSpace.exp ((s : ℂ) • Y) * NormedSpace.exp ((t : ℂ) • Y)))
        (c (∑ a, ∑ b, Y a b • X.E a b u) (g * NormedSpace.exp ((s : ℂ) • Y))) (s - s) := by
      rw [sub_self]
      exact h0
    have h1 : HasDerivAt (fun t : ℝ => c u (g * NormedSpace.exp ((s : ℂ) • Y) * NormedSpace.exp (((t - s : ℝ) : ℂ) • Y)))
        (c (∑ a, ∑ b, Y a b • X.E a b u) (g * NormedSpace.exp ((s : ℂ) • Y))) s :=
      HasDerivAt.comp_sub_const s s h0'
    refine h1.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    show c u (g * NormedSpace.exp ((t : ℂ) • Y)) = c u (g * NormedSpace.exp ((s : ℂ) • Y) * NormedSpace.exp (((t - s : ℝ) : ℂ) • Y))
    rw [Matrix.mul_assoc, ← Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left _).smul_right _), ← add_smul]
    congr 4
    push_cast
    ring_nf
  have hbd : ∀ s ∈ Icc (0:ℝ) 1, ‖c (∑ a, ∑ b, Y a b • X.E a b u) (g * NormedSpace.exp ((s : ℂ) • Y)) - T‖ ≤
      η * ∑ a, ∑ b, ‖Y a b‖ := by
    intro s hs
    have hs' : ‖(s : ℂ) • Y‖ < r := by
      refine (Matrix.norm_lt_iff hr).mpr fun i j => ?_
      rw [Matrix.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
      calc s * ‖Y i j‖ ≤ 1 * ‖Y i j‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
        _ < r := by rw [one_mul]; exact hYs i j
    have hxU : g * NormedSpace.exp ((s : ℂ) • Y) ∈ U := hball (by simpa using hs')
    have hxJ : Formalism.REAL.inUJ ε (g * NormedSpace.exp ((s : ℂ) • Y)) := slm_inUJ_mul hg (Formalism.REAL.exp_indefinite_unitary_holds n ε Y hY s)
    have hq := hUs ⟨hxU, hxJ⟩
    set x := g * NormedSpace.exp ((s : ℂ) • Y) with hx
    have e : c (∑ a, ∑ b, Y a b • X.E a b u) x - T = ∑ a, ∑ b, Y a b * (c (X.E a b u) x - c (X.E a b u) g) := by
      simp only [hT, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
    rw [e, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hq a b).le (norm_nonneg _)
  have h1 : ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt (fun t : ℝ => c u (g * NormedSpace.exp ((t : ℂ) • Y)) - t • T)
      (c (∑ a, ∑ b, Y a b • X.E a b u) (g * NormedSpace.exp ((t : ℂ) • Y)) - T) (Icc (0:ℝ) 1) t := by
    intro t _
    exact (((hder t).sub ((hasDerivAt_id' t).smul_const T)).congr_deriv (by simp)).hasDerivWithinAt
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le h1 hbd (convex_Icc 0 1)
    (⟨le_rfl, zero_le_one⟩ : (0:ℝ) ∈ Icc (0:ℝ) 1) (⟨zero_le_one, le_rfl⟩ : (1:ℝ) ∈ Icc (0:ℝ) 1)
  simp only [Complex.ofReal_one, Complex.ofReal_zero, one_smul, zero_smul, sub_zero, NormedSpace.exp_zero,
    Matrix.mul_one, norm_one, mul_one] at hmv
  rw [sub_right_comm] at hmv
  exact hmv

theorem chain {X : GMod n} {c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)} (hR : RightOK ε X c)
    (hC : ContOK ε X c) (u : X.V) {cv : ℝ → Matrix (Fin n) (Fin n) ℂ} {cv' : Matrix (Fin n) (Fin n) ℂ} {s0 : ℝ}
    (hc : HasDerivAt cv cv' s0) (hcU : ∀ᶠ s in 𝓝 s0, Formalism.REAL.inUJ ε (cv s)) :
    HasDerivAt (fun s => c u (cv s))
      (∑ a, ∑ b, (slmJi ε (cv s0) * cv') a b * c (X.E a b u) (cv s0)) s0 := by
  have hg : Formalism.REAL.inUJ ε (cv s0) := hcU.self_of_nhds
  set g := cv s0 with hgdef
  have hmd : HasDerivAt (fun s => slmJi ε g * cv s) (slmJi ε g * cv') s0 := by
    have h := slm_hd_mul (hasDerivAt_const s0 (slmJi ε g)) hc
    simpa using h
  obtain ⟨Y, hY, hY0, hYe⟩ := logcurve n ε (fun s => slmJi ε g * cv s) (slmJi ε g * cv') s0
    (slm_hd_iff.mp hmd) (slm_Ji_mul hg) (by
      filter_upwards [hcU] with s hs
      exact slm_inUJ_mul (slm_Ji_inUJ hg) hs)
  set A : Fin n → Fin n → ℂ := fun a b => c (X.E a b u) g with hA
  have hT : ∀ Z : Matrix (Fin n) (Fin n) ℂ, c (∑ a, ∑ b, Z a b • X.E a b u) g = ∑ a, ∑ b, Z a b * A a b := by
    intro Z
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hA]
  have hTd : HasDerivAt (fun s => ∑ a, ∑ b, Y s a b * A a b) (∑ a, ∑ b, (slmJi ε g * cv') a b * A a b) s0 :=
    HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun b _ => (hY a b).mul_const (A a b)
  set R : ℝ → ℂ := fun s => c u (g * NormedSpace.exp (Y s)) - c u g - ∑ a, ∑ b, Y s a b * A a b with hRdef
  have hYt : ∀ a b, Tendsto (fun s => Y s a b) (𝓝 s0) (𝓝 0) := fun a b => by
    have := (hY a b).continuousAt.tendsto
    simpa [hY0] using this
  have hRo : R =o[𝓝 s0] (fun s => ∑ a, ∑ b, ‖Y s a b‖) := by
    rw [isLittleO_iff]
    intro η hη
    obtain ⟨δ, hδ, hF⟩ := frechet n ε X c hR hC u g hg η hη
    have hsm : ∀ᶠ s in 𝓝 s0, ∀ a b, ‖Y s a b‖ < δ := by
      refine eventually_all.mpr fun a => eventually_all.mpr fun b => ?_
      have := (hYt a b).norm
      rw [norm_zero] at this
      exact this.eventually (gt_mem_nhds hδ)
    filter_upwards [hsm, hYe] with s h1 h2
    have h3 := hF (Y s) h2.1 h1
    rw [hT] at h3
    have hN : 0 ≤ ∑ a, ∑ b, ‖Y s a b‖ := by positivity
    rw [Real.norm_of_nonneg hN]
    exact h3
  have hNO : (fun s => ∑ a, ∑ b, ‖Y s a b‖) =O[𝓝 s0] (fun s => s - s0) := by
    apply IsBigO.fun_sum
    intro a _
    apply IsBigO.fun_sum
    intro b _
    have h := (hY a b).isBigO_sub
    simp only [hY0, Matrix.zero_apply, sub_zero] at h
    exact h.norm_left
  have hR0 : HasDerivAt R 0 s0 := by
    rw [hasDerivAt_iff_isLittleO]
    have h0 : R s0 = 0 := by simp [hRdef, hY0, NormedSpace.exp_zero]
    simp only [h0, sub_zero, smul_zero]
    exact hRo.trans_isBigO hNO
  have hev : (fun s => c u (cv s)) =ᶠ[𝓝 s0] fun s => R s + c u g + ∑ a, ∑ b, Y s a b * A a b := by
    filter_upwards [hYe] with s hs
    have h2 : cv s = g * NormedSpace.exp (Y s) := by
      rw [hs.2, ← Matrix.mul_assoc, slm_mul_Ji hg, Matrix.one_mul]
    simp only [hRdef]
    rw [← h2]
    ring
  have hD := (hR0.add_const (c u g)).add hTd
  exact (hD.congr_of_eventuallyEq hev).congr_deriv (by simp [hA])

theorem smooth_of_rightOK {X : GMod n} {c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)} (hR : RightOK ε X c)
    (hC : ContOK ε X c) (u : X.V) : Formalism.REAL.SmoothOnG ε (c u) := by
  intro g0 hg0
  obtain ⟨V, γ, hV, hg0V, hγ, hγU, hγid⟩ := slm_exists_ret ε hg0
  let P : (Matrix (Fin n) (Fin n) ℂ → ℂ) → Prop := fun F => ∃ v, ∀ g, Formalism.REAL.inUJ ε g → F g = c v g
  let Φ : (Matrix (Fin n) (Fin n) ℂ → ℂ) → Matrix (Fin n) (Fin n) ℂ → ℂ := fun F q => F (γ q)
  have hEv : ∀ (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (v : X.V), (∀ g, Formalism.REAL.inUJ ε g → F g = c v g) →
      ∀ a b g, Formalism.REAL.inUJ ε g → Formalism.REAL.Eab ε a b F g = c (X.E a b v) g := by
    intro F v hv a b g hg
    rw [icx_eab_eq, icx_eabV_congr hv a b hg, ← icx_eab_eq]
    exact eab_of_rightOK hR a b v hg
  have hP : ∀ F, P F → ∀ a b, P (Formalism.REAL.Eab ε a b F) := by
    rintro F ⟨v, hv⟩ a b
    exact ⟨X.E a b v, hEv F v hv a b⟩
  have hcont : ∀ F, P F → ContinuousOn (Φ F) V := by
    rintro F ⟨v, hv⟩
    exact ((hC v).comp hγ.continuousOn (fun q hq => hγU q hq)).congr fun q hq => hv _ (hγU q hq)
  have hint : ∀ F, P F → ∀ q ∈ V, ∃ δ > 0, ∀ W : Matrix (Fin n) (Fin n) ℂ, ‖W‖ < δ → ∀ B : ℝ,
      (∀ s ∈ Ioc (0:ℝ) 1, ‖(∑ a, ∑ b, ((slmJi ε (γ (q + s • W)) * fderiv ℝ γ (q + s • W) W) a b) •
          Φ (Formalism.REAL.Eab ε a b F) (q + s • W)) -
          ∑ a, ∑ b, ((slmJi ε (γ q) * fderiv ℝ γ q W) a b) • Φ (Formalism.REAL.Eab ε a b F) q‖ ≤ B) →
      ‖Φ F (q + W) - Φ F q - ∑ a, ∑ b, ((slmJi ε (γ q) * fderiv ℝ γ q W) a b) • Φ (Formalism.REAL.Eab ε a b F) q‖ ≤ B := by
    rintro F ⟨v, hv⟩ q hq
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hV q hq
    refine ⟨δ, hδ, fun W hW B hB => ?_⟩
    have hseg : ∀ s ∈ Icc (0:ℝ) 1, q + s • W ∈ V := by
      intro s hs
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hs.1]
      calc s * ‖W‖ ≤ 1 * ‖W‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
        _ < δ := by rw [one_mul]; exact hW
    set Dv : Matrix (Fin n) (Fin n) ℂ → ℂ := fun q' =>
      ∑ a, ∑ b, ((slmJi ε (γ q') * fderiv ℝ γ q' W) a b) • Φ (Formalism.REAL.Eab ε a b F) q' with hDv
    have hder : ∀ s ∈ Icc (0:ℝ) 1, HasDerivAt (fun t : ℝ => Φ F (q + t • W)) (Dv (q + s • W)) s := by
      intro s hs
      have hq' := hseg s hs
      have hdγ : HasFDerivAt γ (fderiv ℝ γ (q + s • W)) (q + s • W) :=
        ((hγ.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hq')).hasFDerivAt
      have hline := ((hasDerivAt_id' s).smul_const W).const_add q
      simp only [one_smul] at hline
      have hc1 : HasDerivAt (fun t => γ (q + t • W)) (fderiv ℝ γ (q + s • W) W) s :=
        hdγ.comp_hasDerivAt s hline
      have hcU : ∀ᶠ t in 𝓝 s, Formalism.REAL.inUJ ε (γ (q + t • W)) := by
        filter_upwards [hline.continuousAt.preimage_mem_nhds (hV.mem_nhds hq')] with t ht
        exact hγU _ ht
      have h := chain hR hC v hc1 hcU
      have hev : (fun t : ℝ => Φ F (q + t • W)) =ᶠ[𝓝 s] fun t => c v (γ (q + t • W)) := by
        filter_upwards [hcU] with t ht using hv _ ht
      refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
      refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
      rw [smul_eq_mul]
      exact congrArg _ (hEv F v hv a b _ (hγU _ hq')).symm
    have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 1 ⟨zero_lt_one, le_rfl⟩)
    have h1 : ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt (fun t : ℝ => Φ F (q + t • W) - t • Dv q)
        (Dv (q + t • W) - Dv q) (Icc (0:ℝ) 1) t := by
      intro t ht
      exact (((hder t ht).sub ((hasDerivAt_id' t).smul_const (Dv q))).congr_deriv (by simp)).hasDerivWithinAt
    have h2 : ∀ t ∈ Icc (0:ℝ) 1, ‖Dv (q + t • W) - Dv q‖ ≤ B := by
      intro t ht
      rcases ht.1.eq_or_lt with h0 | h0
      · simp [← h0, hB0]
      · exact hB t ⟨h0, ht.2⟩
    have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le h1 h2 (convex_Icc 0 1)
      (⟨le_rfl, zero_le_one⟩ : (0:ℝ) ∈ Icc (0:ℝ) 1) (⟨zero_le_one, le_rfl⟩ : (1:ℝ) ∈ Icc (0:ℝ) 1)
    simp only [one_smul, zero_smul, add_zero, sub_zero, norm_one, mul_one] at hmv
    rw [sub_right_comm] at hmv
    exact hmv
  refine ⟨V, Φ (c u), hV, hg0V, slm_mat hV hγ (slm_mc hγ) Φ P (Formalism.REAL.Eab ε) hP hcont hint (c u) ⟨u, fun _ _ => rfl⟩,
    fun g hgV hgU => ?_⟩
  show c u g = c u (γ g)
  rw [hγid g hgV hgU]

end Smooth

theorem word_of_rightOK {X : GMod n} {c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)} (hR : RightOK ε X c) :
    ∀ (w : List (Fin n × Fin n)) (u : X.V), ∃ v : X.V, ∀ g, Formalism.REAL.inUJ ε g → Formalism.REAL.Eword ε w (c u) g = c v g
  | [], u => ⟨u, fun _ _ => rfl⟩
  | p :: w, u => by
      obtain ⟨v, hv⟩ := word_of_rightOK hR w u
      refine ⟨X.E p.1 p.2 v, fun g hg => ?_⟩
      simp only [Formalism.REAL.Eword]
      rw [icx_eab_eq, icx_eabV_congr hv p.1 p.2 hg, ← icx_eab_eq]
      exact eab_of_rightOK hR p.1 p.2 v hg

theorem memLp_of_level {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hc : ContinuousOn F {g | Formalism.REAL.inUJ ε g})
    (hL : LevelF ε F 0) : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := by
  have hcont : Continuous (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) :=
    hc.comp_continuous (Units.continuous_val.comp continuous_subtype_val) (fun g => g.2)
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  unfold LevelF at hL
  simp only [Real.rpow_zero, ENNReal.ofReal_one, mul_one] at hL
  have h' : (∫⁻ a : Formalism.REAL.UJ ε, ‖F (Formalism.MainNotions.S.umat a)‖ₑ ^ 2 ∂(Formalism.REAL.muG ε)) < ⊤ := hL
  simpa using h'

theorem smooth_l2_of_right_continuous_level {X : GMod n} {c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)} (hR : RightOK ε X c)
    (hC : ContOK ε X c) (hL : ∀ u, LevelF ε (c u) 0) (u : X.V) : IsSmoothL2 ε (c u) := by
  refine ⟨smooth_of_rightOK hR hC u, fun w => ?_⟩
  obtain ⟨v, hv⟩ := word_of_rightOK hR w u
  have e : (fun g : Formalism.REAL.UJ ε => Formalism.REAL.Eword ε w (c u) (Formalism.MainNotions.S.umat g)) =
      fun g => c v (Formalism.MainNotions.S.umat g) := funext fun g => hv _ g.2
  rw [e]
  exact memLp_of_level (hC v) (hL v)

theorem toL2_congr_on_unitary_bis {F G : Matrix (Fin n) (Fin n) ℂ → ℂ} (h : ∀ g, Formalism.REAL.inUJ ε g → F g = G g) :
    toL2 ε F = toL2 ε G := by
  have e : (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) = fun g => G (Formalism.MainNotions.S.umat g) :=
    funext fun g => h _ g.2
  by_cases hm : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)
  · rw [toL2_eq_toLp_of_memLp hm, toL2_eq_toLp_of_memLp (e ▸ hm)]
    exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun g => congrFun e g)
  · unfold toL2
    rw [dif_neg hm, dif_neg (e ▸ hm)]

theorem emb_of {X : GMod n} {c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)} (hR : RightOK ε X c)
    (hC : ContOK ε X c) (hL : ∀ u, LevelF ε (c u) 0) (u : X.V) (h1 : c u 1 ≠ 0) :
    ∃ c' : X.V →ₗ[ℂ] smD ε (rreg ε),
      (∀ a b x, c' (X.E a b x) = smE ε (rreg ε) a b (c' x)) ∧ c' u ≠ 0 := by
  have hS := smooth_l2_of_right_continuous_level hR hC hL
  have hM : ∀ v, MemLp (fun g : Formalism.REAL.UJ ε => c v (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) :=
    fun v => memLp_of_level (hC v) (hL v)
  let c' : X.V →ₗ[ℂ] smD ε (rreg ε) :=
    { toFun := fun v => ⟨toL2 ε (c v), toL2_mem_smD_of_isSmoothL2 (hS v)⟩
      map_add' := fun v w => by
        apply Subtype.ext
        show toL2 ε (c (v + w)) = toL2 ε (c v) + toL2 ε (c w)
        rw [toL2_eq_toLp_of_memLp (hM (v + w)), toL2_eq_toLp_of_memLp (hM v), toL2_eq_toLp_of_memLp (hM w), ← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun g => by simp)
      map_smul' := fun r v => by
        apply Subtype.ext
        show toL2 ε (c (r • v)) = r • toL2 ε (c v)
        rw [toL2_eq_toLp_of_memLp (hM (r • v)), toL2_eq_toLp_of_memLp (hM v), ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun g => by simp) }
  refine ⟨c', fun a b x => ?_, fun h0 => h1 ?_⟩
  · apply Subtype.ext
    show toL2 ε (c (X.E a b x)) = ((smE ε (rreg ε) a b ⟨toL2 ε (c x), toL2_mem_smD_of_isSmoothL2 (hS x)⟩ : smD ε (rreg ε)) : L2 ε)
    rw [rightDerivative_toL2 (hS x) a b]
    exact toL2_congr_on_unitary_bis fun g hg => (eab_of_rightOK hR a b x hg).symm
  · have h2 : toL2 ε (c u) = 0 := congrArg Subtype.val h0
    rw [toL2_eq_toLp_of_memLp (hM u)] at h2
    have h3 : (fun g : Formalism.REAL.UJ ε => c u (Formalism.MainNotions.S.umat g)) =ᵐ[Formalism.REAL.muG ε] 0 := by
      have := MemLp.coeFn_toLp (hM u)
      rw [h2] at this
      exact this.symm.trans (Lp.coeFn_zero _ _ _)
    have hcont : Continuous (fun g : Formalism.REAL.UJ ε => c u (Formalism.MainNotions.S.umat g)) :=
      (hC u).comp_continuous (Units.continuous_val.comp continuous_subtype_val) (fun g => g.2)
    have h4 := (Continuous.ae_eq_iff_eq (Formalism.REAL.muG ε) hcont continuous_zero).mp h3
    exact congrFun h4 1

theorem pack : CompanionTheory.RgExh.Dec.L.Pack := by
  intro n ε H _ _ _ σ D E hK χ ss hσ hL u hu
  have hb : ∀ x : (⟨D, E, hK.gl⟩ : GMod n).V, x ≠ 0 → ∃ c ∈ Set.range (fun ξ : D => baseCoef σ D (ξ : H)), c x 1 ≠ 0 := by
    intro x hx
    refine ⟨_, ⟨x, rfl⟩, ?_⟩
    show ⟪(x : H), σ 1 (x : H)⟫_ℂ ≠ 0
    rw [hσ.1.1]
    simpa using fun h => hx (Subtype.ext h)
  obtain ⟨_, ⟨ξ, rfl⟩, js, h1⟩ := path_sep ss ⟨D, E, hK.gl⟩ χ _ hb u hu
  exact emb_of (c := famP σ D E hK.gl χ ss (ξ, js))
    (path_ok ss ⟨D, E, hK.gl⟩ _ χ js (base_ok hK hσ _))
    (path_cont ss ⟨D, E, hK.gl⟩ _ χ js (base_cont hK.gl hσ _)) (fun v => hL (ξ, js) v) u h1

end GlobalTheory.CompanionTheory.PackEmb
