import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandOperatorAdjointStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveCptBoundedTime

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.WaveSymm

theorem one_dim (Φ A B : ℝ → ℝ → ℂ)
    (h1 : ∀ T r, HasDerivAt (fun r => Φ r (T - r)) (A r (T - r) - B r (T - r)) r)
    (h2 : ∀ t s r, A (t + r) (s + r) - B (t + r) (s + r) = A t s - B t s)
    (h3 : ∀ t s r, A (t + r) (s - r) + B (t + r) (s - r) = A t s + B t s)
    (hA : ∀ s, A 0 s = 0) (hB : ∀ t, B t 0 = 0) (T : ℝ) : Φ T 0 = Φ 0 T := by
  have hq : ∀ t s, (A t s - B t s) + (A s t - B s t) = 0 := by
    intro t s
    have e1 := h2 (t - s) 0 s
    have e2 := h2 0 (t - s) s
    have e3 := h3 0 (t - s) (t - s)
    simp only [sub_add_cancel, zero_add, sub_self] at e1 e2 e3
    rw [e1, e2]
    rw [hB, hA] at e3 ⊢
    linear_combination e3
  have hd : ∀ r, HasDerivAt (fun r => Φ r (T - r) - Φ (T - r) (T - (T - r))) 0 r := by
    intro r
    have a1 := h1 T r
    have a2 := HasDerivAt.comp_const_sub (f := fun r => Φ r (T - r)) T r (h1 T (T - r))
    have a3 : HasDerivAt (fun r => Φ r (T - r) - Φ (T - r) (T - (T - r)))
        (A r (T - r) - B r (T - r) - -(A (T - r) (T - (T - r)) - B (T - r) (T - (T - r)))) r := a1.sub a2
    have e : A r (T - r) - B r (T - r) - -(A (T - r) (T - (T - r)) - B (T - r) (T - (T - r))) = 0 := by
      rw [sub_sub_cancel]
      linear_combination hq r (T - r)
    rwa [e] at a3
  have hc := is_const_of_deriv_eq_zero (f := fun r => Φ r (T - r) - Φ (T - r) (T - (T - r)))
    (fun r => (hd r).differentiableAt) (fun r => (hd r).deriv) 0 T
  simp only [sub_zero, sub_self] at hc
  linear_combination (-1 / 2 : ℂ) * hc

variable {n : ℕ}

theorem val_mem_GLs (y : G n) : y.val ∈ GLs n := by
  have h : IsUnit (y.val.det) := (Matrix.isUnit_iff_isUnit_det _).mp y.isUnit
  exact h.ne_zero

theorem continuous_val : Continuous (fun y : G n => y.val) := Units.continuous_val

section Int

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

theorem integrable_of_vanish (hL : LgFacts) (f : G n → ℂ) (hf : Continuous f) (R : ℝ)
    (h : ∀ y : G n, R < lg y.val → f y = 0) : Integrable f μ := by
  have hK : IsCompact {y : G n | lg y.val ≤ R} := ((hL n).2.2.2.2.1 R)
  refine hf.integrable_of_hasCompactSupport (HasCompactSupport.intro hK fun y hy => h y ?_)
  simpa using hy

theorem hasDerivAt_integral (hL : LgFacts) (c c' : ℝ → Mat n → ℂ)
    (hc : ContinuousOn (Function.uncurry c) (Set.univ ×ˢ GLs n))
    (hc' : ContinuousOn (Function.uncurry c') (Set.univ ×ˢ GLs n))
    (hd : ∀ r, ∀ y ∈ GLs n, HasDerivAt (fun r => c r y) (c' r y) r)
    (hs : ∀ B : ℝ, ∃ R : ℝ, ∀ r, |r| ≤ B → ∀ y ∈ GLs n, R < lg y → c r y = 0 ∧ c' r y = 0) (r : ℝ) :
    HasDerivAt (fun r => ∫ y : G n, c r y.val ∂μ) (∫ y : G n, c' r y.val ∂μ) r := by
  obtain ⟨R, hR⟩ := hs (|r| + 1)
  have hK : IsCompact {y : G n | lg y.val ≤ R} := ((hL n).2.2.2.2.1 R)
  have cont2 : ∀ {f : ℝ → Mat n → ℂ}, ContinuousOn (Function.uncurry f) (Set.univ ×ˢ GLs n) →
      Continuous (fun p : ℝ × G n => f p.1 p.2.val) := by
    intro f hf
    exact hf.comp_continuous (continuous_fst.prodMk (continuous_val.comp continuous_snd))
      fun p => ⟨Set.mem_univ _, val_mem_GLs p.2⟩
  have contc := cont2 hc
  have contc' := cont2 hc'
  have cont1 : ∀ {f : ℝ → Mat n → ℂ}, Continuous (fun p : ℝ × G n => f p.1 p.2.val) → ∀ x,
      Continuous (fun y : G n => f x y.val) := by
    intro f hf x
    exact hf.comp (continuous_const.prodMk continuous_id)
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := r - 1) (b := r + 1)).prod hK).exists_bound_of_continuousOn
    contc'.continuousOn
  have hball : ∀ x ∈ Metric.ball r 1, |x| ≤ |r| + 1 ∧ x ∈ Set.Icc (r - 1) (r + 1) := by
    intro x hx
    have hx' : |x - r| < 1 := by simpa [Real.dist_eq] using hx
    have := abs_lt.mp hx'
    refine ⟨?_, by constructor <;> linarith [this.1, this.2]⟩
    calc |x| = |(x - r) + r| := by ring_nf
      _ ≤ |x - r| + |r| := abs_add_le _ _
      _ ≤ |r| + 1 := by linarith
  have hfar : ∀ y : G n, R < lg y.val → ∀ x, |x| ≤ |r| + 1 → c x y.val = 0 ∧ c' x y.val = 0 :=
    fun y hy x hx => hR x hx _ (val_mem_GLs y) hy
  have hr0 : |r| ≤ |r| + 1 := by linarith
  have hbound : Integrable ({y : G n | lg y.val ≤ R}.indicator fun _ => C) μ := by
    refine IntegrableOn.integrable_indicator ?_ hK.measurableSet
    exact integrableOn_const hK.measure_lt_top.ne
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := fun r (y : G n) => c r y.val)
    (F' := fun r (y : G n) => c' r y.val) (s := Metric.ball r 1) (bound := {y : G n | lg y.val ≤ R}.indicator fun _ => C)
    (Metric.ball_mem_nhds r one_pos)
    (Filter.Eventually.of_forall fun x => (cont1 contc x).aestronglyMeasurable)
    (integrable_of_vanish μ hL _ (cont1 contc r) R fun y hy => (hfar y hy r hr0).1)
    (cont1 contc' r).aestronglyMeasurable ?_ hbound ?_).2
  · refine Filter.Eventually.of_forall fun y x hx => ?_
    by_cases hy : lg y.val ≤ R
    · rw [Set.indicator_of_mem (by exact hy)]
      exact hC (x, y) ⟨(hball x hx).2, hy⟩
    · rw [Set.indicator_of_notMem (by exact hy), (hfar y (not_le.mp hy) x (hball x hx).1).2]
      simp
  · exact Filter.Eventually.of_forall fun y x _ => hd x _ (val_mem_GLs y)

end Int

theorem smooth_deriv_gen {X V : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : ℝ → X → V) {S : Set X} (hS : IsOpen S) (h : ContDiffOn ℝ ∞ (Function.uncurry a) (Set.univ ×ˢ S)) :
    ContDiffOn ℝ ∞ (Function.uncurry fun t y => deriv (fun s => a s y) t) (Set.univ ×ˢ S) ∧
      ∀ t, ∀ y ∈ S, HasDerivAt (fun s => a s y) (deriv (fun s => a s y) t) t := by
  have hO : IsOpen ((Set.univ : Set ℝ) ×ˢ S) := isOpen_univ.prod hS
  have hf : ∀ t, ∀ y ∈ S, HasDerivAt (fun s => a s y) (fderiv ℝ (Function.uncurry a) (t, y) ((1 : ℝ), (0 : X))) t := by
    intro t y hy
    have hd : HasFDerivAt (Function.uncurry a) (fderiv ℝ (Function.uncurry a) (t, y)) (t, y) :=
      ((h.contDiffAt (hO.mem_nhds ⟨Set.mem_univ _, hy⟩)).differentiableAt (by simp)).hasFDerivAt
    have hl : HasDerivAt (fun s : ℝ => (s, y)) ((1 : ℝ), (0 : X)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
    exact hd.comp_hasDerivAt t hl
  constructor
  · have h1 : ContDiffOn ℝ ∞ (fderiv ℝ (Function.uncurry a)) (Set.univ ×ˢ S) :=
      ContDiffOn.fderiv_of_isOpen h hO (by simp)
    have h2 : ContDiffOn ℝ ∞ (fun p => fderiv ℝ (Function.uncurry a) p ((1 : ℝ), (0 : X))) (Set.univ ×ˢ S) :=
      h1.clm_apply contDiffOn_const
    refine h2.congr ?_
    rintro ⟨t, y⟩ ⟨-, hy⟩
    exact (hf t y hy).deriv
  · intro t y hy
    rw [(hf t y hy).deriv]
    exact hf t y hy

section Time

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem isOpen_GLs (n : ℕ) : IsOpen (GLs n) := by
  have hc : Continuous (fun y : Mat n => y.det) := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage hc

def dt (a : ℝ → Mat n → V) : ℝ → Mat n → V := fun t y => deriv (fun s => a s y) t

def Sm (a : ℝ → Mat n → V) : Prop := ContDiffOn ℝ ∞ (Function.uncurry a) (Set.univ ×ˢ GLs n)

def Sp (a : ℝ → Mat n → V) : Prop := ∀ B : ℝ, ∃ R : ℝ, ∀ t, |t| ≤ B → ∀ y ∈ GLs n, R < lg y → a t y = 0

theorem hasDerivAt_dt {a : ℝ → Mat n → V} (h : Sm a) (t : ℝ) {y : Mat n} (hy : y ∈ GLs n) :
    HasDerivAt (fun s => a s y) (dt a t y) t :=
  (smooth_deriv_gen a (isOpen_GLs n) h).2 t y hy

theorem sm_dt {a : ℝ → Mat n → V} (h : Sm a) : Sm (dt a) :=
  (smooth_deriv_gen a (isOpen_GLs n) h).1

theorem sm_at {a : ℝ → Mat n → V} (h : Sm a) (t : ℝ) : ContDiffOn ℝ ∞ (a t) (GLs n) := by
  have h1 : ContDiff ℝ ∞ (fun y : Mat n => (t, y)) := contDiff_const.prodMk contDiff_id
  have h2 := ContDiffOn.comp (g := Function.uncurry a) (f := fun y : Mat n => (t, y)) (s := GLs n)
    (t := Set.univ ×ˢ GLs n) h h1.contDiffOn fun y hy => ⟨Set.mem_univ _, hy⟩
  exact h2

theorem sp_dt {a : ℝ → Mat n → V} (h : Sp a) : Sp (dt a) := by
  intro B
  obtain ⟨R, hR⟩ := h (|B| + 1)
  refine ⟨R, fun t ht y hy hl => ?_⟩
  have hlt : |t| < |B| + 1 := by linarith [le_abs_self B]
  have h1 : ∀ᶠ s in nhds t, |s| < |B| + 1 :=
    (continuous_abs.tendsto t).eventually (gt_mem_nhds hlt)
  have h2 : (fun s => a s y) =ᶠ[nhds t] fun _ => 0 := by
    filter_upwards [h1] with s hs using hR s hs.le y hy hl
  change deriv (fun s => a s y) t = 0
  rw [h2.deriv_eq]
  simp

theorem contOn_shift {a : ℝ → Mat n → V} (h : Sm a) (t α : ℝ) :
    ContinuousOn (fun p : ℝ × Mat n => a (t + α * p.1) p.2) (Set.univ ×ˢ GLs n) := by
  have h1 : Continuous (fun p : ℝ × Mat n => (t + α * p.1, p.2)) := by fun_prop
  exact ContinuousOn.comp (ContDiffOn.continuousOn h) h1.continuousOn fun p hp => ⟨Set.mem_univ _, hp.2⟩

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

theorem integrable_inner (hL : LgFacts) {f h : Mat n → V} (hf : ContinuousOn f (GLs n)) (hh : ContinuousOn h (GLs n))
    (R : ℝ) (hv : ∀ y ∈ GLs n, R < lg y → ⟪f y, h y⟫_ℂ = 0) :
    Integrable (fun y : G n => ⟪f y.val, h y.val⟫_ℂ) μ := by
  refine integrable_of_vanish μ hL _ ?_ R fun y hy => hv _ (val_mem_GLs y) hy
  exact (hf.comp_continuous continuous_val val_mem_GLs).inner (hh.comp_continuous continuous_val val_mem_GLs)

def Pr (a b : ℝ → Mat n → V) (t s : ℝ) : ℂ := ∫ y : G n, ⟪a t y.val, b s y.val⟫_ℂ ∂μ

theorem Pr_hasDeriv (hL : LgFacts) {a b : ℝ → Mat n → V} (ha : Sm a) (hb : Sm b) (hsa : Sp a) (hsb : Sp b)
    (t s α β r : ℝ) :
    HasDerivAt (fun r => Pr μ a b (t + α * r) (s + β * r))
      ((α : ℂ) * Pr μ (dt a) b (t + α * r) (s + β * r) + (β : ℂ) * Pr μ a (dt b) (t + α * r) (s + β * r)) r := by
  have c1 : ContinuousOn (fun p : ℝ × Mat n => ⟪a (t + α * p.1) p.2, b (s + β * p.1) p.2⟫_ℂ) (Set.univ ×ˢ GLs n) :=
    (contOn_shift ha t α).inner (contOn_shift hb s β)
  have c2 : ContinuousOn (fun p : ℝ × Mat n => (α : ℂ) * ⟪dt a (t + α * p.1) p.2, b (s + β * p.1) p.2⟫_ℂ +
      (β : ℂ) * ⟪a (t + α * p.1) p.2, dt b (s + β * p.1) p.2⟫_ℂ) (Set.univ ×ˢ GLs n) :=
    (continuousOn_const.mul ((contOn_shift (sm_dt ha) t α).inner (contOn_shift hb s β))).add
      (continuousOn_const.mul ((contOn_shift ha t α).inner (contOn_shift (sm_dt hb) s β)))
  have key := hasDerivAt_integral μ hL (fun r y => ⟪a (t + α * r) y, b (s + β * r) y⟫_ℂ)
    (fun r y => (α : ℂ) * ⟪dt a (t + α * r) y, b (s + β * r) y⟫_ℂ + (β : ℂ) * ⟪a (t + α * r) y, dt b (s + β * r) y⟫_ℂ)
    c1 c2 ?_ ?_ r
  · have e : ∫ y : G n, ((α : ℂ) * ⟪dt a (t + α * r) y.val, b (s + β * r) y.val⟫_ℂ +
        (β : ℂ) * ⟪a (t + α * r) y.val, dt b (s + β * r) y.val⟫_ℂ) ∂μ =
        (α : ℂ) * Pr μ (dt a) b (t + α * r) (s + β * r) + (β : ℂ) * Pr μ a (dt b) (t + α * r) (s + β * r) := by
      obtain ⟨Ra, hRa⟩ := hsa |t + α * r|
      obtain ⟨Rb, hRb⟩ := hsb |s + β * r|
      have i1 := integrable_inner μ hL (sm_at (sm_dt ha) (t + α * r)).continuousOn (sm_at hb (s + β * r)).continuousOn Rb
        (fun y hy hl => by rw [hRb _ le_rfl y hy hl, inner_zero_right])
      have i2 := integrable_inner μ hL (sm_at ha (t + α * r)).continuousOn (sm_at (sm_dt hb) (s + β * r)).continuousOn Ra
        (fun y hy hl => by rw [hRa _ le_rfl y hy hl, inner_zero_left])
      rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul]
      rfl
    rw [← e]
    exact key
  · intro r y hy
    have l1 : HasDerivAt (fun r : ℝ => t + α * r) α r := by
      simpa using ((hasDerivAt_id r).const_mul α).const_add t
    have l2 : HasDerivAt (fun r : ℝ => s + β * r) β r := by
      simpa using ((hasDerivAt_id r).const_mul β).const_add s
    have da0 : HasDerivAt (fun τ => a τ y) (dt a (t + α * r) y) ((fun r : ℝ => t + α * r) r) :=
      hasDerivAt_dt ha (t + α * r) hy
    have db0 : HasDerivAt (fun τ => b τ y) (dt b (s + β * r) y) ((fun r : ℝ => s + β * r) r) :=
      hasDerivAt_dt hb (s + β * r) hy
    have da : HasDerivAt (fun r => a (t + α * r) y) (α • dt a (t + α * r) y) r :=
      HasDerivAt.scomp (g₁ := fun τ => a τ y) (h := fun r : ℝ => t + α * r) r da0 l1
    have db : HasDerivAt (fun r => b (s + β * r) y) (β • dt b (s + β * r) y) r :=
      HasDerivAt.scomp (g₁ := fun τ => b τ y) (h := fun r : ℝ => s + β * r) r db0 l2
    refine (da.inner ℂ db).congr_deriv ?_
    rw [← Complex.coe_smul, ← Complex.coe_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    ring
  · intro B
    obtain ⟨Ra, hRa⟩ := hsa (|t| + |α| * |B|)
    obtain ⟨Rb, hRb⟩ := hsb (|s| + |β| * |B|)
    refine ⟨max Ra Rb, fun r hr y hy hl => ?_⟩
    have hrB : |r| ≤ |B| := hr.trans (le_abs_self B)
    have b1 : |t + α * r| ≤ |t| + |α| * |B| := by
      calc |t + α * r| ≤ |t| + |α * r| := abs_add_le _ _
        _ = |t| + |α| * |r| := by rw [abs_mul]
        _ ≤ _ := by gcongr
    have b2 : |s + β * r| ≤ |s| + |β| * |B| := by
      calc |s + β * r| ≤ |s| + |β * r| := abs_add_le _ _
        _ = |s| + |β| * |r| := by rw [abs_mul]
        _ ≤ _ := by gcongr
    have z1 := hRa _ b1 y hy (lt_of_le_of_lt (le_max_left _ _) hl)
    have z2 := hRb _ b2 y hy (lt_of_le_of_lt (le_max_right _ _) hl)
    simp [z1, z2]

end Time

section Gel

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rd_zero (X : Mat n) : Rd X (0 : Mat n → V) = 0 := by
  funext g
  have : fderiv ℝ (0 : Mat n → V) g = 0 := by
    change fderiv ℝ (fun _ : Mat n => (0 : V)) g = 0
    simp
  simp [Rd, this]

theorem Eu_zero (s : Bool) (a b : Fin n) : Eu s a b (0 : Mat n → V) = 0 := by
  simp [Eu, Rd_zero]

theorem Epow_one (s : Bool) (c b : Fin n) (f : Mat n → V) : Epow s 1 c b f = Eu s c b f := by
  simp only [Epow]
  rw [Finset.sum_eq_single b]
  · simp
  · intro d _ hd
    simp [hd, Eu_zero]
  · simp

theorem EpowT_one (s : Bool) (c b : Fin n) (f : Mat n → V) : EpowT s 1 c b f = Eu s b c f := by
  simp only [EpowT]
  rw [Finset.sum_eq_single b]
  · simp
  · intro d _ hd
    simp [hd, Eu_zero]
  · simp

theorem gel_two (s : Bool) (f : Mat n → V) : gel s 2 f = ∑ a, ∑ c, Eu s a c (Eu s c a f) := by
  unfold gel
  refine Finset.sum_congr rfl fun a _ => ?_
  change (∑ c, Eu s a c (Epow s 1 c a f)) = _
  simp only [Epow_one]

theorem gelT_eq_gel (s : Bool) (f : Mat n → V) : gelT s 2 f = gel s 2 f := by
  have h : gelT s 2 f = ∑ a, ∑ c, Eu s c a (Eu s a c f) := by
    unfold gelT
    refine Finset.sum_congr rfl fun a _ => ?_
    change (∑ c, Eu s c a (EpowT s 1 c a f)) = _
    simp only [EpowT_one]
  rw [h, gel_two, Finset.sum_comm]

end Gel

section Om

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem Eu_smooth (hR : RCalc) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (a b : Fin n) :
    ContDiffOn ℝ ∞ (Eu s a b f) (GLs n) := by
  have h := ((hR n).1 V f hf).1
  exact ((h _).add ((h _).const_smul _)).const_smul _

theorem gel_smooth (hR : RCalc) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) :
    ContDiffOn ℝ ∞ (gel s 2 f) (GLs n) := by
  have e : gel s 2 f = fun x => ∑ a, ∑ c, Eu s a c (Eu s c a f) x := by
    funext x
    rw [gel_two]
    simp [Finset.sum_apply]
  rw [e]
  exact ContDiffOn.sum fun a _ => ContDiffOn.sum fun c _ => Eu_smooth hR (Eu_smooth hR hf s c a) s a c

variable [CompleteSpace V] [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

theorem Om_symm (hL : LgFacts) (hR : RCalc) {f h : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hh : ContDiffOn ℝ ∞ h (GLs n)) (cf : Cpt f) (ch : Cpt h) :
    ∫ y : G n, ⟪Om f y.val, h y.val⟫_ℂ ∂μ = ∫ y : G n, ⟪f y.val, Om h y.val⟫_ℂ ∂μ := by
  have I : ∀ s : Bool, ∫ y : G n, ⟪gel s 2 f y.val, h y.val⟫_ℂ ∂μ = ∫ y : G n, ⟪f y.val, gel (!s) 2 h y.val⟫_ℂ ∂μ := by
    intro s
    have := GlobalTheory.T.gelfand_operator_adjoint hL hR n μ V s 2 f h hf hh cf ch
    rw [gelT_eq_gel] at this
    simpa using this
  obtain ⟨Rf, hRf⟩ := cf
  obtain ⟨Rh, hRh⟩ := ch
  have i1 : ∀ s, Integrable (fun y : G n => ⟪gel s 2 f y.val, h y.val⟫_ℂ) μ := fun s =>
    integrable_inner μ hL (gel_smooth hR hf s).continuousOn hh.continuousOn Rh
      (fun y hy hl => by rw [hRh y hy hl, inner_zero_right])
  have i2 : ∀ s, Integrable (fun y : G n => ⟪f y.val, gel s 2 h y.val⟫_ℂ) μ := fun s =>
    integrable_inner μ hL hf.continuousOn (gel_smooth hR hh s).continuousOn Rf
      (fun y hy hl => by rw [hRf y hy hl, inner_zero_left])
  have e1 : ∫ y : G n, ⟪Om f y.val, h y.val⟫_ℂ ∂μ =
      2 * (∫ y : G n, ⟪gel true 2 f y.val, h y.val⟫_ℂ ∂μ + ∫ y : G n, ⟪gel false 2 f y.val, h y.val⟫_ℂ ∂μ) := by
    rw [← integral_add (i1 true) (i1 false), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp [Om, inner_add_left, inner_smul_left]
    ring
  have e2 : ∫ y : G n, ⟪f y.val, Om h y.val⟫_ℂ ∂μ =
      2 * (∫ y : G n, ⟪f y.val, gel true 2 h y.val⟫_ℂ ∂μ + ∫ y : G n, ⟪f y.val, gel false 2 h y.val⟫_ℂ ∂μ) := by
    rw [← integral_add (i2 true) (i2 false), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp [Om, inner_add_right, inner_smul_right]
    ring
  rw [e1, e2, I true, I false]
  simp only [Bool.not_true, Bool.not_false]
  ring

end Om

section Wave

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

theorem dt_dt {E : KMod n} {u : ℝ → Mat n → E.V} (hu : IsWave E u) (t : ℝ) {y : Mat n} (hy : y ∈ GLs n) :
    dt (dt u) t y = Om (u t) y := by
  rw [← hu.2.2.1 t y hy, iteratedDeriv_succ, iteratedDeriv_one]
  rfl

theorem dt_zero {E : KMod n} {u : ℝ → Mat n → E.V} (hu : IsWave E u) {y : Mat n} (hy : y ∈ GLs n) :
    dt u 0 y = 0 := hu.2.2.2 y hy

theorem wave_pairing_second_time_derivative (hL : LgFacts) (hR : RCalc) {E : KMod n} {u v : ℝ → Mat n → E.V} (hu : IsWave E u) (hv : IsWave E v)
    (su : Sp u) (sv : Sp v) (t s : ℝ) : Pr μ (dt (dt u)) v t s = Pr μ u (dt (dt v)) t s := by
  haveI := FiniteDimensional.complete ℂ E.V
  obtain ⟨Ru, hRu⟩ := su |t|
  obtain ⟨Rv, hRv⟩ := sv |s|
  have h := Om_symm μ hL hR (sm_at (a := u) hu.1 t) (sm_at (a := v) hv.1 s) ⟨Ru, hRu t le_rfl⟩ ⟨Rv, hRv s le_rfl⟩
  unfold Pr
  calc ∫ y : G n, ⟪dt (dt u) t y.val, v s y.val⟫_ℂ ∂μ = ∫ y : G n, ⟪Om (u t) y.val, v s y.val⟫_ℂ ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun y => by
          simp only [dt_dt hu t (val_mem_GLs y)])
    _ = ∫ y : G n, ⟪u t y.val, Om (v s) y.val⟫_ℂ ∂μ := h
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun y => by
          simp only [dt_dt hv s (val_mem_GLs y)])

theorem line_const (hL : LgFacts) (hR : RCalc) {E : KMod n} {u v : ℝ → Mat n → E.V} (hu : IsWave E u) (hv : IsWave E v)
    (su : Sp u) (sv : Sp v) (β : ℝ) (hβ : β * β = 1) (t s r : ℝ) :
    Pr μ (dt u) v (t + 1 * r) (s + β * r) - (β : ℂ) * Pr μ u (dt v) (t + 1 * r) (s + β * r) =
      Pr μ (dt u) v t s - (β : ℂ) * Pr μ u (dt v) t s := by
  have hd : ∀ r, HasDerivAt (fun r => Pr μ (dt u) v (t + 1 * r) (s + β * r) - (β : ℂ) * Pr μ u (dt v) (t + 1 * r) (s + β * r)) 0 r := by
    intro r
    have d1 := Pr_hasDeriv μ hL (sm_dt (a := u) hu.1) hv.1 (sp_dt su) sv t s 1 β r
    have d2 := Pr_hasDeriv μ hL hu.1 (sm_dt (a := v) hv.1) su (sp_dt sv) t s 1 β r
    have d3 := d1.sub (d2.const_mul (β : ℂ))
    have hβ' : (β : ℂ) * β = 1 := by exact_mod_cast hβ
    have e := wave_pairing_second_time_derivative μ hL hR hu hv su sv (t + 1 * r) (s + β * r)
    have z : ((1 : ℝ) : ℂ) * Pr μ (dt (dt u)) v (t + 1 * r) (s + β * r) + (β : ℂ) * Pr μ (dt u) (dt v) (t + 1 * r) (s + β * r) -
        (β : ℂ) * (((1 : ℝ) : ℂ) * Pr μ (dt u) (dt v) (t + 1 * r) (s + β * r) + (β : ℂ) * Pr μ u (dt (dt v)) (t + 1 * r) (s + β * r)) = 0 := by
      rw [e]
      push_cast
      linear_combination (-Pr μ u (dt (dt v)) (t + 1 * r) (s + β * r)) * hβ'
    rw [z] at d3
    exact d3
  have hc := is_const_of_deriv_eq_zero
    (f := fun r => Pr μ (dt u) v (t + 1 * r) (s + β * r) - (β : ℂ) * Pr μ u (dt v) (t + 1 * r) (s + β * r))
    (fun r => (hd r).differentiableAt) (fun r => (hd r).deriv) r 0
  simpa using hc

end Wave

theorem _root_.GlobalTheory.CompanionTheory.WaveMult.wave_symm : LgFacts → RCalc → WaveSpeed → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (u v : ℝ → Mat n → E.V), IsWave E u → IsWave E v → Cpt (u 0) → Cpt (v 0) → ∀ t, ∫ y : G n, ⟪u t y.val, v 0 y.val⟫_ℂ ∂μ = ∫ y : G n, ⟪u 0 y.val, v t y.val⟫_ℂ ∂μ := by
  intro hL hR hS n _ _ μ _ E u v hu hv cu cv t
  have su : Sp u := wave_cpt_bounded_time hL hS n E u hu cu
  have sv : Sp v := wave_cpt_bounded_time hL hS n E v hv cv
  refine one_dim (Pr μ u v) (Pr μ (dt u) v) (Pr μ u (dt v)) ?_ ?_ ?_ ?_ ?_ t
  · intro T r
    have h := Pr_hasDeriv μ hL hu.1 hv.1 su sv 0 T 1 (-1) r
    have e1 : ∀ r : ℝ, (0 : ℝ) + 1 * r = r := fun r => by ring
    have e2 : ∀ r : ℝ, T + -1 * r = T - r := fun r => by ring
    simp only [e1, e2] at h
    refine h.congr_deriv ?_
    push_cast
    ring
  · intro t s r
    have h := line_const μ hL hR hu hv su sv 1 (by norm_num) t s r
    simpa using h
  · intro t s r
    have h := line_const μ hL hR hu hv su sv (-1) (by norm_num) t s r
    simpa [sub_eq_add_neg] using h
  · intro s
    unfold Pr
    have : ∀ y : G n, ⟪dt u 0 y.val, v s y.val⟫_ℂ = 0 := fun y => by
      rw [dt_zero hu (val_mem_GLs y), inner_zero_left]
    simp [this]
  · intro t
    unfold Pr
    have : ∀ y : G n, ⟪u t y.val, dt v 0 y.val⟫_ℂ = 0 := fun y => by
      rw [dt_zero hv (val_mem_GLs y), inner_zero_right]
    simp [this]

end GlobalTheory.CompanionTheory.WaveMult.WaveSymm
