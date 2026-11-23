import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothGramSchmidtIndefiniteHermitianFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegativeFrameDomainProductOpenPreconnectedStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusLawOfKilled
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HolDict.Uniq

open Filter Topology

variable {n : ℕ} {ι : Type} [Fintype ι]

def oneE (ι : Type) (n : ℕ) : ι → Fin n → Fin n → ℂ := fun _ a c => if a = c then 1 else 0

def loP (ζ : ℂ) (z : ι → Fin n → Fin n → ℂ) : ι → Fin n → Fin n → ℂ :=
  fun τ a c => if c < a then ζ ^ ((a : ℕ) - c) * z τ a c else 0

def upperParabolic (z : ι → Fin n → Fin n → ℂ) : ι → Fin n → Fin n → ℂ :=
  fun τ a c => if c < a then 0 else z τ a c

def luMap (z : ι → Fin n → Fin n → ℂ) : ι → Fin n → Fin n → ℂ :=
  fun τ => (Matrix.of ((oneE ι n + loP 1 z) τ) * Matrix.of ((oneE ι n + upperParabolic z) τ) : Mt n)

omit [Fintype ι] in
lemma of_oneE (τ : ι) : Matrix.of (oneE ι n τ) = (1 : Mt n) := by
  ext a c
  simp [oneE, Matrix.one_apply]

omit [Fintype ι] in
lemma luMap_eq (z : ι → Fin n → Fin n → ℂ) :
    luMap z = oneE ι n + z + fun τ a c => ∑ j, loP 1 z τ a j * upperParabolic z τ j c := by
  funext τ a c
  have hz : loP 1 z τ a c + upperParabolic z τ a c = z τ a c := by
    simp only [loP, upperParabolic]; split_ifs <;> simp
  simp only [luMap, Pi.add_apply, Matrix.mul_apply, Matrix.of_apply, add_mul, mul_add,
    Finset.sum_add_distrib, oneE, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, ↓reduceIte]
  linear_combination hz

lemma strict_coord (τ : ι) (a c : Fin n) : ∃ L, HasStrictFDerivAt (𝕜 := ℂ) (fun z : ι → Fin n → Fin n → ℂ => z τ a c) L 0 := by
  let L : (ι → Fin n → Fin n → ℂ) →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) c).comp
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => Fin n → ℂ) a).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => Fin n → Fin n → ℂ) τ))
  have hL : (fun z : ι → Fin n → Fin n → ℂ => z τ a c) = ⇑L := by
    funext z; first | rfl | simp [L]
  refine ⟨L, ?_⟩
  rw [hL]; exact L.hasStrictFDerivAt

lemma luMap_strict : HasStrictFDerivAt (luMap : (ι → Fin n → Fin n → ℂ) → _) (ContinuousLinearMap.id ℂ _) 0 := by
  have hlo : ∀ (τ : ι) (a j : Fin n), ∃ L : (ι → Fin n → Fin n → ℂ) →L[ℂ] ℂ, HasStrictFDerivAt (fun z : ι → Fin n → Fin n → ℂ => loP 1 z τ a j) L 0 := by
    intro τ a j
    by_cases h : j < a
    · obtain ⟨L, hL⟩ := strict_coord (n := n) τ a j
      exact ⟨L, by simpa [loP, h] using hL⟩
    · exact ⟨0, by simpa [loP, h] using hasStrictFDerivAt_const (0 : ℂ) (0 : ι → Fin n → Fin n → ℂ)⟩
  have hup : ∀ (τ : ι) (j c : Fin n), ∃ L : (ι → Fin n → Fin n → ℂ) →L[ℂ] ℂ, HasStrictFDerivAt (fun z : ι → Fin n → Fin n → ℂ => upperParabolic z τ j c) L 0 := by
    intro τ j c
    by_cases h : c < j
    · exact ⟨0, by simpa [upperParabolic, h] using hasStrictFDerivAt_const (0 : ℂ) (0 : ι → Fin n → Fin n → ℂ)⟩
    · obtain ⟨L, hL⟩ := strict_coord (n := n) τ j c
      exact ⟨L, by simpa [upperParabolic, h] using hL⟩
  have hB : ∀ (τ : ι) (a c : Fin n), HasStrictFDerivAt
      (fun z : ι → Fin n → Fin n → ℂ => ∑ j, loP 1 z τ a j * upperParabolic z τ j c)
      (0 : (ι → Fin n → Fin n → ℂ) →L[ℂ] ℂ) 0 := by
    intro τ a c
    choose L1 hL1 using hlo τ a
    choose L2 hL2 using fun j => hup τ j c
    first
    | exact (HasStrictFDerivAt.fun_sum (u := Finset.univ) (fun j _ => (hL1 j).fun_mul (hL2 j))).congr_fderiv
        (by simp [loP, upperParabolic])
    | (convert HasStrictFDerivAt.sum (u := Finset.univ) (fun j _ => (hL1 j).mul (hL2 j)) using 1 <;>
        first | (funext z; simp [Finset.sum_apply]) | simp [loP, upperParabolic])
  have hBall : HasStrictFDerivAt
      (fun z : ι → Fin n → Fin n → ℂ => fun τ a c => ∑ j, loP 1 z τ a j * upperParabolic z τ j c)
      (0 : (ι → Fin n → Fin n → ℂ) →L[ℂ] (ι → Fin n → Fin n → ℂ)) 0 := by
    first
    | (refine (hasStrictFDerivAt_pi.2 fun τ => hasStrictFDerivAt_pi.2 fun a =>
          hasStrictFDerivAt_pi.2 fun c => hB τ a c).congr_fderiv ?_
       refine ContinuousLinearMap.ext fun z => ?_
       funext τ a c
       simp)
    | (refine hasStrictFDerivAt_pi'.2 fun τ => ?_
       rw [ContinuousLinearMap.comp_zero]
       refine hasStrictFDerivAt_pi'.2 fun a => ?_
       rw [ContinuousLinearMap.comp_zero]
       refine hasStrictFDerivAt_pi'.2 fun c => ?_
       rw [ContinuousLinearMap.comp_zero]
       exact hB τ a c)
  have hfun : (luMap : (ι → Fin n → Fin n → ℂ) → _) =
      fun z => oneE ι n + z + fun τ a c => ∑ j, loP 1 z τ a j * upperParabolic z τ j c := funext luMap_eq
  rw [hfun]
  have := ((hasStrictFDerivAt_const (oneE ι n) (0 : ι → Fin n → Fin n → ℂ)).add
    (hasStrictFDerivAt_id (0 : ι → Fin n → Fin n → ℂ))).add hBall
  simpa using this

lemma map_luMap : map (luMap : (ι → Fin n → Fin n → ℂ) → _) (𝓝 0) = 𝓝 (oneE ι n) := by
  have h0 : (luMap : (ι → Fin n → Fin n → ℂ) → _) 0 = oneE ι n := by
    rw [luMap_eq]; funext τ a c; simp [loP, upperParabolic]
  have hs : HasStrictFDerivAt (luMap : (ι → Fin n → Fin n → ℂ) → _)
      ((ContinuousLinearEquiv.refl ℂ (ι → Fin n → Fin n → ℂ) : (ι → Fin n → Fin n → ℂ) ≃L[ℂ] _) :
        (ι → Fin n → Fin n → ℂ) →L[ℂ] _) 0 := by
    rw [ContinuousLinearEquiv.coe_refl]; exact luMap_strict
  rw [hs.map_nhds_eq_of_equiv, h0]

lemma norm_loP_le {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1) (z : ι → Fin n → Fin n → ℂ) : ‖loP ζ z‖ ≤ ‖z‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun τ => ?_
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun a => ?_
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun c => ?_
  have hz : ‖z τ a c‖ ≤ ‖z‖ :=
    ((norm_le_pi_norm (z τ a) c).trans (norm_le_pi_norm (z τ) a)).trans (norm_le_pi_norm z τ)
  simp only [loP]
  split_ifs
  · rw [norm_mul, norm_pow]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hζ) (norm_nonneg _)).trans
      (by rw [one_mul]; exact hz)
  · simp

lemma differentiable_loP (z : ι → Fin n → Fin n → ℂ) : Differentiable ℂ fun ζ : ℂ => oneE ι n + loP ζ z := by
  refine differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun c => ?_
  simp only [Pi.add_apply, loP]
  by_cases h : c < a
  · simp only [h, ↓reduceIte]; fun_prop
  · simp only [h, ↓reduceIte]; fun_prop

lemma local_zero {Q : (ι → Fin n → Fin n → ℂ) → ℂ} {Ω : Set (ι → Fin n → Fin n → ℂ)} (hΩ : Ω ∈ 𝓝 (oneE ι n))
    (hQ : DifferentiableOn ℂ Q Ω)
    (hb : ∀ y ∈ Ω, ∀ b : ι → Mt n, (∀ τ, UpT (b τ)) → Q y = 0 → Q (fun τ => (Matrix.of (y τ) * b τ : Mt n)) = 0)
    (hd : ∀ y ∈ Ω, ∀ y' ∈ Ω, ∀ s : ι → Fin n → ℝ,
      (∀ τ, Matrix.of (y' τ) * diagonal (fun a => Complex.exp ((s τ a : ℂ) * Complex.I)) =
        diagonal (fun a => Complex.exp ((s τ a : ℂ) * Complex.I)) * Matrix.of (y τ)) → Q y' = Q y)
    (h1 : Q (oneE ι n) = 0) : Q =ᶠ[𝓝 (oneE ι n)] 0 := by
  obtain ⟨r, hr, hrΩ⟩ := Metric.mem_nhds_iff.1 hΩ
  have hmem : ∀ z : ι → Fin n → Fin n → ℂ, ‖z‖ < r → ∀ ζ : ℂ, ‖ζ‖ ≤ 1 →
      oneE ι n + loP ζ z ∈ Metric.ball (oneE ι n) r := by
    intro z hz ζ hζ
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact (norm_loP_le hζ z).trans_lt hz
  have hdisc : ∀ z : ι → Fin n → Fin n → ℂ, ‖z‖ < r → Q (oneE ι n + loP 1 z) = 0 := by
    intro z hz
    have hgd : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → DifferentiableAt ℂ (fun ζ : ℂ => Q (oneE ι n + loP ζ z)) ζ := by
      intro ζ hζ
      have hQa : DifferentiableAt ℂ Q (oneE ι n + loP ζ z) :=
        (hQ _ (hrΩ (hmem z hz ζ hζ))).differentiableAt
          (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds (hmem z hz ζ hζ)) hrΩ)
      exact hQa.comp ζ ((differentiable_loP z) ζ)
    have he : ∀ (θ : ℝ) (k : Fin n), Complex.exp ((((k : ℕ) : ℝ) * θ : ℝ) * Complex.I) =
        Complex.exp (θ * Complex.I) ^ (k : ℕ) := by
      intro θ k
      rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
    have hcirc : ∀ ζ : ℂ, ‖ζ‖ = 1 → Q (oneE ι n + loP ζ z) = Q (oneE ι n + loP 1 z) := by
      intro ζ hζ
      have hζe : Complex.exp ((Complex.arg ζ : ℂ) * Complex.I) = ζ := by
        have := Complex.norm_mul_exp_arg_mul_I ζ
        rw [hζ] at this; simpa using this
      refine hd _ (hrΩ (hmem z hz 1 (by simp))) _ (hrΩ (hmem z hz ζ hζ.le))
        (fun _ a => ((a : ℕ) : ℝ) * Complex.arg ζ) ?_
      intro τ
      ext a c
      simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply, Pi.add_apply]
      simp only [he, hζe]
      simp only [oneE, loP]
      rcases lt_trichotomy c a with h | h | h
      · have hne : a ≠ c := (ne_of_lt h).symm
        have hca : (c : ℕ) ≤ a := (Fin.lt_iff_val_lt_val.mp h).le
        simp only [if_neg hne, if_pos h, zero_add, one_pow, one_mul]
        rw [show ζ ^ (a : ℕ) = ζ ^ ((a : ℕ) - c) * ζ ^ (c : ℕ) by
          rw [← pow_add, Nat.sub_add_cancel hca]]
        ring
      · subst h; simp [mul_comm]
      · have hne : a ≠ c := ne_of_lt h
        simp [hne, not_lt.2 h.le]
    have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le (U := Metric.ball (0 : ℂ) 1)
      (f := fun ζ : ℂ => Q (oneE ι n + loP ζ z) - Q (oneE ι n + loP 1 z)) Metric.isBounded_ball
      (DifferentiableOn.diffContOnCl fun ζ hζ => by
        rw [closure_ball (0 : ℂ) one_ne_zero, mem_closedBall_zero_iff] at hζ
        exact ((hgd ζ hζ).sub_const _).differentiableWithinAt)
      (C := 0) (fun ζ hζ => by
        rw [frontier_ball (0 : ℂ) one_ne_zero, mem_sphere_zero_iff_norm] at hζ
        simp [hcirc ζ hζ])
      (subset_closure (Metric.mem_ball_self one_pos))
    have hl0 : loP (0 : ℂ) z = 0 := by
      funext τ a c
      simp only [loP, Pi.zero_apply]
      split_ifs with h
      · rw [zero_pow (Nat.sub_ne_zero_of_lt (Fin.lt_iff_val_lt_val.mp h)), zero_mul]
      · rfl
    have : Q (oneE ι n + loP 1 z) = Q (oneE ι n + loP 0 z) := by
      have h0 := norm_le_zero_iff.1 hmax
      simp only [sub_eq_zero] at h0
      exact h0.symm
    rw [this, hl0, add_zero, h1]
  have hS : Metric.ball (0 : ι → Fin n → Fin n → ℂ) (min r 1) ∈ 𝓝 (0 : ι → Fin n → Fin n → ℂ) :=
    Metric.ball_mem_nhds _ (lt_min hr one_pos)
  have himg : luMap '' Metric.ball (0 : ι → Fin n → Fin n → ℂ) (min r 1) ∈ 𝓝 (oneE ι n) := by
    rw [← map_luMap]; exact Filter.image_mem_map hS
  filter_upwards [himg] with y hy
  obtain ⟨z, hz, rfl⟩ := hy
  rw [mem_ball_zero_iff] at hz
  have hzr : ‖z‖ < r := hz.trans_le (min_le_left _ _)
  have hyΩ : oneE ι n + loP 1 z ∈ Ω := hrΩ (hmem z hzr 1 (by simp))
  have hup : ∀ τ, UpT (Matrix.of ((oneE ι n + upperParabolic z) τ) : Mt n) := by
    intro τ
    have hlow : ∀ a c : Fin n, c < a → (Matrix.of ((oneE ι n + upperParabolic z) τ) : Mt n) a c = 0 := by
      intro a c h
      simp [oneE, upperParabolic, h, (ne_of_lt h).symm]
    refine ⟨?_, hlow⟩
    rw [Matrix.det_of_upperTriangular (by intro a c h; exact hlow a c h)]
    refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
    have hv : (Matrix.of ((oneE ι n + upperParabolic z) τ) : Mt n) a a = 1 + z τ a a := by simp [oneE, upperParabolic]
    rw [hv]
    intro h0
    have hm1 : z τ a a = -1 := by linear_combination h0
    have hle : ‖z τ a a‖ ≤ ‖z‖ :=
      ((norm_le_pi_norm (z τ a) a).trans (norm_le_pi_norm (z τ) a)).trans (norm_le_pi_norm z τ)
    rw [hm1, norm_neg, norm_one] at hle
    linarith [hz.trans_le (min_le_right r 1)]
  show Q (luMap z) = 0
  exact hb _ hyΩ _ hup (hdisc z hzr)

theorem eq_zero_of_torus_law (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Hm : ι → Mt n) (q : ι → ℕ) (x₀ : ι → Mt n)
    (w : ι → Fin n → ℤ) (h : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) (f : (ι → Mt n) → ℂ) (hf : HolFn Hm q x₀ w f)
    (ht : ∀ u ∈ UG Hm, ∀ s, f (torEl x₀ s * u) = torCh w s * f u) (h1 : f 1 = 0) : ∀ u ∈ UG Hm, f u = 0 := by
  obtain ⟨P, ⟨hPd, hPw⟩, hPf⟩ := hf
  obtain ⟨hFo, hFc, hFs, hx0⟩ := GlobalTheory.HolDict.frDoms_open_preconnected_stable n ι Hm q x₀ h
  have hx0u : ∀ τ, IsUnit (x₀ τ).det := fun τ => (TorusLaw.units_of_orth (h τ)).1
  have hinv : ∀ τ, (x₀ τ)⁻¹ * x₀ τ = 1 := fun τ => Matrix.nonsing_inv_mul (x₀ τ) (hx0u τ)
  have hinv' : ∀ τ, x₀ τ * (x₀ τ)⁻¹ = 1 := fun τ => Matrix.mul_nonsing_inv (x₀ τ) (hx0u τ)
  have hUpT1 : UpT (1 : Mt n) := ⟨by simp, fun a c hac => Matrix.one_apply_ne (ne_of_lt hac).symm⟩
  have hUHmul : ∀ (H g k : Mt n), g ∈ Formalism.QuantumDeterminants.UH H → k ∈ Formalism.QuantumDeterminants.UH H → g * k ∈ Formalism.QuantumDeterminants.UH H := by
    intro H g k hg hk
    simp only [Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq] at hg hk ⊢
    rw [Matrix.conjTranspose_mul]
    calc kᴴ * gᴴ * H * (g * k) = kᴴ * (gᴴ * H * g) * k := by simp only [Matrix.mul_assoc]
      _ = H := by rw [hg, hk]
  have hUG1 : (1 : ι → Mt n) ∈ UG Hm := by
    simp only [UG, Set.mem_setOf_eq]; intro τ; simp [Formalism.QuantumDeterminants.UH]
  have hUGmul : ∀ u v : ι → Mt n, u ∈ UG Hm → v ∈ UG Hm → u * v ∈ UG Hm := by
    intro u v hu hv
    simp only [UG, Set.mem_setOf_eq] at hu hv ⊢
    intro τ; exact hUHmul _ _ _ (hu τ) (hv τ)
  have htor : ∀ s, torEl x₀ s ∈ UG Hm := fun s => by
    have := TorusLaw.mul_torEl_mem h s hUG1
    rwa [one_mul] at this

  have hPt : ∀ x ∈ frDoms Hm q, ∀ s,
      P (fun τ => (torEl x₀ s τ * Matrix.of (x τ) : Mt n)) = torCh w s * P x := by
    intro x hx s
    choose β _ hβ using fun τ => GlobalTheory.HolDict.GS.smooth_gramSchmidt n (Hm τ) (q τ) (x₀ τ) (h τ)
    have hxτ : ∀ τ, Matrix.of (x τ) ∈ frDom (Hm τ) (q τ) := hx
    obtain ⟨b, hb⟩ : ∃ b : ι → Mt n, ∀ τ, b τ = Matrix.of (β τ (x τ)) := ⟨_, fun _ => rfl⟩
    obtain ⟨u, hu⟩ : ∃ u : ι → Mt n, ∀ τ, u τ = Matrix.of (x τ) * (b τ)⁻¹ * (x₀ τ)⁻¹ :=
      ⟨_, fun _ => rfl⟩
    have hbT : ∀ τ, UpT (b τ) := fun τ => by rw [hb]; exact (hβ τ (x τ) (hxτ τ)).1
    have huG : u ∈ UG Hm := by
      simp only [UG, Set.mem_setOf_eq]; intro τ; rw [hu, hb]; exact (hβ τ (x τ) (hxτ τ)).2
    have hxeq : ∀ τ, (Matrix.of (x τ) : Mt n) = u τ * x₀ τ * b τ := by
      intro τ
      have hbu : IsUnit (b τ).det := isUnit_iff_ne_zero.2 (hbT τ).1
      have e2 : (b τ)⁻¹ * b τ = 1 := Matrix.nonsing_inv_mul (b τ) hbu
      rw [hu]
      calc (Matrix.of (x τ) : Mt n) = Matrix.of (x τ) * ((b τ)⁻¹ * ((x₀ τ)⁻¹ * x₀ τ) * b τ) := by
            rw [hinv τ, Matrix.mul_one, e2, Matrix.mul_one]
        _ = Matrix.of (x τ) * (b τ)⁻¹ * (x₀ τ)⁻¹ * x₀ τ * b τ := by simp only [Matrix.mul_assoc]
    have hF1 : ∀ v ∈ UG Hm, (fun τ => (v τ * x₀ τ : Mt n)) ∈ frDoms Hm q := by
      intro v hv
      have := hFs v hv (fun _ => 1) (fun _ => hUpT1) (fun τ => (x₀ τ : Mt n)) hx0
      simp only [Matrix.mul_one] at this
      exact this
    have e1 : P x = (∏ τ, ∏ a, b τ a a ^ w τ a) * f u := by
      calc P x = P (fun τ => (Matrix.of ((fun τ => (u τ * x₀ τ : Mt n)) τ) * b τ : Mt n)) := by
            congr 1; funext τ; exact hxeq τ
        _ = (∏ τ, ∏ a, b τ a a ^ w τ a) * P (fun τ => (u τ * x₀ τ : Mt n)) := hPw _ (hF1 u huG) b hbT
        _ = (∏ τ, ∏ a, b τ a a ^ w τ a) * f u := by rw [hPf u huG]
    have hv : torEl x₀ s * u ∈ UG Hm := hUGmul _ _ (htor s) huG
    have e2 : P (fun τ => (torEl x₀ s τ * Matrix.of (x τ) : Mt n)) =
        (∏ τ, ∏ a, b τ a a ^ w τ a) * f (torEl x₀ s * u) := by
      calc P (fun τ => (torEl x₀ s τ * Matrix.of (x τ) : Mt n))
          = P (fun τ => (Matrix.of ((fun τ => ((torEl x₀ s * u) τ * x₀ τ : Mt n)) τ) * b τ : Mt n)) := by
            congr 1; funext τ
            show torEl x₀ s τ * Matrix.of (x τ) = torEl x₀ s τ * u τ * x₀ τ * b τ
            rw [hxeq τ]; simp only [Matrix.mul_assoc]
        _ = (∏ τ, ∏ a, b τ a a ^ w τ a) * P (fun τ => ((torEl x₀ s * u) τ * x₀ τ : Mt n)) :=
            hPw _ (hF1 _ hv) b hbT
        _ = (∏ τ, ∏ a, b τ a a ^ w τ a) * f (torEl x₀ s * u) := by rw [hPf _ hv]
    rw [e2, ht u huG s, e1]; ring

  obtain ⟨m, hm⟩ : ∃ m : (ι → Fin n → Fin n → ℂ) → (ι → Fin n → Fin n → ℂ),
      ∀ y, m y = fun τ => (x₀ τ * Matrix.of (y τ) : Mt n) := ⟨_, fun _ => rfl⟩
  have hmd : Differentiable ℂ m := by
    rw [show m = fun y τ => (x₀ τ * Matrix.of (y τ) : Mt n) from funext hm]
    refine differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun c => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply]
    first
    | fun_prop
    | exact Differentiable.sum fun j _ => (differentiable_const _).mul (by fun_prop)
  have hm1 : m (oneE ι n) = fun τ => (x₀ τ : Mt n) := by
    rw [hm]; funext τ
    show x₀ τ * Matrix.of (oneE ι n τ) = x₀ τ
    rw [of_oneE, Matrix.mul_one]
  have hΩ : m ⁻¹' frDoms Hm q ∈ 𝓝 (oneE ι n) :=
    (hmd.continuous.isOpen_preimage _ hFo).mem_nhds (by show m (oneE ι n) ∈ frDoms Hm q; rw [hm1]; exact hx0)
  have hQd : DifferentiableOn ℂ (fun y => P (m y)) (m ⁻¹' frDoms Hm q) :=
    hPd.comp hmd.differentiableOn (fun _ hy => hy)
  have hb' : ∀ y ∈ m ⁻¹' frDoms Hm q, ∀ b : ι → Mt n, (∀ τ, UpT (b τ)) → P (m y) = 0 →
      P (m (fun τ => (Matrix.of (y τ) * b τ : Mt n))) = 0 := by
    intro y hy b hbT h0
    have e : m (fun τ => (Matrix.of (y τ) * b τ : Mt n)) =
        fun τ => (Matrix.of (m y τ) * b τ : Mt n) := by
      refine (hm _).trans ?_
      funext τ
      rw [hm y]
      show x₀ τ * (Matrix.of (y τ) * b τ) = x₀ τ * Matrix.of (y τ) * b τ
      rw [Matrix.mul_assoc]
    rw [e, hPw _ hy b hbT, h0, mul_zero]
  have hd' : ∀ y ∈ m ⁻¹' frDoms Hm q, ∀ y' ∈ m ⁻¹' frDoms Hm q, ∀ s : ι → Fin n → ℝ,
      (∀ τ, Matrix.of (y' τ) * diagonal (fun a => Complex.exp ((s τ a : ℂ) * Complex.I)) =
        diagonal (fun a => Complex.exp ((s τ a : ℂ) * Complex.I)) * Matrix.of (y τ)) →
      P (m y') = P (m y) := by
    intro y hy y' hy' s hcomm
    obtain ⟨E, hE⟩ : ∃ E : ι → Mt n, ∀ τ, E τ = diagonal (fun a => Complex.exp (-(s τ a : ℂ) * Complex.I)) :=
      ⟨_, fun _ => rfl⟩
    have hET : ∀ τ, UpT (E τ) := by
      intro τ
      refine ⟨?_, fun a c hac => ?_⟩
      · rw [hE, Matrix.det_diagonal]
        exact Finset.prod_ne_zero_iff.2 fun a _ => Complex.exp_ne_zero _
      · rw [hE]; exact Matrix.diagonal_apply_ne _ (ne_of_lt hac).symm
    have hDE : ∀ τ, diagonal (fun a => Complex.exp ((s τ a : ℂ) * Complex.I)) * E τ = 1 := by
      intro τ
      rw [hE, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext a
      rw [← Complex.exp_add]; simp
    have htx : ∀ τ, torEl x₀ s τ * x₀ τ =
        x₀ τ * diagonal (fun a => Complex.exp ((s τ a : ℂ) * Complex.I)) := by
      intro τ
      simp only [torEl, Matrix.mul_assoc, hinv τ, Matrix.mul_one]
    have e : m y' = fun τ => (Matrix.of ((fun τ => (torEl x₀ s τ * Matrix.of (m y τ) : Mt n)) τ) * E τ : Mt n) := by
      simp only [hm]; funext τ
      show x₀ τ * Matrix.of (y' τ) = torEl x₀ s τ * (x₀ τ * Matrix.of (y τ)) * E τ
      rw [← Matrix.mul_assoc (torEl x₀ s τ), htx τ, Matrix.mul_assoc (x₀ τ), ← hcomm τ,
        Matrix.mul_assoc, Matrix.mul_assoc, hDE τ, Matrix.mul_one]
    have hT : (fun τ => (torEl x₀ s τ * Matrix.of (m y τ) : Mt n)) ∈ frDoms Hm q := by
      have := hFs (torEl x₀ s) (htor s) (fun _ => 1) (fun _ => hUpT1) (m y) hy
      simp only [Matrix.mul_one] at this
      exact this
    have hc : (∏ τ, ∏ a, E τ a a ^ w τ a) * torCh w s = 1 := by
      simp only [hE, torCh, Matrix.diagonal_apply_eq, ← Finset.prod_mul_distrib, ← mul_zpow,
        ← Complex.exp_add]
      simp
    rw [e, hPw _ hT E hET, hPt _ hy s, ← mul_assoc, hc, one_mul]
  have h1' : P (m (oneE ι n)) = 0 := by
    rw [hm1]
    have := hPf 1 hUG1
    rw [h1] at this
    simpa using this.symm
  have hloc := local_zero (Q := fun y => P (m y)) hΩ hQd hb' hd' h1'

  obtain ⟨m', hm'⟩ : ∃ m' : (ι → Fin n → Fin n → ℂ) → (ι → Fin n → Fin n → ℂ),
      ∀ y, m' y = fun τ => ((x₀ τ)⁻¹ * Matrix.of (y τ) : Mt n) := ⟨_, fun _ => rfl⟩
  have hmm' : ∀ y, m (m' y) = y := by
    intro y; rw [hm, hm']; funext τ
    show x₀ τ * ((x₀ τ)⁻¹ * Matrix.of (y τ)) = Matrix.of (y τ)
    rw [← Matrix.mul_assoc, hinv' τ, Matrix.one_mul]
  have hm'0 : m' (fun τ => (x₀ τ : Mt n)) = oneE ι n := by
    refine (hm' _).trans ?_
    funext τ
    show (x₀ τ)⁻¹ * x₀ τ = Matrix.of (oneE ι n τ)
    rw [of_oneE, hinv τ]
  have hm'c : Continuous m' := by
    rw [show m' = fun y τ => ((x₀ τ)⁻¹ * Matrix.of (y τ) : Mt n) from funext hm']
    refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun c => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply]
    first
    | fun_prop
    | exact continuous_finset_sum _ fun j _ => continuous_const.mul (by fun_prop)
  have hPloc : P =ᶠ[𝓝 (fun τ => (x₀ τ : Mt n))] 0 := by
    have ht' : Tendsto m' (𝓝 (fun τ => (x₀ τ : Mt n))) (𝓝 (oneE ι n)) := by
      rw [← hm'0]; exact hm'c.continuousAt
    filter_upwards [hloc.comp_tendsto ht'] with y hy
    have hy' : P (m (m' y)) = 0 := by simpa [Function.comp] using hy
    rw [hmm' y] at hy'
    exact hy'
  have hEq := GlobalTheory.SCV.eqOn_of_eventuallyEq hFo hFc hPd
    (differentiableOn_const (0 : ℂ) : DifferentiableOn ℂ (0 : (ι → Fin n → Fin n → ℂ) → ℂ) _) hx0 hPloc
  intro u hu
  rw [hPf u hu]
  have hux : (fun τ => (u τ * x₀ τ : Mt n)) ∈ frDoms Hm q := by
    have := hFs u hu (fun _ => 1) (fun _ => hUpT1) (fun τ => (x₀ τ : Mt n)) hx0
    simp only [Matrix.mul_one] at this
    exact this
  exact hEq hux

end GlobalTheory.HolDict.Uniq
