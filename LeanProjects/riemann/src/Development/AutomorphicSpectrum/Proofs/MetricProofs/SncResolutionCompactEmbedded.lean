import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top

open MvPolynomial ReciprocityTheory.AnForm.R

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem normSq_pos {z : (Σ k, ι k) → ℂ} {k : K} (h : ∃ i, z ⟨k, i⟩ ≠ 0) :
    0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := by
  obtain ⟨i, hi⟩ := h
  exact Finset.sum_pos' (fun j _ => by positivity) ⟨i, Finset.mem_univ _, by positivity⟩

theorem proj_smul (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ) :
    proj (fun q => c q.1 * z q) = proj z := by
  funext q
  obtain ⟨k, i, j⟩ := q
  simp only [proj, norm_mul, mul_pow, ← Finset.mul_sum, map_mul]
  have h1 : ((‖c k‖ ^ 2 : ℝ) : ℂ) = c k * starRingEnd ℂ (c k) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h2 : c k * starRingEnd ℂ (c k) ≠ 0 := mul_ne_zero (hc k) (by simpa using hc k)
  rw [Complex.ofReal_mul, h1, ← mul_div_mul_left (z ⟨k, i⟩ * starRingEnd ℂ (z ⟨k, j⟩)) _ h2]
  congr 1
  ring

theorem continuousOn_proj :
    ContinuousOn (proj (ι := ι)) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  refine continuousOn_pi.2 fun q => ?_
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun z hz => ?_
  exact Complex.ofReal_ne_zero.2 (normSq_pos (hz q.1)).ne'

theorem compactSpace_pts {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) :
    CompactSpace (Pts P) := by
  let S : Set ((Σ k, ι k) → ℂ) := {z | (∀ k, ∑ i, ‖z ⟨k, i⟩‖ ^ 2 = 1) ∧ ∀ f ∈ P, eval z f = 0}
  have hne : ∀ z ∈ S, ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := by
    intro z hz k
    by_contra h
    push Not at h
    have := hz.1 k
    simp [h] at this
  have hS : IsCompact S := by
    apply Metric.isCompact_of_isClosed_isBounded
    · simp only [S, Set.setOf_and, Set.setOf_forall]
      refine IsClosed.inter (isClosed_iInter fun k => isClosed_eq (by fun_prop) continuous_const)
        (isClosed_iInter fun f => isClosed_iInter fun _ =>
          isClosed_eq (MvPolynomial.continuous_eval f) continuous_const)
    · refine (Metric.isBounded_closedBall (x := (0 : (Σ k, ι k) → ℂ)) (r := 1)).subset fun z hz => ?_
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      rintro ⟨k, i⟩
      have h1 : ‖z ⟨k, i⟩‖ ^ 2 ≤ 1 := by
        rw [← hz.1 k]
        exact Finset.single_le_sum (f := fun j => ‖z ⟨k, j⟩‖ ^ 2) (fun j _ => by positivity)
          (Finset.mem_univ i)
      nlinarith [norm_nonneg (z ⟨k, i⟩)]
  have hE : Pts P = proj '' S := by
    apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      have hpos : ∀ k, 0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := fun k => normSq_pos (hz.1 k)
      let c : K → ℂ := fun k => (((√(∑ i, ‖z ⟨k, i⟩‖ ^ 2))⁻¹ : ℝ) : ℂ)
      have hc : ∀ k, c k ≠ 0 := fun k =>
        Complex.ofReal_ne_zero.2 (inv_ne_zero (Real.sqrt_pos.2 (hpos k)).ne')
      refine ⟨fun q => c q.1 * z q, ⟨fun k => ?_, eval_eq_zero_of_smul hP c z hz.2⟩, proj_smul c hc z⟩
      simp only [norm_mul, mul_pow, ← Finset.mul_sum, c, Complex.norm_real, Real.norm_eq_abs, sq_abs,
        inv_pow]
      rw [Real.sq_sqrt (hpos k).le, inv_mul_cancel₀ (hpos k).ne']
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨z, ⟨hne z hz, hz.2⟩, rfl⟩
  rw [← isCompact_iff_compactSpace, hE]
  exact hS.image_of_continuousOn (continuousOn_proj.mono hne)

variable {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)}

theorem mem_src_iff (p : (k : K) → ι k) (x : Pts P) :
    x ∈ src P p ↔ ∀ k, x.1 ⟨k, (p k, p k)⟩ ≠ 0 := by
  refine forall_congr' fun k => ?_
  have h : ((∑ i, ‖rep x ⟨k, i⟩‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (normSq_pos ((rep_mem x).1 k)).ne'
  rw [← proj_rep x]
  simp only [proj, ne_eq, div_eq_zero_iff, h, or_false, mul_eq_zero, map_eq_zero, or_self]

theorem isOpen_alt_bis (p : (k : K) → ι k) : IsOpen (src P p) := by
  have : src P p = ⋂ k, {x : Pts P | x.1 ⟨k, (p k, p k)⟩ ≠ 0} := by
    ext x; simp [mem_src_iff]
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_ne_fun ((continuous_apply _).comp continuous_subtype_val) continuous_const

theorem affCoord_rep (p : (k : K) → ι k) (x : Pts P) (hx : x ∈ src P p) (q : Σ k, ι k) :
    affCoord p (rep x) q = x.1 ⟨q.1, (q.2, p q.1)⟩ / x.1 ⟨q.1, (p q.1, p q.1)⟩ := by
  obtain ⟨k, i⟩ := q
  have h : ((∑ i, ‖rep x ⟨k, i⟩‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (normSq_pos ((rep_mem x).1 k)).ne'
  have h1 : rep x ⟨k, p k⟩ ≠ 0 := hx k
  have h2 : starRingEnd ℂ (rep x ⟨k, p k⟩) ≠ 0 := by simpa using h1
  rw [← proj_rep x]
  simp only [proj, affCoord]
  rw [div_div_div_cancel_right₀ h, mul_div_mul_right _ _ h2]

theorem proj_affCoord (p : (k : K) → ι k) (x : Pts P) (hx : x ∈ src P p) :
    proj (affCoord p (rep x)) = x.1 := by
  have hA : affCoord p (rep x) = fun q => (rep x ⟨q.1, p q.1⟩)⁻¹ * rep x q := by
    funext q; simp [affCoord, div_eq_inv_mul]
  rw [hA, proj_smul (fun k => (rep x ⟨k, p k⟩)⁻¹) (fun k => inv_ne_zero (hx k)), proj_rep]

theorem isEmbedding_affCoord (p : (k : K) → ι k) :
    Topology.IsEmbedding (fun x : src P p => affCoord p (rep x.1)) := by
  have hc : Continuous (fun x : src P p => affCoord p (rep x.1)) := by
    refine continuous_pi fun q => ?_
    simp only [affCoord_rep p _ (Subtype.prop _)]
    have hv : ∀ r : (Σ k, ι k × ι k), Continuous fun a : src P p => a.1.1 r := fun r =>
      (continuous_apply r).comp (continuous_subtype_val.comp continuous_subtype_val)
    exact Continuous.div (hv _) (hv _) fun x => (mem_src_iff p x.1).1 x.2 q.1
  let U : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
  have hU : ∀ x : src P p, affCoord p (rep x.1) ∈ U := fun x k =>
    ⟨p k, by simpa [affCoord] using x.2 k⟩
  let f : src P p → U := fun x => ⟨_, hU x⟩
  have hf : Continuous f := hc.subtype_mk _
  have hg : Continuous (U.restrict proj) := continuousOn_proj.restrict
  have hgf : U.restrict proj ∘ f = Subtype.val ∘ Subtype.val := by
    funext x; exact proj_affCoord p x.1 x.2
  have he : Topology.IsEmbedding f :=
    Topology.IsEmbedding.of_comp hf hg
      (hgf ▸ Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal)
  exact Topology.IsEmbedding.subtypeVal.comp he

theorem isEmbedding_coord (p : (k : K) → ι k) :
    Topology.IsEmbedding (fun x : src P p => coord P p x) := by
  have h : Topology.IsEmbedding
      (fun y : (Σ k, ι k) → ℂ => (renPt y : Fin (Fintype.card (Σ k, ι k)) → ℂ)) :=
    Function.LeftInverse.isEmbedding (f := fun t => t ∘ Fintype.equivFin (Σ k, ι k))
      (fun y => by funext q; simp [renPt]) (by fun_prop) (by fun_prop)
  exact h.comp (isEmbedding_affCoord p)

theorem compact_open_embedding (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hP : IsMultiHomogIdeal P) :
    CompactSpace (Pts P) ∧ ∀ p : (k : K) → ι k,
      IsOpen (src P p) ∧ Topology.IsEmbedding (fun x : src P p => coord P p x) :=
  ⟨compactSpace_pts hP, fun p => ⟨isOpen_alt_bis p, isEmbedding_coord p⟩⟩

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Top
