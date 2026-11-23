import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsTestZero
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def hsq (x : Lie E a) : ℝ :=
  ∑ i, ∑ j, ∑ w, ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2

theorem hsq_nonneg (x : Lie E a) : 0 ≤ hsq x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem sq_le_hsq (x : Lie E a) (i j : Fin a) (w : InfinitePlace E) :
    ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2 ≤ hsq x := by
  have h1 : ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2 ≤
      ∑ w, ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2 :=
    Finset.single_le_sum (f := fun w => ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ w)
  have h2 : ∑ w, ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2 ≤
      ∑ j, ∑ w, ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ∑ w, ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ j)
  have h3 : ∑ j, ∑ w, ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2 ≤ hsq x :=
    Finset.single_le_sum (f := fun i => ∑ j, ∑ w, ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)
  exact h1.trans (h2.trans h3)

theorem hsq_oneL : hsq (oneL E a) = 0 := by
  simp [hsq, oneL, toL]

theorem dist_oneL_lt {x : Lie E a} {δ : ℝ} (hδ : 0 < δ) (h : hsq x < δ ^ 2) : dist x (oneL E a) < δ := by
  refine (dist_pi_lt_iff hδ).2 fun i => (dist_pi_lt_iff hδ).2 fun j => (dist_pi_lt_iff hδ).2 fun w => ?_
  have h1 := (sq_le_hsq x i j w).trans_lt h
  rw [dist_eq_norm]
  exact lt_of_pow_lt_pow_left₀ 2 hδ.le h1

theorem contDiff_hsq : ContDiff ℝ ∞ (hsq : Lie E a → ℝ) := by
  unfold hsq
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ContDiff.sum fun w _ => ContDiff.norm_sq ℝ ?_
  change ContDiff ℝ ∞ fun x : Lie E a => x i j w - (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w
  fun_prop

theorem ofReal_hsq (x : Lie E a) :
    (hsq x : ℂ) = ∑ w, Matrix.trace ((Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) *
      star (Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E))) w := by
  simp only [hsq, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply, Finset.sum_apply, Pi.mul_apply,
    Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow, Complex.star_def, Complex.mul_conj']
  refine Eq.trans ?_ Finset.sum_comm
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Eq.trans ?_ Finset.sum_comm
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun w _ => rfl

theorem hsq_conj (k : Kinf E a) (x : Lie E a) : hsq (toL (k.1 * Matrix.of x * star k.1)) = hsq x := by
  apply Complex.ofReal_injective
  rw [ofReal_hsq, ofReal_hsq]
  have hk : k.1 * star k.1 = 1 := Matrix.mem_unitaryGroup_iff.1 k.2
  have hk' : star k.1 * k.1 = 1 := Matrix.mem_unitaryGroup_iff'.1 k.2
  set Y : Matrix (Fin a) (Fin a) (Cinf E) := Matrix.of x - 1 with hY
  have e1 : (Matrix.of (toL (k.1 * Matrix.of x * star k.1)) - 1 : Matrix (Fin a) (Fin a) (Cinf E)) = k.1 * Y * star k.1 := by
    rw [hY, mul_sub, sub_mul, mul_one, hk]
    rfl
  have e2 : Matrix.trace ((k.1 * Y * star k.1) * star (k.1 * Y * star k.1)) = Matrix.trace (Y * star Y) := by
    have : (k.1 * Y * star k.1) * star (k.1 * Y * star k.1) = k.1 * ((Y * star Y) * star k.1) := by
      simp only [star_mul, star_star]
      calc k.1 * Y * star k.1 * (k.1 * (star Y * star k.1))
          = k.1 * Y * (star k.1 * k.1) * (star Y * star k.1) := by simp only [mul_assoc]
        _ = k.1 * ((Y * star Y) * star k.1) := by rw [hk']; simp only [mul_one, mul_assoc]
    rw [this, Matrix.trace_mul_comm, mul_assoc, hk', mul_one]
  rw [e1, e2]

end GlobalTheory.CompanionTheory.SmoothRep

namespace GlobalTheory.CompanionTheory.SmoothRep

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

theorem val_image_mem_nhds_one {E : Type} [Field E] [NumberField E] {a : ℕ} {N : Set (GL (Fin a) (Cinf E))} (hN : N ∈ 𝓝 1) :
    (Units.val '' N) ∈ 𝓝 (1 : Matrix (Fin a) (Fin a) (Cinf E)) := by
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  exact (Units.isOpenEmbedding_val (R := Matrix (Fin a) (Fin a) (Cinf E))).isOpenMap.image_mem_nhds hN

theorem exists_bump_conjInv : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (N : Set (GL (Fin a) (Cinf E))), N ∈ 𝓝 1 → ∃ β₀ : Lie E a → ℝ, 0 ≤ β₀ ∧ 0 < β₀ (oneL E a) ∧
      IsTest (fun x => (β₀ x : ℂ)) ∧ ConjInv (fun x => (β₀ x : ℂ)) ∧ ∀ x, β₀ x ≠ 0 → ∃ y ∈ N, toL y.val = x := by
  intro E _ _ _ a N hN
  have h := val_image_mem_nhds_one hN
  have e : (toL '' (Units.val '' N) : Set (Lie E a)) = Units.val '' N := Set.image_id _
  have hV : (toL '' (Units.val '' N) : Set (Lie E a)) ∈ 𝓝 (oneL E a) := by
    rw [e]; exact h
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.1 hV
  have hδ2 : 0 < δ ^ 2 := by positivity
  let f : ContDiffBump (0 : ℝ) := ⟨δ ^ 2 / 4, δ ^ 2 / 2, by positivity, by linarith⟩
  have hsupp : ∀ x : Lie E a, f (hsq x) ≠ 0 → hsq x < δ ^ 2 / 2 := fun x hx => by
    have : hsq x ∈ Function.support f := hx
    rw [f.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg (hsq_nonneg x)] at this
    exact this
  have hmem : ∀ x : Lie E a, hsq x ≤ δ ^ 2 / 2 → ∃ y ∈ N, toL y.val = x := fun x hx => by
    have : x ∈ Metric.ball (oneL E a) δ := dist_oneL_lt hδ (by linarith)
    obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := hb this
    exact ⟨y, hy, rfl⟩
  have hKc : IsClosed {x : Lie E a | hsq x ≤ δ ^ 2 / 2} :=
    isClosed_le contDiff_hsq.continuous continuous_const
  have hts : tsupport (fun x => (f (hsq x) : ℂ)) ⊆ {x : Lie E a | hsq x ≤ δ ^ 2 / 2} :=
    closure_minimal (fun x hx => (hsupp x (fun h0 => hx (by simp [h0]))).le) hKc
  have hKb : {x : Lie E a | hsq x ≤ δ ^ 2 / 2} ⊆ Metric.closedBall (oneL E a) δ := fun x hx =>
    (dist_oneL_lt hδ (by simp only [Set.mem_setOf_eq] at hx; linarith)).le
  refine ⟨fun x => f (hsq x), fun x => f.nonneg, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · show 0 < f (hsq (oneL E a))
    rw [hsq_oneL]
    exact f.pos_of_mem_ball (Metric.mem_ball_self f.rOut_pos)
  · exact Complex.ofRealCLM.contDiff.comp (f.contDiff.comp contDiff_hsq)
  · exact (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) (hts.trans hKb)
  · intro x hx
    obtain ⟨y, _, rfl⟩ := hmem x (hts hx)
    exact y.isUnit
  · intro k x
    show (f (hsq (toL (k.1 * Matrix.of x * star k.1))) : ℂ) = f (hsq x)
    rw [hsq_conj]
  · exact fun x hx => hmem x (hsupp x hx).le

end GlobalTheory.CompanionTheory.SmoothRep
