import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.PeriodIntegrals.QuotInv
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.LocalRingCardinality.DataCD
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GroupGeneratedByExp

noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.ClosedMatGroup

section Banach

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem pow_mem_of_mul {S : Set 𝔸} (h1 : (1 : 𝔸) ∈ S) (hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) {a : 𝔸} (ha : a ∈ S) (n : ℕ) :
    a ^ n ∈ S := by
  induction n with
  | zero => simpa using h1
  | succ n ih => rw [pow_succ]; exact hm _ ih _ ha

def lieSub (S : Set 𝔸) (hc : IsClosed S) (h1 : (1 : 𝔸) ∈ S) (hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) : Submodule ℝ 𝔸 where
  carrier := {X | ∀ t : ℝ, NormedSpace.exp (t • X) ∈ S}
  zero_mem' := by intro t; simpa [NormedSpace.exp_zero] using h1
  add_mem' := by
    intro X Y hX hY t
    rw [smul_add]
    refine hc.mem_of_tendsto (Formalism.FourierDecayAlt.P.GroupGeneratedByExp.trotter (t • X) (t • Y)) (Eventually.of_forall fun n => ?_)
    refine pow_mem_of_mul h1 hm (hm _ ?_ _ ?_) n
    · rw [smul_smul]; exact hX _
    · rw [smul_smul]; exact hY _
  smul_mem' := by
    intro c X hX t
    rw [smul_smul]; exact hX _

theorem exp_smul_mem_of_tendsto {S : Set 𝔸} (hc : IsClosed S) (h1 : (1 : 𝔸) ∈ S) (hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S)
    (hi : ∀ Z : 𝔸, NormedSpace.exp Z ∈ S → NormedSpace.exp (-Z) ∈ S) {y : ℕ → 𝔸} {u : 𝔸}
    (hy0 : Tendsto y atTop (𝓝 0)) (hne : ∀ n, y n ≠ 0) (hS : ∀ n, NormedSpace.exp (y n) ∈ S)
    (hu : Tendsto (fun n => ‖y n‖⁻¹ • y n) atTop (𝓝 u)) (t : ℝ) : NormedSpace.exp (t • u) ∈ S := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  have key : ∀ t : ℝ, 0 ≤ t → NormedSpace.exp (t • u) ∈ S := by
    intro t ht
    have hpos : ∀ n, 0 < ‖y n‖ := fun n => norm_pos_iff.2 (hne n)
    have hn0 : Tendsto (fun n => ‖y n‖) atTop (𝓝 0) := by simpa using hy0.norm
    have hk : Tendsto (fun n => ((⌊t / ‖y n‖⌋₊ : ℕ) : ℝ) * ‖y n‖) atTop (𝓝 t) := by
      have hl : Tendsto (fun n => t - ‖y n‖) atTop (𝓝 t) := by simpa using hn0.const_sub t
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds (fun n => ?_) (fun n => ?_)
      · have h := (Nat.lt_floor_add_one (t / ‖y n‖)).le
        rw [div_le_iff₀ (hpos n)] at h
        show t - ‖y n‖ ≤ _
        nlinarith
      · have h := Nat.floor_le (div_nonneg ht (hpos n).le)
        rw [le_div_iff₀ (hpos n)] at h
        exact h
    have hlim := (NormedSpace.exp_continuous.tendsto _).comp (hk.smul hu)
    refine hc.mem_of_tendsto hlim (Eventually.of_forall fun n => ?_)
    have e : (((⌊t / ‖y n‖⌋₊ : ℕ) : ℝ) * ‖y n‖) • ‖y n‖⁻¹ • y n = (⌊t / ‖y n‖⌋₊ : ℕ) • y n := by
      rw [smul_smul, mul_assoc, mul_inv_cancel₀ (hpos n).ne', mul_one, Nat.cast_smul_eq_nsmul]
    simp only [Function.comp]
    rw [e, NormedSpace.exp_nsmul]
    exact pow_mem_of_mul h1 hm (hS n) _
  rcases le_total 0 t with ht | ht
  · exact key t ht
  · have := hi _ (key (-t) (by linarith))
    rwa [neg_smul, neg_neg] at this

theorem eventually_eq_zero [FiniteDimensional ℝ 𝔸] {S : Set 𝔸} (hc : IsClosed S) (h1 : (1 : 𝔸) ∈ S)
    (hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) (hi : ∀ Z : 𝔸, NormedSpace.exp Z ∈ S → NormedSpace.exp (-Z) ∈ S)
    {W : Submodule ℝ 𝔸} (hW : Disjoint (lieSub S hc h1 hm) W) :
    ∀ᶠ y in 𝓝 (0 : 𝔸), y ∈ W → NormedSpace.exp y ∈ S → y = 0 := by
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨y, hy0, hy⟩ := exists_seq_forall_of_frequently hcon
  push_neg at hy
  haveI : ProperSpace 𝔸 := FiniteDimensional.proper ℝ 𝔸
  have hsph : ∀ n, ‖y n‖⁻¹ • y n ∈ Metric.sphere (0 : 𝔸) 1 := fun n => by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 (hy n).2.2)]
  obtain ⟨u, hu1, φ, hφ, hu⟩ := (isCompact_sphere (0 : 𝔸) 1).tendsto_subseq hsph
  have huL : u ∈ lieSub S hc h1 hm :=
    exp_smul_mem_of_tendsto hc h1 hm hi (y := y ∘ φ) (hy0.comp hφ.tendsto_atTop) (fun n => (hy _).2.2)
      (fun n => (hy _).2.1) hu
  have huW : u ∈ W :=
    W.closed_of_finiteDimensional.mem_of_tendsto hu (Eventually.of_forall fun n => W.smul_mem _ (hy _).1)
  have h0 : u = 0 := (Submodule.disjoint_def.1 hW) u huL huW
  rw [h0] at hu1
  simp at hu1

theorem map_exp_mul_exp (p : 𝔸 →L[ℝ] 𝔸) :
    map (fun z => NormedSpace.exp (p z) * NormedSpace.exp (z - p z)) (𝓝 0) = 𝓝 (1 : 𝔸) := by
  have hexp : HasStrictFDerivAt NormedSpace.exp (1 : 𝔸 →L[ℝ] 𝔸) (0 : 𝔸) := hasStrictFDerivAt_exp_zero
  have h1 : HasStrictFDerivAt (fun z => NormedSpace.exp (p z)) ((1 : 𝔸 →L[ℝ] 𝔸).comp p) 0 :=
    HasStrictFDerivAt.comp (0 : 𝔸) (by rw [map_zero]; exact hexp) p.hasStrictFDerivAt
  have h2 : HasStrictFDerivAt (fun z => NormedSpace.exp (z - p z))
      ((1 : 𝔸 →L[ℝ] 𝔸).comp (ContinuousLinearMap.id ℝ 𝔸 - p)) 0 :=
    HasStrictFDerivAt.comp (0 : 𝔸) (f := fun z => z - p z) (by rw [map_zero, sub_zero]; exact hexp)
      (ContinuousLinearMap.id ℝ 𝔸 - p).hasStrictFDerivAt
  have h3 := h1.mul' h2
  have h4 : HasStrictFDerivAt (fun z => NormedSpace.exp (p z) * NormedSpace.exp (z - p z))
      ((ContinuousLinearEquiv.refl ℝ 𝔸 : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) 0 := by
    refine h3.congr_fderiv ?_
    ext z
    simp [NormedSpace.exp_zero]
  have h5 := h4.map_nhds_eq_of_equiv
  simpa [NormedSpace.exp_zero] using h5

theorem eventually_exists_exp [FiniteDimensional ℝ 𝔸] {S : Set 𝔸} (hc : IsClosed S) (h1 : (1 : 𝔸) ∈ S)
    (hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) (hi : ∀ Z : 𝔸, NormedSpace.exp Z ∈ S → NormedSpace.exp (-Z) ∈ S)
    {U : Set 𝔸} (hU : U ∈ 𝓝 (0 : 𝔸)) :
    ∀ᶠ g in 𝓝 (1 : 𝔸), g ∈ S → ∃ X ∈ U, (∀ t : ℝ, NormedSpace.exp (t • X) ∈ S) ∧ NormedSpace.exp X = g := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  obtain ⟨W, hW⟩ := (lieSub S hc h1 hm).exists_isCompl
  let p : 𝔸 →L[ℝ] 𝔸 := LinearMap.toContinuousLinearMap ((lieSub S hc h1 hm).projection W hW)
  have hpL : ∀ z, p z ∈ lieSub S hc h1 hm := fun z => Submodule.projection_apply_mem hW z
  have hqW : ∀ z, z - p z ∈ W := fun z => by
    have h := Submodule.projection_add_projection_eq_self hW z
    have e : z - p z = W.projection _ hW.symm z := by
      rw [sub_eq_iff_eq_add']; exact h.symm
    rw [e]; exact Submodule.projection_apply_mem hW.symm z
  rw [← map_exp_mul_exp p, eventually_map]
  have hp0 : Tendsto p (𝓝 0) (𝓝 0) := by simpa using p.continuous.tendsto 0
  have hq0 : Tendsto (fun z => z - p z) (𝓝 0) (𝓝 (0 : 𝔸)) := by simpa using (tendsto_id (x := 𝓝 (0 : 𝔸))).sub hp0
  filter_upwards [hp0.eventually hU, hq0.eventually (eventually_eq_zero hc h1 hm hi hW.disjoint)] with z hz1 hz2 hg
  have hneg : NormedSpace.exp (-p z) ∈ S := by simpa using hpL z (-1)
  have hq : NormedSpace.exp (z - p z) ∈ S := by
    have h := hm _ hneg _ hg
    rwa [← mul_assoc, ← NormedSpace.exp_add_of_commute (Commute.refl (p z)).neg_left, neg_add_cancel,
      NormedSpace.exp_zero, one_mul] at h
  refine ⟨p z, hz1, hpL z, ?_⟩
  rw [hz2 (hqW z) hq, NormedSpace.exp_zero, mul_one]

end Banach

theorem unrealify_realify {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) :
    unrealify ((WithLp.equiv 2 _).symm (realifyFun X)) = X := by
  ext i j
  apply Complex.ext <;> simp [unrealify, realifyFun]

theorem unrealify_mem_lieOf {m : ℕ} {S : Set (Matrix (Fin m) (Fin m) ℂ)} (hS : PI.IsMatGroup S)
    {x : EuclideanSpace ℝ (Fin m × Fin m × Bool)} (hx : x ∈ lieE S) : unrealify x ∈ lieOf S := by
  let _ := Matrix.linftyOpNormedRing (n := Fin m) (α := ℂ)
  let _ := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin m) (α := ℂ)
  have hc : CompleteSpace (Matrix (Fin m) (Fin m) ℂ) := FiniteDimensional.complete ℝ _
  have hL : ∀ X, X ∈ lieOf S ↔ X ∈ lieSub S hS.1 hS.2.1 hS.2.2.1 := fun X => by
    simp only [lieOf, Set.mem_setOf_eq, Complex.coe_smul]; rfl
  rw [hL]
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨X, hX, rfl⟩ := hx
    rw [unrealify_realify]; exact (hL X).1 hX
  | zero =>
    have e : unrealify (0 : EuclideanSpace ℝ (Fin m × Fin m × Bool)) = 0 := by
      ext i j; apply Complex.ext <;> simp [unrealify]
    rw [e]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have e : unrealify (x + y) = unrealify x + unrealify y := by
      ext i j; apply Complex.ext <;> simp [unrealify]
    rw [e]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    have e : unrealify (c • x) = c • unrealify x := by
      ext i j; apply Complex.ext <;> simp [unrealify]
    rw [e]; exact Submodule.smul_mem _ _ hx

theorem eventually_exists_exp_matrix {m : ℕ} {S : Set (Matrix (Fin m) (Fin m) ℂ)} (hS : PI.IsMatGroup S)
    {U : Set (Matrix (Fin m) (Fin m) ℂ)} (hU : U ∈ 𝓝 (0 : Matrix (Fin m) (Fin m) ℂ)) :
    ∀ᶠ g in 𝓝 (1 : Matrix (Fin m) (Fin m) ℂ), g ∈ S → ∃ X ∈ U, X ∈ lieOf S ∧ NormedSpace.exp X = g := by
  have hi : ∀ Z : Matrix (Fin m) (Fin m) ℂ, NormedSpace.exp Z ∈ S → NormedSpace.exp (-Z) ∈ S := fun Z hZ => by
    rw [Matrix.exp_neg]; exact (hS.2.2.2 _ hZ).1
  let _ := Matrix.linftyOpNormedRing (n := Fin m) (α := ℂ)
  let _ := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin m) (α := ℂ)
  have hc : CompleteSpace (Matrix (Fin m) (Fin m) ℂ) := FiniteDimensional.complete ℝ _
  have h := eventually_exists_exp hS.1 hS.2.1 hS.2.2.1 hi hU
  simp only [lieOf, Set.mem_setOf_eq, Complex.coe_smul]
  exact h

theorem closed_subgroup : ∀ (m : ℕ) (S : Set (Matrix (Fin m) (Fin m) ℂ)), PI.IsMatGroup S → (∀ X : lieE S, unrealify (X : EuclideanSpace ℝ _) ∈ lieOf S) ∧ ∀ ρ : ℝ, 0 < ρ → ∃ δ : ℝ, 0 < δ ∧ ∀ g ∈ S, (∀ i j, ‖(g - 1) i j‖ < δ) → Matrix.of.symm g ∈ expSet S (Metric.ball 0 ρ) := by
  intro m S hS
  refine ⟨fun X => unrealify_mem_lieOf hS X.2, fun ρ hρ => ?_⟩
  let R : Matrix (Fin m) (Fin m) ℂ → EuclideanSpace ℝ (Fin m × Fin m × Bool) :=
    fun X => (WithLp.equiv 2 _).symm (realifyFun X)
  have hR : Continuous R := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun p => ?_)
    obtain ⟨i, j, b⟩ := p
    cases b
    · simp only [realifyFun]; simp; fun_prop
    · simp only [realifyFun]; simp; fun_prop
  have hR0 : R 0 = 0 := by
    ext p; simp [R, realifyFun]
  have hU : R ⁻¹' Metric.ball 0 ρ ∈ 𝓝 (0 : Matrix (Fin m) (Fin m) ℂ) :=
    hR.continuousAt.preimage_mem_nhds (by rw [hR0]; exact Metric.ball_mem_nhds _ hρ)
  have h := eventually_exists_exp_matrix hS hU
  obtain ⟨δ, hδ, hb⟩ := (Metric.eventually_nhds_iff (α := Fin m → Fin m → ℂ)).1 h
  refine ⟨δ, hδ, fun g hg hgδ => ?_⟩
  obtain ⟨X, hXU, hXL, rfl⟩ := @hb g (by
    refine (dist_pi_lt_iff hδ).2 fun i => (dist_pi_lt_iff hδ).2 fun j => ?_
    rw [dist_eq_norm]; exact hgδ i j) hg
  refine ⟨⟨R X, Submodule.subset_span ⟨X, hXL, rfl⟩⟩, ?_, ?_⟩
  · rw [mem_ball_zero_iff]; exact mem_ball_zero_iff.1 hXU
  · simp only [R]; rw [unrealify_realify]

end GlobalTheory.ClosedMatGroup
