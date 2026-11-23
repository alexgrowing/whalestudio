import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClosedMatrixSubgroupTheorem

noncomputable section

open Filter Topology Matrix

namespace GlobalTheory.ClosedMatGroup

section Banach

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem hasStrictFDerivAt_ofFn_prod {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ∀ (d : ℕ) (f : Fin d → E → 𝔸) (f' : Fin d → E →L[ℝ] 𝔸) (x : E), (∀ i, f i x = 1) →
    (∀ i, HasStrictFDerivAt (f i) (f' i) x) →
    HasStrictFDerivAt (fun y => (List.ofFn fun i => f i y).prod) (∑ i, f' i) x := by
  intro d
  induction d with
  | zero =>
    intro f f' x _ _
    simpa using (hasStrictFDerivAt_const (1 : 𝔸) x)
  | succ d ih =>
    intro f f' x h1 hd
    have hr := ih (fun i => f i.succ) (fun i => f' i.succ) x (fun i => h1 _) (fun i => hd _)
    have hm := (hd 0).mul' hr
    simp only [List.ofFn_succ, List.prod_cons]
    refine hm.congr_fderiv ?_
    ext1 v
    simp [Fin.sum_univ_succ, h1, add_comm]

theorem exists_left_inv_ofFn_prod {S : Set 𝔸} (h1 : (1 : 𝔸) ∈ S) (hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) :
    ∀ (d : ℕ) (Y : Fin d → 𝔸), (∀ i, NormedSpace.exp (-Y i) ∈ S) →
      ∃ Q ∈ S, Q * (List.ofFn fun i => NormedSpace.exp (Y i)).prod = 1 := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  intro d
  induction d with
  | zero => intro Y _; exact ⟨1, h1, by simp⟩
  | succ d ih =>
    intro Y hY
    obtain ⟨Q, hQ, hQe⟩ := ih (fun i => Y i.succ) (fun i => hY _)
    refine ⟨Q * NormedSpace.exp (-Y 0), hm _ hQ _ (hY 0), ?_⟩
    rw [List.ofFn_succ, List.prod_cons]
    have e : NormedSpace.exp (-Y 0) * NormedSpace.exp (Y 0) = 1 := by
      rw [← NormedSpace.exp_add_of_commute (Commute.refl (Y 0)).neg_left, neg_add_cancel,
        NormedSpace.exp_zero]
    calc Q * NormedSpace.exp (-Y 0) * (NormedSpace.exp (Y 0) * (List.ofFn fun i => NormedSpace.exp (Y i.succ)).prod)
        = Q * (NormedSpace.exp (-Y 0) * NormedSpace.exp (Y 0)) * (List.ofFn fun i => NormedSpace.exp (Y i.succ)).prod := by
          simp only [mul_assoc]
      _ = 1 := by rw [e, mul_one, hQe]

end Banach

section Banach2

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem exists_coords_second_kind [FiniteDimensional ℝ 𝔸] {S : Set 𝔸} (hc : IsClosed S)
    (h1 : (1 : 𝔸) ∈ S) (hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S)
    (hi : ∀ Z : 𝔸, NormedSpace.exp Z ∈ S → NormedSpace.exp (-Z) ∈ S) :
    ∃ (d : ℕ) (Z : Fin d → 𝔸) (s : 𝔸 → Fin d → ℝ), (∀ i, Z i ∈ lieSub S hc h1 hm) ∧
      Tendsto s (𝓝 1) (𝓝 0) ∧
      ∀ᶠ X in 𝓝 (1 : 𝔸), X ∈ S → X = (List.ofFn fun i => NormedSpace.exp (s X i • Z i)).prod := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  obtain ⟨W, hW⟩ := (lieSub S hc h1 hm).exists_isCompl
  let L := lieSub S hc h1 hm
  let d := Module.finrank ℝ L
  let bL := Module.finBasis ℝ L
  let Z : Fin d → 𝔸 := fun i => (bL i : 𝔸)
  have hZ : ∀ i, ∀ t : ℝ, NormedSpace.exp (t • Z i) ∈ S := fun i t => (bL i).2 t
  let c : 𝔸 →L[ℝ] (Fin d → ℝ) :=
    LinearMap.toContinuousLinearMap (bL.equivFun.toLinearMap ∘ₗ L.projectionOnto W hW)
  let p : 𝔸 →L[ℝ] 𝔸 := LinearMap.toContinuousLinearMap (L.projection W hW)
  have hpc : ∀ z, ∑ i, c z i • Z i = p z := by
    intro z
    show ∑ i, (bL.equivFun (L.projectionOnto W hW z)) i • (bL i : 𝔸) = ((L.projectionOnto W hW z : L) : 𝔸)
    conv_rhs => rw [← bL.sum_equivFun (L.projectionOnto W hW z)]
    rw [Submodule.coe_sum]
    rfl
  have hqW : ∀ z, z - p z ∈ W := fun z => by
    have h := Submodule.projection_add_projection_eq_self hW z
    have e : z - p z = W.projection _ hW.symm z := by
      rw [sub_eq_iff_eq_add']; exact h.symm
    rw [e]; exact Submodule.projection_apply_mem hW.symm z
  let P : 𝔸 → 𝔸 := fun z => (List.ofFn fun i => NormedSpace.exp (c z i • Z i)).prod
  let Φ : 𝔸 → 𝔸 := fun z => P z * NormedSpace.exp (z - p z)
  have hexp : HasStrictFDerivAt NormedSpace.exp (1 : 𝔸 →L[ℝ] 𝔸) (0 : 𝔸) := hasStrictFDerivAt_exp_zero
  have hf : ∀ i, HasStrictFDerivAt (fun z => NormedSpace.exp (c z i • Z i))
      ((1 : 𝔸 →L[ℝ] 𝔸).comp (((ContinuousLinearMap.proj i).comp c).smulRight (Z i))) 0 := fun i =>
    HasStrictFDerivAt.comp (0 : 𝔸) (g := NormedSpace.exp) (by rw [map_zero, Pi.zero_apply, zero_smul]; exact hexp)
      (((ContinuousLinearMap.proj i).comp c).smulRight (Z i)).hasStrictFDerivAt
  have hP := hasStrictFDerivAt_ofFn_prod d (fun i z => NormedSpace.exp (c z i • Z i)) _ 0
    (fun i => by simp) hf
  have h2 : HasStrictFDerivAt (fun z => NormedSpace.exp (z - p z))
      ((1 : 𝔸 →L[ℝ] 𝔸).comp (ContinuousLinearMap.id ℝ 𝔸 - p)) 0 :=
    HasStrictFDerivAt.comp (0 : 𝔸) (f := fun z => z - p z) (by rw [map_zero, sub_zero]; exact hexp)
      (ContinuousLinearMap.id ℝ 𝔸 - p).hasStrictFDerivAt
  have hP0 : P 0 = 1 := by simp [P]
  have h4 : HasStrictFDerivAt Φ ((ContinuousLinearEquiv.refl ℝ 𝔸 : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) 0 := by
    refine (hP.mul' h2).congr_fderiv ?_
    ext1 z
    have e1 : (List.ofFn fun i => NormedSpace.exp ((0 : Fin d → ℝ) i • Z i)).prod = 1 := by simp
    simp [e1, hpc]
  have hΦ0 : Φ 0 = 1 := by
    show P 0 * NormedSpace.exp (0 - p 0) = 1
    rw [hP0, map_zero, sub_zero, NormedSpace.exp_zero, one_mul]
  let Ψ := h4.localInverse Φ _ 0
  have hΨ : Tendsto Ψ (𝓝 1) (𝓝 0) := by
    have h := h4.localInverse_tendsto
    rw [hΦ0] at h
    exact h
  have hR : ∀ᶠ X in 𝓝 (1 : 𝔸), Φ (Ψ X) = X := by
    have h := h4.eventually_right_inverse
    rw [hΦ0] at h
    exact h
  have hp0 : Tendsto p (𝓝 0) (𝓝 0) := by simpa using p.continuous.tendsto 0
  have hq0 : Tendsto (fun z => z - p z) (𝓝 0) (𝓝 (0 : 𝔸)) := by
    simpa using (tendsto_id (x := 𝓝 (0 : 𝔸))).sub hp0
  refine ⟨d, Z, fun X => c (Ψ X), fun i => (bL i).2, ?_, ?_⟩
  · have hc0 : Tendsto c (𝓝 0) (𝓝 0) := by simpa using c.continuous.tendsto 0
    exact hc0.comp hΨ
  · filter_upwards [hR, hΨ.eventually (hq0.eventually (eventually_eq_zero hc h1 hm hi hW.disjoint))]
      with X hX1 hX2 hXS
    obtain ⟨Q, hQ, hQe⟩ := exists_left_inv_ofFn_prod h1 hm d (fun i => c (Ψ X) i • Z i)
      (fun i => by rw [← neg_smul]; exact hZ i _)
    have hE : NormedSpace.exp (Ψ X - p (Ψ X)) = Q * X := by
      conv_rhs => rw [← hX1]
      show _ = Q * ((List.ofFn fun i => NormedSpace.exp (c (Ψ X) i • Z i)).prod * NormedSpace.exp (Ψ X - p (Ψ X)))
      rw [← mul_assoc, hQe, one_mul]
    have hw := hX2 (hqW _) (by rw [hE]; exact hm _ hQ _ hXS)
    calc X = Φ (Ψ X) := hX1.symm
      _ = _ := by
        show (List.ofFn fun i => NormedSpace.exp (c (Ψ X) i • Z i)).prod * NormedSpace.exp (Ψ X - p (Ψ X)) = _
        rw [hw, NormedSpace.exp_zero, mul_one]

end Banach2

theorem skew_of_exp_smul_mem {m : ℕ} (A Z : Matrix (Fin m) (Fin m) ℂ)
    (hZ : ∀ t : ℝ, NormedSpace.exp (t • Z) ∈ {X : Matrix (Fin m) (Fin m) ℂ | Xᴴ * A * X = A}) :
    Zᴴ * A + A * Z = 0 := by
  let _ := Matrix.linftyOpNormedRing (n := Fin m) (α := ℂ)
  let _ := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin m) (α := ℂ)
  have _ : CompleteSpace (Matrix (Fin m) (Fin m) ℂ) := FiniteDimensional.complete ℝ _
  have e : ∀ t : ℝ, NormedSpace.exp (t • Zᴴ) * A * NormedSpace.exp (t • Z) = A := fun t => by
    have h := hZ t
    simp only [Set.mem_setOf_eq] at h
    rwa [← Matrix.exp_conjTranspose, conjTranspose_smul, star_trivial] at h
  have hd : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Zᴴ) * A * NormedSpace.exp (t • Z))
      (Zᴴ * A + A * Z) 0 := by
    have h1 := (hasDerivAt_exp_smul_const (𝕂 := ℝ) Zᴴ (0 : ℝ)).mul_const A
    have h2 := h1.mul (hasDerivAt_exp_smul_const (𝕂 := ℝ) Z (0 : ℝ))
    simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one] at h2
    exact h2
  have hc : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Zᴴ) * A * NormedSpace.exp (t • Z)) 0 0 := by
    have h : (fun t : ℝ => NormedSpace.exp (t • Zᴴ) * A * NormedSpace.exp (t • Z)) = fun _ => A :=
      funext e
    rw [h]; exact hasDerivAt_const 0 A
  exact hd.unique hc

theorem coords_second_kind_unitary : ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ), ∃ (d : ℕ)
    (Z : Fin d → Matrix (Fin m) (Fin m) ℂ) (s : Matrix (Fin m) (Fin m) ℂ → Fin d → ℝ),
    (∀ i, (Z i)ᴴ * A + A * Z i = 0) ∧
    Tendsto s (𝓝[{X : Matrix (Fin m) (Fin m) ℂ | Xᴴ * A * X = A}] 1) (𝓝 0) ∧
    ∀ᶠ X in 𝓝[{X : Matrix (Fin m) (Fin m) ℂ | Xᴴ * A * X = A}] 1,
      X = (List.ofFn fun i => NormedSpace.exp (s X i • Z i)).prod := by
  intro m A
  let S := {X : Matrix (Fin m) (Fin m) ℂ | Xᴴ * A * X = A}
  have hc : IsClosed S :=
    isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
      continuous_id) continuous_const
  have h1 : (1 : Matrix (Fin m) (Fin m) ℂ) ∈ S := by simp [S]
  have hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S := by
    intro a ha b hb
    simp only [S, Set.mem_setOf_eq] at ha hb ⊢
    rw [conjTranspose_mul]
    calc bᴴ * aᴴ * A * (a * b) = bᴴ * (aᴴ * A * a) * b := by simp only [Matrix.mul_assoc]
      _ = A := by rw [ha, hb]
  have hi : ∀ Z : Matrix (Fin m) (Fin m) ℂ, NormedSpace.exp Z ∈ S → NormedSpace.exp (-Z) ∈ S := by
    intro Z hZ
    simp only [S, Set.mem_setOf_eq] at hZ ⊢
    have hXY : NormedSpace.exp Z * NormedSpace.exp (-Z) = 1 := by
      rw [← Matrix.exp_add_of_commute _ _ (Commute.refl Z).neg_right, add_neg_cancel,
        NormedSpace.exp_zero]
    calc (NormedSpace.exp (-Z))ᴴ * A * NormedSpace.exp (-Z)
        = (NormedSpace.exp (-Z))ᴴ * ((NormedSpace.exp Z)ᴴ * A * NormedSpace.exp Z) * NormedSpace.exp (-Z) := by
          rw [hZ]
      _ = (NormedSpace.exp Z * NormedSpace.exp (-Z))ᴴ * A * (NormedSpace.exp Z * NormedSpace.exp (-Z)) := by
          rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = A := by rw [hXY]; simp
  let _ := Matrix.linftyOpNormedRing (n := Fin m) (α := ℂ)
  let _ := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin m) (α := ℂ)
  have _ : CompleteSpace (Matrix (Fin m) (Fin m) ℂ) := FiniteDimensional.complete ℝ _
  obtain ⟨d, Z, s, hZ, hs, hev⟩ := exists_coords_second_kind hc h1 hm hi
  exact ⟨d, Z, s, fun i => skew_of_exp_smul_mem A (Z i) (hZ i), hs.mono_left nhdsWithin_le_nhds,
    eventually_nhdsWithin_iff.2 hev⟩

end GlobalTheory.ClosedMatGroup
