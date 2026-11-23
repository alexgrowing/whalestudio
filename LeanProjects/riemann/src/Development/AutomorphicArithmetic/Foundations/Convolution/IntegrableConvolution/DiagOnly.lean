import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TrDefs

noncomputable section

open GroundTheory.Automorphic UpperTheory.ConvolutionTheory.C
open scoped InnerProductSpace

namespace UpperTheory.ConvolutionTheory.L1

section SlopeTestRemainingChoices
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem prj_fd (Z : Submodule ℂ H) [FiniteDimensional ℂ Z] : prj Z = Z.starProjection := by
  have h : Z.topologicalClosure = Z :=
    (Submodule.closed_of_finiteDimensional Z).submodule_topologicalClosure_eq
  have key : ∀ (K : Submodule ℂ H) [K.HasOrthogonalProjection], K = Z →
      K.starProjection = Z.starProjection := by
    intro K _ hK
    subst hK
    rfl
  exact key _ h

private def cmp (Z : Submodule ℂ H) [FiniteDimensional ℂ Z] (T : H →L[ℂ] H) : Z →ₗ[ℂ] Z :=
  (Z.orthogonalProjectionOnto : H →L[ℂ] Z).toLinearMap ∘ₗ T.toLinearMap ∘ₗ Z.subtype

private theorem cmp_coe (Z : Submodule ℂ H) [FiniteDimensional ℂ Z] (T : H →L[ℂ] H) (z : Z) :
    ((cmp Z T z : Z) : H) = Z.starProjection (T z) := rfl

private theorem trOn_fd (Z : Submodule ℂ H) [FiniteDimensional ℂ Z] (T : H →L[ℂ] H) :
    trOn Z T = LinearMap.trace ℂ Z (cmp Z T) := by
  let b := stdOrthonormalBasis ℂ Z
  rw [LinearMap.trace_eq_sum_inner _ b]
  unfold trOn trace
  rw [prj_fd]
  have hP : ∀ x : H, Z.starProjection x = ∑ j, ⟪(b j : H), x⟫_ℂ • (b j : H) := by
    intro x
    rw [b.starProjection_eq_sum_rankOne]
    simp [InnerProductSpace.rankOne_apply]
  have hterm : ∀ e : H, ⟪e, (Z.starProjection ∘L T ∘L Z.starProjection) e⟫_ℂ =
      ∑ j, ⟪(b j : H), e⟫_ℂ * ⟪e, Z.starProjection (T (b j))⟫_ℂ := by
    intro e
    simp only [ContinuousLinearMap.comp_apply]
    rw [hP e]
    simp only [map_sum, map_smul, inner_sum, inner_smul_right]
  have hs : HasSum (fun i => ⟪stdHilbertBasis ℂ H i,
      (Z.starProjection ∘L T ∘L Z.starProjection) (stdHilbertBasis ℂ H i)⟫_ℂ)
      (∑ j, ⟪(b j : H), Z.starProjection (T (b j))⟫_ℂ) := by
    simp_rw [hterm]
    exact hasSum_sum fun j _ => (stdHilbertBasis ℂ H).hasSum_inner_mul_inner _ _
  rw [hs.tsum_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Submodule.coe_inner, cmp_coe]

private theorem trace_cut {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    [FiniteDimensional ℂ Z] {ι : Type} (s : Finset ι) (a a' : ι → Module.End ℂ Z)
    (T Q : Module.End ℂ Z) (hT : ∀ j ∈ s, a j * T = T * a' j)
    (ha : ∀ j ∈ s, ∀ i ∈ s, Commute (a j) (a i)) (ha' : ∀ j ∈ s, ∀ i ∈ s, Commute (a j) (a' i))
    (hQ : ∀ j ∈ s, Commute (a j) Q)
    (hs : ∀ j ∈ s, LinearMap.IsSymmetric (a j)) (hs' : ∀ j ∈ s, LinearMap.IsSymmetric (a' j))
    (hQs : LinearMap.IsSymmetric Q) (hQQ : Q * Q = Q)
    (hQd : ∀ j ∈ s, Q * (a j - a' j) = 0)
    (hker : ∀ z, (∀ j ∈ s, a j z = a' j z) → Q z = z) :
    LinearMap.trace ℂ Z T = LinearMap.trace ℂ Z (T * Q) := by
  set M : Module.End ℂ Z := ∑ j ∈ s, (a j - a' j) * (a j - a' j) + Q with hM
  have hds : ∀ j ∈ s, LinearMap.IsSymmetric (a j - a' j) := fun j hj x y => by
    simp only [LinearMap.sub_apply, inner_sub_left, inner_sub_right, hs j hj x y, hs' j hj x y]
  have hinj : LinearMap.ker M = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro z hz
    have h1 : ⟪z, M z⟫_ℂ = ∑ j ∈ s, ((‖(a j - a' j) z‖ ^ 2 : ℝ) : ℂ) + ((‖Q z‖ ^ 2 : ℝ) : ℂ) := by
      have hq : ⟪z, Q z⟫_ℂ = ((‖Q z‖ ^ 2 : ℝ) : ℂ) := by
        have : ⟪z, Q z⟫_ℂ = ⟪z, Q (Q z)⟫_ℂ := by
          rw [← Module.End.mul_apply, hQQ]
        rw [this, ← hQs z (Q z), inner_self_eq_norm_sq_to_K]
        push_cast
        rfl
      rw [hM, LinearMap.add_apply, LinearMap.sum_apply, inner_add_right, inner_sum, hq]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Module.End.mul_apply, ← hds j hj z, inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    rw [hz, inner_zero_right] at h1
    have h2 : ∑ j ∈ s, ‖(a j - a' j) z‖ ^ 2 + ‖Q z‖ ^ 2 = 0 := by
      exact_mod_cast h1.symm
    have hn : 0 ≤ ∑ j ∈ s, ‖(a j - a' j) z‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    have hq0 : ‖Q z‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖Q z‖]
    have hd0 : ∑ j ∈ s, ‖(a j - a' j) z‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖Q z‖]
    have hd : ∀ j ∈ s, a j z = a' j z := by
      intro j hj
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)).1 hd0 j hj
      have h3 : (a j - a' j) z = 0 := by simpa using this
      exact sub_eq_zero.1 h3
    rw [← hker z hd]
    simpa using hq0
  obtain ⟨u, hu⟩ : IsUnit M := (LinearMap.isUnit_iff_ker_eq_bot M).2 hinj
  set c : Module.End ℂ Z := ((u⁻¹ : (Module.End ℂ Z)ˣ) : Module.End ℂ Z) with hc
  have hMc : M * c = 1 := by rw [hc, ← hu]; exact u.mul_inv
  have hcomM : ∀ j ∈ s, Commute (a j) M := by
    intro j hj
    refine Commute.add_right (Commute.sum_right _ _ _ fun i hi => ?_) (hQ j hj)
    have : Commute (a j) (a i - a' i) := (ha j hj i hi).sub_right (ha' j hj i hi)
    exact this.mul_right this
  have hcomc : ∀ j ∈ s, Commute (a j) c := by
    intro j hj
    have : Commute (a j) (u : Module.End ℂ Z) := by rw [hu]; exact hcomM j hj
    exact this.units_inv_right
  have hzero : ∀ j ∈ s, LinearMap.trace ℂ Z (T * ((a j - a' j) * (a j - a' j) * c)) = 0 := by
    intro j hj
    set x := (a j - a' j) * c with hx
    have hxc : Commute (a j) x :=
      ((ha j hj j hj).sub_right (ha' j hj j hj)).mul_right (hcomc j hj)
    have e1 : T * ((a j - a' j) * (a j - a' j) * c) = T * a j * x - T * a' j * x := by
      rw [hx]; noncomm_ring
    rw [e1, map_sub, ← hT j hj, mul_assoc (a j), LinearMap.trace_mul_comm ℂ (a j),
      mul_assoc T, mul_assoc T, hxc.eq, sub_self]
  have hQM : Q * M = Q := by
    have : Q * ∑ j ∈ s, (a j - a' j) * (a j - a' j) = 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [← mul_assoc, hQd j hj, zero_mul]
    rw [hM, mul_add, this, zero_add, hQQ]
  have hQc : Q * c = Q := by
    calc Q * c = Q * M * c := by rw [hQM]
      _ = Q := by rw [mul_assoc, hMc, mul_one]
  calc LinearMap.trace ℂ Z T = LinearMap.trace ℂ Z (T * (M * c)) := by rw [hMc, mul_one]
    _ = ∑ j ∈ s, LinearMap.trace ℂ Z (T * ((a j - a' j) * (a j - a' j) * c))
          + LinearMap.trace ℂ Z (T * (Q * c)) := by
        rw [hM, add_mul, mul_add, map_add, Finset.sum_mul, Finset.mul_sum, map_sum]
    _ = LinearMap.trace ℂ Z (T * Q) := by
        rw [Finset.sum_eq_zero hzero, zero_add, hQc]

end SlopeTestRemainingChoices

section Aux2
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem mem_eigIn (W : Submodule ℂ H) (A : H →L[ℂ] H) (x : ℝ) (v : H) :
    v ∈ eigIn W A x ↔ v ∈ W ∧ A v = (x : ℂ) • v := by
  simp [eigIn, Module.End.mem_eigenspace_iff]

private theorem proj_comm (W : Submodule ℂ H) [W.HasOrthogonalProjection] (B : H →L[ℂ] H)
    (hB : ∀ x y, ⟪B x, y⟫_ℂ = ⟪x, B y⟫_ℂ) (hW : ∀ w ∈ W, B w ∈ W) (x : H) :
    W.starProjection (B x) = B (W.starProjection x) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hW _ (by simp)) fun w hw => ?_
  rw [← map_sub, hB]
  exact Submodule.starProjection_inner_eq_zero _ _ (hW w hw)

private theorem inner_pow_nonneg (a : H →L[ℂ] H) (hs : ∀ x y, ⟪a x, y⟫_ℂ = ⟪x, a y⟫_ℂ)
    (hp : ∀ x, 0 ≤ RCLike.re ⟪x, a x⟫_ℂ) (k : ℕ) :
    ∀ v, 0 ≤ RCLike.re ⟪v, (a ^ k) v⟫_ℂ := by
  induction k using Nat.twoStepInduction with
  | zero =>
    intro v
    simp only [pow_zero, ContinuousLinearMap.one_apply]
    rw [inner_self_eq_norm_sq]
    positivity
  | one => intro v; simpa using hp v
  | more k ih _ =>
    intro v
    have e : (a ^ (k + 2)) v = a ((a ^ k) (a v)) := by
      rw [pow_succ', pow_succ]
      rfl
    rw [e, ← hs]
    exact ih (a v)

private theorem pow_root (a : H →L[ℂ] H) (hs : ∀ x y, ⟪a x, y⟫_ℂ = ⟪x, a y⟫_ℂ)
    (hp : ∀ x, 0 ≤ RCLike.re ⟪x, a x⟫_ℂ) {y : ℝ} (hy : 0 < y) (n : ℕ) (v : H)
    (h : (a ^ (n + 1)) v = ((y : ℂ) ^ (n + 1)) • v) : a v = (y : ℂ) • v := by
  set c : H →L[ℂ] H := (y : ℂ) • 1 with hc
  have hcomm : Commute a c := (Commute.one_right a).smul_right _
  have hcp : ∀ k, c ^ k = ((y : ℂ) ^ k) • (1 : H →L[ℂ] H) := fun k => by
    rw [hc, smul_pow, one_pow]
  set w := a v - (y : ℂ) • v with hw
  have hwe : (a - c) v = w := by simp [hc, hw]
  have hg := hcomm.geom_sum₂_mul (n + 1)
  have h0 : (∑ i ∈ Finset.range (n + 1), a ^ i * c ^ (n + 1 - 1 - i)) w = 0 := by
    rw [← hwe]
    have := congrArg (fun X : H →L[ℂ] H => X v) hg
    simp only [ContinuousLinearMap.mul_apply] at this
    rw [this, ContinuousLinearMap.sub_apply, h, hcp]
    simp
  have h1 : ∑ i ∈ Finset.range (n + 1), y ^ (n - i) * RCLike.re ⟪w, (a ^ i) w⟫_ℂ = 0 := by
    have h2 := congrArg (fun u => RCLike.re ⟪w, u⟫_ℂ) h0
    simp only [ContinuousLinearMap.sum_apply, inner_sum, map_sum, inner_zero_right, map_zero] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Nat.add_sub_cancel, hcp, ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, map_smul, inner_smul_right]
    rw [← Complex.ofReal_pow, RCLike.re_eq_complex_re, Complex.re_ofReal_mul]
  have hnn : ∀ i ∈ Finset.range (n + 1), 0 ≤ y ^ (n - i) * RCLike.re ⟪w, (a ^ i) w⟫_ℂ :=
    fun i _ => mul_nonneg (by positivity) (inner_pow_nonneg a hs hp i w)
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h1 0 (by simp)
  have h4 : ‖w‖ ^ 2 = 0 := by
    simp only [Nat.sub_zero, pow_zero, ContinuousLinearMap.one_apply] at h3
    rw [inner_self_eq_norm_sq] at h3
    rcases mul_eq_zero.1 h3 with h5 | h5
    · exact absurd h5 (by positivity)
    · exact h5
  have h5 : w = 0 := by simpa using h4
  exact sub_eq_zero.1 h5

private theorem list_prod_apply (a : H →L[ℂ] H) (v : H) (L : List (H →L[ℂ] H))
    (hL : ∀ l ∈ L, Commute l a ∧ l v = a v) : L.prod v = (a ^ L.length) v := by
  induction L with
  | nil => simp
  | cons l L ih =>
    have h1 := hL l (by simp)
    have h2 := ih fun l' hl' => hL l' (by simp [hl'])
    have h3 : Commute l (a ^ L.length) := h1.1.pow_right _
    calc (l :: L).prod v = l (L.prod v) := by simp
      _ = (l * a ^ L.length) v := by rw [h2]; rfl
      _ = (a ^ L.length * l) v := by rw [h3.eq]
      _ = (a ^ L.length) (a v) := by rw [ContinuousLinearMap.mul_apply, h1.2]
      _ = (a ^ (l :: L).length) v := by
        rw [List.length_cons, pow_succ]
        rfl

open Fin.NatCast Fin.CommRing in
private theorem cycle_const {X : Type} {m : ℕ} (f : Fin (m + 1) → X) (i₀ : Fin (m + 1))
    (h : ∀ j, j ≠ i₀ → f j = f (j + 1)) (j : Fin (m + 1)) : f j = f (i₀ + 1) := by
  have key : ∀ k : ℕ, k ≤ m → f (i₀ + 1 + (k : Fin (m + 1))) = f (i₀ + 1) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      rw [← ih (by omega)]
      have hne : i₀ + 1 + (k : Fin (m + 1)) ≠ i₀ := by
        intro he
        have h0 : ((k + 1 : ℕ) : Fin (m + 1)) = 0 := by
          have : i₀ + ((k + 1 : ℕ) : Fin (m + 1)) = i₀ + 0 := by
            calc i₀ + ((k + 1 : ℕ) : Fin (m + 1)) = i₀ + 1 + (k : Fin (m + 1)) := by
                  push_cast
                  ring
              _ = i₀ := he
              _ = i₀ + 0 := by simp
          exact add_left_cancel this
        rw [Fin.natCast_eq_zero] at h0
        have := Nat.le_of_dvd (by omega) h0
        omega
      rw [h _ hne]
      congr 1
      push_cast
      ring
  have hj := key (j - (i₀ + 1)).val (by have := (j - (i₀ + 1)).isLt; omega)
  rw [Fin.cast_val_eq_self] at hj
  rwa [add_sub_cancel] at hj

end Aux2

end UpperTheory.ConvolutionTheory.L1

open UpperTheory.ConvolutionTheory.L1 in
theorem UpperTheory.ConvolutionTheory.L1.diagOnly :
    UpperTheory.ConvolutionTheory.L1.DiagOnly := by
  intro Γ G H _ _ _ _ _ _ π V m ι E A U hS y hy hfd
  have hAA : ∀ i j, Commute (A i) (A j) := fun i j =>
    ContinuousLinearMap.ext fun v => hS.A_A i j v
  have hsa : ∀ i x z, ⟪A i x, z⟫_ℂ = ⟪x, A i z⟫_ℂ := fun i x z =>
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1
      (isSelfAdjoint_of_nonneg (hS.A_pos i))) x z
  have hpos : ∀ i x, 0 ≤ RCLike.re ⟪x, A i x⟫_ℂ := fun i x => by
    rw [inner_apply_eq_norm_sqrt_sq (hS.A_pos i) x]
    simp only [← Complex.ofReal_pow, RCLike.re_eq_complex_re, Complex.ofReal_re]
    positivity
  have memZ : ∀ v, v ∈ prodEig V E A (y ^ (m + 1)) ↔ (v ∈ V ∧ E v = v) ∧
      (List.ofFn A).prod v = ((y : ℂ) ^ (m + 1)) • v := by
    intro v
    simp [prodEig, mem_eigIn]
  have memJ : ∀ v, v ∈ jointEig V E A y ↔ (v ∈ V ∧ E v = v) ∧ ∀ i, A i v = (y : ℂ) • v := by
    intro v
    simp only [jointEig, Submodule.mem_iInf, mem_eigIn]
    simp only [Complex.ofReal_one, one_smul]
    exact ⟨fun h => ⟨(h 0).1, fun i => (h i).2⟩, fun h i => ⟨h.1, h.2 i⟩⟩
  have hJZ : jointEig V E A y ≤ prodEig V E A (y ^ (m + 1)) := by
    intro v hv
    obtain ⟨h1, h2⟩ := (memJ v).1 hv
    refine (memZ v).2 ⟨h1, ?_⟩
    have := list_prod_apply ((y : ℂ) • (1 : H →L[ℂ] H)) v (List.ofFn A) (by
      intro l hl
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hl
      exact ⟨(Commute.one_right _).smul_right _, by simp [h2 i]⟩)
    rw [this, List.length_ofFn, smul_pow, one_pow]
    simp
  refine ⟨hJZ, fun i₀ S hSA => ?_⟩
  generalize hZ : prodEig V E A (y ^ (m + 1)) = Z at memZ hJZ hfd ⊢
  generalize hJ : jointEig V E A y = J at memJ hJZ ⊢
  haveI : FiniteDimensional ℂ J := Submodule.finiteDimensional_of_le hJZ
  have hZinv : ∀ j, ∀ v ∈ Z, A j v ∈ Z := by
    intro j v hv
    obtain ⟨⟨h1, h2⟩, h3⟩ := (memZ v).1 hv
    refine (memZ _).2 ⟨⟨hS.A_mem j v h1, ?_⟩, ?_⟩
    · rw [← hS.A_E, h2]
    · have hc : Commute (A j) (List.ofFn A).prod := by
        refine Commute.list_prod_right _ _ fun l hl => ?_
        obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hl
        exact hAA j i
      calc (List.ofFn A).prod (A j v) = ((List.ofFn A).prod * A j) v := rfl
        _ = (A j * (List.ofFn A).prod) v := by rw [hc.eq]
        _ = A j ((List.ofFn A).prod v) := rfl
        _ = ((y : ℂ) ^ (m + 1)) • A j v := by rw [h3, map_smul]
  have hJinv : ∀ j, ∀ v ∈ J, A j v ∈ J := by
    intro j v hv
    rw [((memJ v).1 hv).2 j]
    exact J.smul_mem _ hv
  set T : H →L[ℂ] H := S ∘L (U : H →L[ℂ] H) with hTdef
  have hTrel : ∀ j, j ≠ i₀ → ∀ v, A j (T v) = T (A (j + 1) v) := by
    intro j hj v
    show A j (S (U v)) = S (U (A (j + 1) v))
    rw [hS.U_A, hSA j hj]
  have cmpA : ∀ j (z : Z), ((cmp Z (A j) z : Z) : H) = A j z := fun j z => by
    rw [cmp_coe, Submodule.starProjection_eq_self_iff]
    exact hZinv j z z.2
  have hPJ : ∀ v, J.starProjection (Z.starProjection v) = J.starProjection v := fun v => by
    have := Submodule.starProjection_comp_starProjection_of_le hJZ
    exact congrArg (fun X : H →L[ℂ] H => X v) this
  have hZJ : ∀ v, Z.starProjection (J.starProjection v) = J.starProjection v := fun v =>
    Submodule.starProjection_eq_self_iff.2 (hJZ (by simp))
  have hsymZ : ∀ j, LinearMap.IsSymmetric (cmp Z (A j)) := fun j x z => by
    rw [Submodule.coe_inner, Submodule.coe_inner, cmpA, cmpA, hsa]
  have cmpQ : ∀ z : Z, ((cmp Z J.starProjection z : Z) : H) = J.starProjection z := fun z => by
    rw [cmp_coe, hZJ]
  have hQQ : cmp Z J.starProjection * cmp Z J.starProjection = cmp Z J.starProjection := by
    ext z
    show ((cmp Z J.starProjection (cmp Z J.starProjection z) : Z) : H) =
      (cmp Z J.starProjection z : Z)
    rw [cmpQ, cmpQ]
    exact Submodule.starProjection_eq_self_iff.2 (by simp)
  have hcut := trace_cut (Finset.univ.erase i₀) (fun j => cmp Z (A j)) (fun j => cmp Z (A (j + 1)))
    (cmp Z T) (cmp Z J.starProjection)
    (by
      intro j hj
      ext z
      have hj' := Finset.ne_of_mem_erase hj
      show ((cmp Z (A j) (cmp Z T z) : Z) : H) = (cmp Z T (cmp Z (A (j + 1)) z) : Z)
      rw [cmpA, cmp_coe, cmp_coe, cmpA, ← hTrel j hj' z,
        proj_comm Z (A j) (hsa j) (hZinv j)])
    (by
      intro j _ i _
      ext z
      show ((cmp Z (A j) (cmp Z (A i) z) : Z) : H) = (cmp Z (A i) (cmp Z (A j) z) : Z)
      rw [cmpA, cmpA, cmpA, cmpA]
      exact hS.A_A j i z)
    (by
      intro j _ i _
      ext z
      show ((cmp Z (A j) (cmp Z (A (i + 1)) z) : Z) : H) = (cmp Z (A (i + 1)) (cmp Z (A j) z) : Z)
      rw [cmpA, cmpA, cmpA, cmpA]
      exact hS.A_A j (i + 1) z)
    (by
      intro j _
      ext z
      show ((cmp Z (A j) (cmp Z J.starProjection z) : Z) : H) =
        (cmp Z J.starProjection (cmp Z (A j) z) : Z)
      rw [cmpA, cmpQ, cmpQ, cmpA, proj_comm J (A j) (hsa j) (hJinv j)])
    (fun j _ => hsymZ j) (fun j _ => hsymZ (j + 1))
    (by
      intro x z
      rw [Submodule.coe_inner, Submodule.coe_inner, cmpQ, cmpQ]
      exact Submodule.inner_starProjection_left_eq_right _ _ _)
    hQQ
    (by
      intro j _
      ext z
      show ((cmp Z J.starProjection ((cmp Z (A j) - cmp Z (A (j + 1))) z) : Z) : H) = 0
      rw [cmpQ, LinearMap.sub_apply, Submodule.coe_sub, cmpA, cmpA, map_sub,
        proj_comm J (A j) (hsa j) (hJinv j), proj_comm J (A (j + 1)) (hsa _) (hJinv _)]
      have hm : J.starProjection (z : H) ∈ J := by simp
      rw [((memJ _).1 hm).2 j, ((memJ _).1 hm).2 (j + 1), sub_self])
    (by
      intro z hz
      have hz' : ∀ j, j ≠ i₀ → A j z = A (j + 1) z := by
        intro j hj
        have := congrArg (fun w : Z => (w : H)) (hz j (Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩))
        simpa only [cmpA] using this
      have hconst := cycle_const (fun j => A j (z : H)) i₀ hz'
      obtain ⟨h1, h3⟩ := (memZ z).1 z.2
      have hpow := list_prod_apply (A (i₀ + 1)) z (List.ofFn A) (by
        intro l hl
        obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hl
        exact ⟨hAA _ _, hconst i⟩)
      rw [List.length_ofFn, h3] at hpow
      have hroot := pow_root (A (i₀ + 1)) (hsa _) (hpos _) hy m z hpow.symm
      have hzJ : (z : H) ∈ J := (memJ z).2 ⟨h1, fun i => (hconst i).trans hroot⟩
      ext
      rw [cmpQ]
      exact Submodule.starProjection_eq_self_iff.2 hzJ)
  rw [trOn_fd Z T, hcut]
  have h1 : trOn J T = trOn Z (J.starProjection ∘L T ∘L J.starProjection) := by
    unfold trOn
    rw [prj_fd, prj_fd]
    congr 1
    ext v
    simp only [ContinuousLinearMap.comp_apply]
    rw [hZJ, hPJ]
  have h2 : cmp Z (J.starProjection ∘L T ∘L J.starProjection) =
      cmp Z J.starProjection * cmp Z T * cmp Z J.starProjection := by
    ext z
    show Z.starProjection (J.starProjection (T (J.starProjection z))) =
      ((cmp Z J.starProjection (cmp Z T (cmp Z J.starProjection z)) : Z) : H)
    rw [cmpQ, cmp_coe, cmpQ, hPJ, hZJ]
  rw [h1, trOn_fd Z, h2, LinearMap.trace_mul_comm ℂ (cmp Z J.starProjection * cmp Z T),
    ← mul_assoc, hQQ, LinearMap.trace_mul_comm ℂ (cmp Z T)]
