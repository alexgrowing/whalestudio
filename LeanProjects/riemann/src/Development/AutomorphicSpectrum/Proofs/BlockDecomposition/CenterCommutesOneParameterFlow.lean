import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsTestZero
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep.Flow

section Abstract

variable {A : Type} [Ring A] [Algebra ℂ A]

def HD (f f' : ℝ → A) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (p p' : ι → ℝ → ℂ) (C : ι → A),
    (∀ i s, HasDerivAt (p i) (p' i s) s) ∧ (∀ s, f s = ∑ i, p i s • C i) ∧ ∀ s, f' s = ∑ i, p' i s • C i

theorem HD.congr {f f' g g' : ℝ → A} (h : HD f f') (e : ∀ s, g s = f s) (e' : ∀ s, g' s = f' s) : HD g g' := by
  obtain ⟨ι, i, p, p', C, h1, h2, h3⟩ := h
  exact ⟨ι, i, p, p', C, h1, fun s => (e s).trans (h2 s), fun s => (e' s).trans (h3 s)⟩

theorem HD.const (C : A) : HD (fun _ => C) (fun _ => 0) :=
  ⟨Unit, inferInstance, fun _ _ => 1, fun _ _ => 0, fun _ => C, fun _ s => hasDerivAt_const s 1, by simp, by simp⟩

theorem HD.add {f f' g g' : ℝ → A} (h : HD f f') (k : HD g g') :
    HD (fun s => f s + g s) (fun s => f' s + g' s) := by
  obtain ⟨ι, _, p, p', C, h1, h2, h3⟩ := h
  obtain ⟨κ, _, q, q', D, k1, k2, k3⟩ := k
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim p q, Sum.elim p' q', Sum.elim C D, ?_, ?_, ?_⟩
  · rintro (i | j) s
    · exact h1 i s
    · exact k1 j s
  · intro s; simp [h2, k2]
  · intro s; simp [h3, k3]

theorem HD.mul {f f' g g' : ℝ → A} (h : HD f f') (k : HD g g') :
    HD (fun s => f s * g s) (fun s => f' s * g s + f s * g' s) := by
  obtain ⟨ι, _, p, p', C, h1, h2, h3⟩ := h
  obtain ⟨κ, _, q, q', D, k1, k2, k3⟩ := k
  refine ⟨ι × κ, inferInstance, fun x s => p x.1 s * q x.2 s,
    fun x s => p' x.1 s * q x.2 s + p x.1 s * q' x.2 s, fun x => C x.1 * D x.2, ?_, ?_, ?_⟩
  · intro x s; exact (h1 x.1 s).mul (k1 x.2 s)
  · intro s
    simp only [h2, k2, Finset.sum_mul_sum, Fintype.sum_prod_type, smul_mul_smul_comm]
  · intro s
    simp only [h2, h3, k2, k3, Finset.sum_mul_sum, Fintype.sum_prod_type, smul_mul_smul_comm, add_smul,
      Finset.sum_add_distrib]

theorem HD.const_of_zero {f : ℝ → A} (h : HD f (fun _ => 0)) (l : A →ₗ[ℂ] ℂ) (s t : ℝ) : l (f s) = l (f t) := by
  obtain ⟨ι, _, p, p', C, h1, h2, h3⟩ := h
  have hd : ∀ s, HasDerivAt (fun s => l (f s)) 0 s := by
    intro s
    have h4 : HasDerivAt (fun s => ∑ i, p i s * l (C i)) (∑ i, p' i s * l (C i)) s :=
      HasDerivAt.fun_sum fun i _ => (h1 i s).mul_const _
    have e1 : (fun s => l (f s)) = fun s => ∑ i, p i s * l (C i) := by
      funext s; simp [h2, map_sum]
    have e2 : ∑ i, p' i s * l (C i) = 0 := by
      have := congrArg l (h3 s)
      simpa [map_sum] using this.symm
    rw [e1]
    rwa [e2] at h4
  exact is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) s t

theorem hd_adjoin (R Q : ℝ → A) (hRQ : ∀ s, R s * Q s = 1) (hQR : ∀ s, Q s * R s = 1) (L : A) (G : Set A)
    (hG : ∀ B ∈ G, HD (fun s => R s * B * Q s) (fun s => R s * (L * B - B * L) * Q s)) :
    ∀ B ∈ Algebra.adjoin ℂ G, HD (fun s => R s * B * Q s) (fun s => R s * (L * B - B * L) * Q s) := by
  have hmul : ∀ s x y, R s * x * Q s * (R s * y * Q s) = R s * (x * y) * Q s := by
    intro s x y
    calc R s * x * Q s * (R s * y * Q s) = R s * x * (Q s * R s) * y * Q s := by simp only [mul_assoc]
      _ = R s * (x * y) * Q s := by rw [hQR]; simp only [mul_assoc, mul_one]
  intro B hB
  induction hB using Algebra.adjoin_induction with
  | mem x hx => exact hG x hx
  | algebraMap r =>
    refine (HD.const (algebraMap ℂ A r)).congr (fun s => ?_) (fun s => ?_)
    · rw [← Algebra.commutes, mul_assoc, hRQ, mul_one]
    · rw [Algebra.commutes, sub_self]; simp
  | add x y _ _ hx hy =>
    refine (hx.add hy).congr (fun s => ?_) (fun s => ?_)
    · noncomm_ring
    · noncomm_ring
  | mul x y _ _ hx hy =>
    refine (hx.mul hy).congr (fun s => ?_) (fun s => ?_)
    · rw [hmul]
    · rw [hmul, hmul, ← add_mul, ← mul_add]
      congr 2
      noncomm_ring

end Abstract

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem Zalg_le : Zalg E a ≤ Algebra.adjoin ℂ (Set.range (lie E a)) := by
  set S := Algebra.adjoin ℂ (Set.range (lie E a)) with hSdef
  have hL : ∀ X, lie E a X ∈ S := fun X => Algebra.subset_adjoin ⟨X, rfl⟩
  have hS : ∀ i j x, lieS E a i j x ∈ S := fun i j x => by rw [lieS_apply]; exact hL _
  have hE : ∀ (τ : E →+* ℂ) i j, Eop τ i j ∈ S := fun τ i j =>
    S.smul_mem (S.sub_mem (hS _ _ _) (S.smul_mem (hS _ _ _) _)) _
  refine Algebra.adjoin_le ?_
  rintro _ ⟨τ, u, rfl⟩
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (hE _ _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

theorem hd_lie {F F' : ℝ → Lie E a} (h : ∀ s, HasDerivAt F (F' s) s) :
    HD (fun s => lie E a (F s)) (fun s => lie E a (F' s)) := by
  classical
  let b := Module.finBasis ℝ (Lie E a)
  have hsum : ∀ X : Lie E a, lie E a X = ∑ m, ((b.repr X m : ℝ) : ℂ) • lie E a (b m) := by
    intro X
    conv_lhs => rw [← b.sum_repr X]
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_smul]
    exact (algebraMap_smul ℂ _ _).symm
  refine ⟨_, inferInstance, fun m s => ((b.repr (F s) m : ℝ) : ℂ), fun m s => ((b.repr (F' s) m : ℝ) : ℂ),
    fun m => lie E a (b m), fun m s => ?_, fun s => hsum _, fun s => hsum _⟩
  have hl := (LinearMap.toContinuousLinearMap (b.coord m)).hasFDerivAt.comp_hasDerivAt s (h s)
  exact hl.ofReal_comp

theorem hasDerivAt_matMul {u v : ℝ → Lie E a} {u' v' : Lie E a} {s : ℝ} (hu : HasDerivAt u u' s)
    (hv : HasDerivAt v v' s) :
    HasDerivAt (fun t => toL (Matrix.of (u t) * Matrix.of (v t)))
      (toL (Matrix.of u' * Matrix.of (v s) + Matrix.of (u s) * Matrix.of v')) s := by
  rw [hasDerivAt_pi] at hu hv ⊢
  intro i
  rw [hasDerivAt_pi]
  intro j
  have hu' := fun k => (hasDerivAt_pi.1 (hu i)) k
  have hv' := fun k => (hasDerivAt_pi.1 (hv k)) j
  have := HasDerivAt.fun_sum (u := Finset.univ) fun k (_ : k ∈ Finset.univ) => (hu' k).mul (hv' k)
  simpa [Matrix.mul_apply, Finset.sum_add_distrib] using this

theorem zalg_comm_rt_curve : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), (∀ (g : GL (Fin a) (Cinf E)) (X : Lie E a), rt E a (infGL E a g) * lie E a X = lie E a (toL (g.val * Matrix.of X * (g⁻¹).val)) * rt E a (infGL E a g)) → ∀ z : Module.End ℂ (Sm E a), z ∈ Zalg E a → (∀ X : Lie E a, z * lie E a X = lie E a X * z) → ∀ (c : ℝ → GL (Fin a) (Cinf E)) (Y : Lie E a), c 0 = 1 → (∀ s, HasDerivAt (fun t => toL (c t).val) (toL ((c s).val * Matrix.of Y)) s) → (∀ s, HasDerivAt (fun t => toL ((c t)⁻¹).val) (toL (-(Matrix.of Y * ((c s)⁻¹).val))) s) → z * rt E a (infGL E a (c 1)) = rt E a (infGL E a (c 1)) * z := by
  intro E _ _ _ a hconj z hz hcomm c Y h0 hc hci
  let R : ℝ → Module.End ℂ (Sm E a) := fun s => rt E a (infGL E a (c s))
  let Q : ℝ → Module.End ℂ (Sm E a) := fun s => rt E a (infGL E a (c s)⁻¹)
  have hRQ : ∀ s, R s * Q s = 1 := fun s => by
    change rt E a _ * rt E a _ = 1
    rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
  have hQR : ∀ s, Q s * R s = 1 := fun s => by
    change rt E a _ * rt E a _ = 1
    rw [← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
  have hconj' : ∀ s X, R s * lie E a X * Q s =
      lie E a (toL ((c s).val * Matrix.of X * ((c s)⁻¹).val)) := by
    intro s X
    change rt E a (infGL E a (c s)) * lie E a X * Q s = _
    rw [hconj (c s) X, mul_assoc]
    rw [show rt E a (infGL E a (c s)) * Q s = 1 from hRQ s, mul_one]
  have hG : ∀ B ∈ Set.range (lie E a), HD (fun s => R s * B * Q s)
      (fun s => R s * (lie E a Y * B - B * lie E a Y) * Q s) := by
    rintro _ ⟨X, rfl⟩
    let W : Lie E a := toL (Matrix.of Y * Matrix.of X - Matrix.of X * Matrix.of Y)
    have hW : lie E a Y * lie E a X - lie E a X * lie E a Y = lie E a W := by
      rw [lie_comm]
      exact (map_sub (lie E a) _ _).symm
    refine (hd_lie (F := fun s => toL ((c s).val * Matrix.of X * ((c s)⁻¹).val))
      (F' := fun s => toL ((c s).val * Matrix.of W * ((c s)⁻¹).val)) fun s => ?_).congr
      (fun s => hconj' s X) (fun s => by rw [hW]; exact hconj' s W)
    have h1 := hasDerivAt_matMul (hc s) (hasDerivAt_const s X)
    have h2 := hasDerivAt_matMul h1 (hci s)
    refine HasDerivAt.congr_deriv h2 ?_
    change toL (((c s).val * Matrix.of Y * Matrix.of X + (c s).val * 0) * ((c s)⁻¹).val +
      ((c s).val * Matrix.of X) * (-(Matrix.of Y * ((c s)⁻¹).val))) =
      toL ((c s).val * (Matrix.of Y * Matrix.of X - Matrix.of X * Matrix.of Y) * ((c s)⁻¹).val)
    congr 1
    noncomm_ring
  have h := hd_adjoin R Q hRQ hQR (lie E a Y) _ hG z (Zalg_le hz)
  have h' : HD (fun s => R s * z * Q s) (fun _ => 0) :=
    h.congr (fun _ => rfl) fun s => by rw [hcomm Y, sub_self, mul_zero, zero_mul]
  let l : Sm E a → GA E a → (Module.End ℂ (Sm E a) →ₗ[ℂ] ℂ) := fun φ x =>
    { toFun := fun B => (B φ).1 x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have e1 : R 1 * z * Q 1 = R 0 * z * Q 0 :=
    LinearMap.ext fun φ => Subtype.ext <| funext fun x => h'.const_of_zero (l φ x) 1 0
  have hR0 : R 0 = 1 := by
    change rt E a (infGL E a (c 0)) = 1
    rw [h0, map_one, map_one]
  have hQ0 : Q 0 = 1 := by
    change rt E a (infGL E a (c 0)⁻¹) = 1
    rw [h0, inv_one, map_one, map_one]
  rw [hR0, hQ0, one_mul, mul_one] at e1
  change z * R 1 = R 1 * z
  calc z * R 1 = R 1 * z * Q 1 * R 1 := by rw [e1]
    _ = R 1 * z * (Q 1 * R 1) := by simp only [mul_assoc]
    _ = R 1 * z := by rw [hQR, mul_one]

end GlobalTheory.CompanionTheory.SmoothRep.Flow
