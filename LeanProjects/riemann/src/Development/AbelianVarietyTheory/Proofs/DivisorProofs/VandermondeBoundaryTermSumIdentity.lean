import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

namespace GlobalTheory.VdmCoef

theorem polar_zero {Z S I : Type} [Fintype Z] [Fintype I] (n : I → Z → ℝ) (v : S → Z → ℝ) (T : Finset S) :
    ∀ c : I → ℝ, (∀ x : Z → ℝ, ∑ j, c j * (∑ z, n j z * x z) ^ T.card = 0) →
      ∑ j, c j * ∏ s ∈ T, ∑ z, n j z * v s z = 0 := by
  induction T using Finset.induction_on with
  | empty => intro c h; simpa using h 0
  | insert s T hs ih =>
    intro c h
    have key := ih (fun j => c j * ∑ z, n j z * v s z) fun x => by
      have hd : HasDerivAt (fun t : ℝ => ∑ j, c j * ((∑ z, n j z * x z) + t * ∑ z, n j z * v s z) ^ (T.card + 1))
          (∑ j, c j * (((T.card + 1 : ℕ) : ℝ) * ((∑ z, n j z * x z) + 0 * ∑ z, n j z * v s z) ^ (T.card + 1 - 1) *
            (1 * ∑ z, n j z * v s z))) 0 :=
        HasDerivAt.fun_sum fun j _ =>
          ((((hasDerivAt_id' (0 : ℝ)).mul_const _).const_add _).fun_pow _).const_mul _
      have h0 : (fun t : ℝ => ∑ j, c j * ((∑ z, n j z * x z) + t * ∑ z, n j z * v s z) ^ (T.card + 1)) =
          fun _ => 0 := by
        funext t
        have := h (fun z => x z + t * v s z)
        rw [Finset.card_insert_of_notMem hs] at this
        rw [← this]
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 2
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun z _ => by ring
      rw [h0] at hd
      have e := hd.unique (hasDerivAt_const _ _)
      have hne : ((T.card + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      refine mul_left_cancel₀ hne ?_
      rw [mul_zero, ← e, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Nat.add_sub_cancel, zero_mul, add_zero]
      ring
    rw [← key]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.prod_insert hs, mul_assoc]

theorem polar {Z S I J : Type} [Fintype Z] [Fintype I] [Fintype J] (c : I → ℝ) (n : I → Z → ℝ) (c' : J → ℝ)
    (n' : J → Z → ℝ) (v : S → Z → ℝ) (T : Finset S)
    (h : ∀ x : Z → ℝ, ∑ j, c j * (∑ z, n j z * x z) ^ T.card = ∑ j, c' j * (∑ z, n' j z * x z) ^ T.card) :
    ∑ j, c j * ∏ s ∈ T, ∑ z, n j z * v s z = ∑ j, c' j * ∏ s ∈ T, ∑ z, n' j z * v s z := by
  have := polar_zero (Sum.elim n n') v T (Sum.elim c fun j => -c' j) fun x => by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib]
    rw [h x, add_neg_cancel]
  rw [Fintype.sum_sum_type] at this
  simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib] at this
  exact sub_eq_zero.1 (by rw [sub_eq_add_neg]; exact this)

@[to_additive  ]
theorem prod_low {M : Type} [CommMonoid M] {m : ℕ} (f : Fin m → Fin m → M) :
    ∏ s : Low m, f s.1.1 s.1.2 = ∏ i, ∏ j ∈ Finset.Ioi i, f j i := by
  rw [← Finset.prod_subtype (Finset.univ.filter fun s : Fin m × Fin m => s.2 < s.1) (by simp) (fun s => f s.1 s.2),
    Finset.prod_filter, Fintype.prod_prod_type_right]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_filter]
  congr 1
  ext
  simp

theorem sum_roots {m : ℕ} (θ : Fin m → ℝ) :
    ∑ s : Low m, (θ s.1.1 - θ s.1.2) = -∑ i : Fin m, ((m : ℝ) - 1 - 2 * (i : ℕ)) * θ i := by
  rw [sum_low fun j i => θ j - θ i]
  simp only [Finset.sum_sub_distrib]
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun j => Finset.Iio j) (by simp), ← Finset.sum_sub_distrib,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_const, Finset.sum_const, Fin.card_Ioi, Fin.card_Iio, nsmul_eq_mul, nsmul_eq_mul]
  have hi := i.isLt
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

variable {ι : Type} [Fintype ι] {r : ι → ℕ}

def root (x : (Σ a, Fin (r a)) → ℝ) (t : Σ a, Low (r a)) : ℝ := x ⟨t.1, t.2.1.1⟩ - x ⟨t.1, t.2.1.2⟩

theorem prod_root (x : (Σ a, Fin (r a)) → ℝ) :
    ∏ t, root x t = ∏ a, ∏ i : Fin (r a), ∏ j ∈ Finset.Ioi i, (x ⟨a, j⟩ - x ⟨a, i⟩) := by
  rw [Fintype.prod_sigma]
  exact Finset.prod_congr rfl fun a _ => prod_low fun j i => x ⟨a, j⟩ - x ⟨a, i⟩

theorem eval_vdm (x : (Σ a, Fin (r a)) → ℝ) : MvPolynomial.eval x (vdm r) = ∏ t, root x t := by
  simp [prod_root, vdm]

def refl (t : Σ a, Low (r a)) : Equiv.Perm (Σ a, Fin (r a)) := Equiv.swap ⟨t.1, t.2.1.1⟩ ⟨t.1, t.2.1.2⟩

omit [Fintype ι] in

theorem pos_ne (t : Σ a, Low (r a)) : (⟨t.1, t.2.1.1⟩ : Σ a, Fin (r a)) ≠ ⟨t.1, t.2.1.2⟩ := fun h =>
  t.2.2.ne' (eq_of_heq (Sigma.mk.inj_iff.1 h).2)

theorem prod_root_refl (x : (Σ a, Fin (r a)) → ℝ) (t : Σ a, Low (r a)) :
    ∏ t', root (fun z => x (refl t z)) t' = -∏ t', root x t' := by
  rw [prod_root, prod_root, ← Finset.mul_prod_erase _ _ (Finset.mem_univ t.1),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ t.1), ← neg_mul]
  congr 1
  · rw [← det_vandermonde fun i => x (refl t ⟨t.1, i⟩), ← det_vandermonde fun i => x ⟨t.1, i⟩]
    have e : (vandermonde fun i => x (refl t ⟨t.1, i⟩)) =
        (vandermonde fun i => x ⟨t.1, i⟩).submatrix (Equiv.swap t.2.1.1 t.2.1.2) id := by
      ext i j
      rw [submatrix_apply, vandermonde_apply, vandermonde_apply, refl, sigma_mk_injective.swap_apply]
      rfl
    rw [e, det_permute, Equiv.Perm.sign_swap t.2.2.ne']
    simp
  · refine Finset.prod_congr rfl fun b hb => ?_
    have e (i : Fin (r b)) : refl t ⟨b, i⟩ = ⟨b, i⟩ :=
      Equiv.swap_apply_of_ne_of_ne (fun h => Finset.ne_of_mem_erase hb (congrArg Sigma.fst h))
        fun h => Finset.ne_of_mem_erase hb (congrArg Sigma.fst h)
    simp only [e]

theorem prod_erase_root_refl (x : (Σ a, Fin (r a)) → ℝ) (t : Σ a, Low (r a)) :
    ∏ t' ∈ Finset.univ.erase t, root (fun z => x (refl t z)) t' = ∏ t' ∈ Finset.univ.erase t, root x t' := by
  by_cases h : root x t = 0
  · have e : (fun z => x (refl t z)) = x := funext fun z => Equiv.apply_swap_eq_self (sub_eq_zero.1 h) z
    rw [e]
  · have e := prod_root_refl x t
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ t), ← Finset.mul_prod_erase _ _ (Finset.mem_univ t)] at e
    have e' : root (fun z => x (refl t z)) t = -root x t := by simp [root, refl]
    rw [e', neg_mul] at e
    exact mul_left_cancel₀ h (neg_injective e)

theorem pair_sub_refl (x θ : (Σ a, Fin (r a)) → ℝ) (t : Σ a, Low (r a)) :
    ∑ z, x z * θ z - ∑ z, x (refl t z) * θ z = root θ t * root x t := by
  rw [← Finset.sum_sub_distrib, Fintype.sum_eq_add _ _ (pos_ne t) fun z hz => by
    rw [refl, Equiv.swap_apply_of_ne_of_ne hz.1 hz.2, sub_self]]
  simp only [refl, root, Equiv.swap_apply_left, Equiv.swap_apply_right]
  ring

theorem pair_rootDiag (x θ : (Σ a, Fin (r a)) → ℝ) (t : Σ a, Low (r a)) :
    ∑ z, x z * rootDiag θ z (some t) = root x t := by
  simp [rootDiag, root, mul_sub, Finset.sum_sub_distrib]

theorem prod_erase_some (x θ : (Σ a, Fin (r a)) → ℝ) (t : Σ a, Low (r a)) :
    ∏ s ∈ Finset.univ.erase (some t), ∑ z, x z * rootDiag θ z s =
      (∑ z, x z * θ z) * ∏ t' ∈ Finset.univ.erase t, root x t' := by
  have e : (Finset.univ.erase (some t) : Finset (Option (Σ a, Low (r a)))) =
      Finset.insertNone (Finset.univ.erase t) := by
    ext s
    cases s <;> simp
  rw [e, Finset.prod_insertNone]
  simp only [pair_rootDiag]
  rfl

variable {I : Type} [Fintype I] {c : I → ℝ} {n : I → (Σ a, Fin (r a)) → ℝ}

theorem coef_root (h : ∀ x : (Σ a, Fin (r a)) → ℝ,
      ∑ j, c j * (∑ z, n j z * x z) ^ Fintype.card (Σ a, Low (r a)) = ∏ t, root x t)
    (θ : (Σ a, Fin (r a)) → ℝ) (t : Σ a, Low (r a)) :
    ∑ j, c j * ∏ s ∈ Finset.univ.erase (some t), ∑ z, n j z * rootDiag θ z s =
      root θ t * (∑ j, c j * ∏ t', root (n j) t') / 2 := by
  have hc : (Finset.univ.erase (some t) : Finset (Option (Σ a, Low (r a)))).card = Fintype.card (Σ a, Low (r a)) := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_option, Nat.add_sub_cancel]
  have e := polar c n (fun j => -c j) (fun j z => n j (refl t z)) (fun s z => rootDiag θ z s)
    (Finset.univ.erase (some t)) fun x => by
      have e₁ (j : I) : ∑ z, n j (refl t z) * x z = ∑ z, n j z * x (refl t z) := by
        rw [← Equiv.sum_comp (refl t)]
        simp [refl]
      simp only [hc, e₁, neg_mul, Finset.sum_neg_distrib]
      rw [h, h, prod_root_refl, neg_neg]
  simp only [prod_erase_some, prod_erase_root_refl, neg_mul, Finset.sum_neg_distrib] at e ⊢
  rw [eq_div_iff two_ne_zero, mul_two]
  nth_rewrite 2 [e]
  rw [← sub_eq_add_neg, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_sub, ← sub_mul, pair_sub_refl, ← Finset.mul_prod_erase _ _ (Finset.mem_univ t)]
  ring

theorem eval_rep (h : ∑ j, c j • lin (n j) ^ Fintype.card (Σ a, Low (r a)) = vdm r) (x : (Σ a, Fin (r a)) → ℝ) :
    ∑ j, c j * (∑ z, n j z * x z) ^ Fintype.card (Σ a, Low (r a)) = ∏ t, root x t := by
  rw [← eval_vdm, ← h]
  simp [lin, MvPolynomial.smul_eval]

theorem total_eq {J : Type} [Fintype J] {c' : J → ℝ} {n' : J → (Σ a, Fin (r a)) → ℝ}
    (h : ∑ j, c j • lin (n j) ^ Fintype.card (Σ a, Low (r a)) = vdm r)
    (h' : ∑ j, c' j • lin (n' j) ^ Fintype.card (Σ a, Low (r a)) = vdm r) :
    ∑ j, c j * ∏ t, root (n j) t = ∑ j, c' j * ∏ t, root (n' j) t := by
  have e := polar c n c' n' (fun t z => rootDiag 0 z (some t)) Finset.univ fun x => by
    rw [Finset.card_univ, eval_rep h, eval_rep h']
  simpa only [pair_rootDiag] using e

theorem coef_block (a : ι) (h : ∑ j, c j • lin (n j) ^ Fintype.card (Σ a, Low (r a)) = vdm r)
    (θ : (Σ a, Fin (r a)) → ℝ) :
    ∑ j, c j * ((Fintype.card (Σ a, Low (r a))).factorial * ∑ s : Option (Σ a, Low (r a)),
      bcDiag a s * ∏ s' ∈ Finset.univ.erase s, ∑ x, n j x * rootDiag θ x s') =
      -((Fintype.card (Σ a, Low (r a))).factorial * (∑ j, c j * ∏ t, root (n j) t) / 2) *
        ∑ i : Fin (r a), ((r a : ℝ) - 1 - 2 * (i : ℕ)) * θ ⟨a, i⟩ := by
  have e₁ : ∑ j, c j * ((Fintype.card (Σ a, Low (r a))).factorial * ∑ s : Option (Σ a, Low (r a)),
      bcDiag a s * ∏ s' ∈ Finset.univ.erase s, ∑ x, n j x * rootDiag θ x s') =
      (Fintype.card (Σ a, Low (r a))).factorial * ∑ s : Option (Σ a, Low (r a)),
      bcDiag a s * ∑ j, c j * ∏ s' ∈ Finset.univ.erase s, ∑ x, n j x * rootDiag θ x s' := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have e₂ : ∑ t : Σ a, Low (r a), bcDiag a (some t) * root θ t = ∑ s : Low (r a), root θ ⟨a, s⟩ := by
    rw [Fintype.sum_sigma, Finset.sum_eq_single a (fun b _ hb => by simp [bcDiag, hb]) (by simp)]
    simp [bcDiag]
  rw [e₁, Fintype.sum_option]
  simp only [coef_root (eval_rep h)]
  rw [neg_mul, ← mul_neg, ← sum_roots fun i => θ ⟨a, i⟩]
  have e₃ : bcDiag a (none : Option (Σ a, Low (r a))) = 0 := rfl
  rw [e₃, zero_mul, zero_add]
  change _ = _ * ∑ s : Low (r a), root θ ⟨a, s⟩
  rw [← e₂, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem bc_vdm_coef : ∀ (ι : Type) [Fintype ι] (r : ι → ℕ) (a : ι), ∃ κ : ℝ, ∀ (I : Type) [Fintype I] (c : I → ℝ) (n : I → (Σ a, Fin (r a)) → ℤ), ∑ j, c j • lin (fun x => (n j x : ℝ)) ^ Fintype.card (Σ a, Low (r a)) = vdm r → ∀ θ : (Σ a, Fin (r a)) → ℝ, ∑ j, c j * ((Fintype.card (Σ a, Low (r a))).factorial * ∑ s : Option (Σ a, Low (r a)), bcDiag a s * ∏ s' ∈ Finset.univ.erase s, ∑ x, (n j x : ℝ) * rootDiag θ x s') = κ * ∑ i : Fin (r a), ((r a : ℝ) - 1 - 2 * (i : ℕ)) * θ ⟨a, i⟩ := by
  intro ι _ r a
  by_cases H : ∃ (J : Type) (_ : Fintype J) (c' : J → ℝ) (n' : J → (Σ a, Fin (r a)) → ℝ),
      ∑ j, c' j • lin (n' j) ^ Fintype.card (Σ a, Low (r a)) = vdm r
  · obtain ⟨J, _, c', n', h'⟩ := H
    refine ⟨-((Fintype.card (Σ a, Low (r a))).factorial * (∑ j, c' j * ∏ t, root (n' j) t) / 2),
      fun I _ c n h θ => ?_⟩
    rw [← total_eq h h']
    exact coef_block a h θ
  · exact ⟨0, fun I _ c n h => (H ⟨I, _, c, _, h⟩).elim⟩

end GlobalTheory.VdmCoef
