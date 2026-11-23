import Mathlib

noncomputable section

open Polynomial

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra

section Ker

variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem common_ker (L : List (Module.End ℂ M)) (hL : ∀ N ∈ L, IsNilpotent N)
    (hc : ∀ N ∈ L, ∀ N' ∈ L, Commute N N') (Q : Submodule ℂ M) (hQ : Q ≠ ⊥)
    (hQL : ∀ N ∈ L, ∀ y ∈ Q, N y ∈ Q) : ∃ y ∈ Q, y ≠ 0 ∧ ∀ N ∈ L, N y = 0 := by
  induction L generalizing Q with
  | nil =>
    obtain ⟨y, hy, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ
    exact ⟨y, hy, h0, by simp⟩
  | cons N L ih =>
    classical
    obtain ⟨y, hy, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ
    obtain ⟨n, hn⟩ := hL N List.mem_cons_self
    have hex : ∃ k, (N ^ k) y = 0 := ⟨n, by rw [hn]; rfl⟩
    set k := Nat.find hex with hk
    have hk0 : k ≠ 0 := by
      intro h
      have h1 := Nat.find_spec hex
      rw [← hk, h, pow_zero, Module.End.one_apply] at h1
      exact h0 h1
    have hpowQ : ∀ j, (N ^ j) y ∈ Q := by
      intro j
      induction j with
      | zero => simpa using hy
      | succ j ihj =>
        rw [pow_succ', Module.End.mul_apply]
        exact hQL N List.mem_cons_self _ ihj
    have hy1 : (N ^ (k - 1)) y ≠ 0 := Nat.find_min hex (by omega)
    have hNy1 : N ((N ^ (k - 1)) y) = 0 := by
      rw [← Module.End.mul_apply, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)]
      exact Nat.find_spec hex
    set Q' := Q ⊓ LinearMap.ker N with hQ'
    have hQ'0 : Q' ≠ ⊥ := by
      intro h
      have hm : (N ^ (k - 1)) y ∈ Q' := ⟨hpowQ _, hNy1⟩
      rw [h] at hm
      exact hy1 ((Submodule.mem_bot ℂ).1 hm)
    have hLQ' : ∀ N' ∈ L, ∀ z ∈ Q', N' z ∈ Q' := by
      intro N' hN' z hz
      refine ⟨hQL N' (List.mem_cons_of_mem _ hN') z hz.1, ?_⟩
      change N (N' z) = 0
      rw [← Module.End.mul_apply, (hc N List.mem_cons_self N' (List.mem_cons_of_mem _ hN')).eq,
        Module.End.mul_apply]
      have : N z = 0 := hz.2
      rw [this, map_zero]
    obtain ⟨z, hz, hz0, hzL⟩ := ih (fun N' hN' => hL N' (List.mem_cons_of_mem _ hN'))
      (fun N' hN' N'' hN'' => hc N' (List.mem_cons_of_mem _ hN') N'' (List.mem_cons_of_mem _ hN'')) Q' hQ'0 hLQ'
    refine ⟨z, hz.1, hz0, fun N' hN' => ?_⟩
    rcases List.mem_cons.1 hN' with rfl | h
    · exact hz.2
    · exact hzL N' h

end Ker

section Poly

variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem poly_eq (n : ℕ) (a : ℕ → Module.End ℂ M) (ha : a n = 1) (σ : Multiset ℂ) (hσ : σ.Nodup)
    (hc : Multiset.card σ = n) (h : ∀ x ∈ σ, (∑ k ∈ Finset.range (n + 1), (-x) ^ k • a k) = 0) (u : ℂ) :
    (∑ k ∈ Finset.range (n + 1), u ^ k • a k) = (σ.map (u + ·)).prod • (1 : Module.End ℂ M) := by
  classical
  set P : ℂ[X] := (σ.map fun x => X + C x).prod with hP
  have hPm : P.Monic := monic_multiset_prod_of_monic _ _ fun x _ => monic_X_add_C x
  have hPd : P.natDegree = n := by
    rw [hP, natDegree_multiset_prod_of_monic _ fun x hx => by
      obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1 hx; exact monic_X_add_C y]
    simp [hc]
  have hPe : ∀ w : ℂ, P.eval w = (σ.map (w + ·)).prod := fun w => by
    simp [hP, eval_multiset_prod, Multiset.map_map]
  have hPsum : ∀ w : ℂ, P.eval w = ∑ k ∈ Finset.range (n + 1), P.coeff k * w ^ k := fun w => by
    rw [eval_eq_sum_range, hPd]
  have hPn : P.coeff n = 1 := by rw [← hPd]; exact hPm.coeff_natDegree
  refine LinearMap.ext fun y => ?_
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun f => ?_
  set g : ℂ[X] := ∑ i : Fin n, C (f (a i y) - f y * P.coeff i) * X ^ (i : ℕ) with hg
  have hge : ∀ w : ℂ, g.eval w = f ((∑ k ∈ Finset.range (n + 1), w ^ k • a k) y) - f y * P.eval w := by
    intro w
    rw [hPsum, hg, eval_finsetSum, Finset.sum_range_succ, Finset.sum_range_succ, hPn, ha,
      LinearMap.add_apply, map_add, LinearMap.sum_apply, map_sum, ← Fin.sum_univ_eq_sum_range (fun k => f ((w ^ k • a k) y)),
      ← Fin.sum_univ_eq_sum_range (fun k => P.coeff k * w ^ k)]
    simp only [eval_mul, eval_C, eval_pow, eval_X, LinearMap.smul_apply, map_smul, smul_eq_mul, Module.End.one_apply,
      mul_add, Finset.mul_sum]
    simp only [sub_mul, Finset.sum_sub_distrib, one_mul]
    have h1 : ∑ x : Fin n, f (a x y) * w ^ (x : ℕ) = ∑ x : Fin n, w ^ (x : ℕ) * f (a x y) :=
      Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have h2 : ∑ x : Fin n, f y * P.coeff x * w ^ (x : ℕ) = ∑ i : Fin n, f y * (P.coeff i * w ^ (i : ℕ)) :=
      Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _
    rw [h1, h2]
    ring
  have hg0 : g = 0 := by
    by_contra hne
    have hdeg : g.natDegree < n := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        exact absurd (by simp [hg]) hne
      · rw [natDegree_lt_iff_degree_lt hne]
        exact degree_sum_fin_lt _
    refine hne (eq_zero_of_natDegree_lt_card_of_eval_eq_zero' g (σ.map Neg.neg).toFinset (fun w hw => ?_) ?_)
    · obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_toFinset.1 hw)
      rw [hge, h x hx, LinearMap.zero_apply, map_zero, hPe]
      have : (σ.map (-x + ·)).prod = 0 := Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨x, hx, by ring⟩)
      rw [this, mul_zero, sub_zero]
    · rw [Multiset.toFinset_card_of_nodup (hσ.map neg_injective), Multiset.card_map, hc]
      exact hdeg
  have := hge u
  rw [hg0, eval_zero, hPe] at this
  rw [map_sub, LinearMap.smul_apply, Module.End.one_apply, map_smul, smul_eq_mul]
  linear_combination -this

theorem isUnit_poly (n : ℕ) (a : ℕ → Module.End ℂ M) (χ : ℕ → ℂ) (hcomm : ∀ k l, Commute (a k) (a l))
    (hnil : ∀ k, IsNilpotent (a k - χ k • 1)) (w : ℂ) (hw : (∑ k ∈ Finset.range (n + 1), w ^ k * χ k) ≠ 0) :
    IsUnit (∑ k ∈ Finset.range (n + 1), w ^ k • a k) := by
  set c := ∑ k ∈ Finset.range (n + 1), w ^ k * χ k with hc
  set N := ∑ k ∈ Finset.range (n + 1), w ^ k • (a k - χ k • 1) with hN
  have hNn : IsNilpotent N := by
    refine Commute.isNilpotent_sum (fun k _ => (hnil k).smul _) fun i j _ _ => ?_
    refine ((((hcomm i j).sub_right (Commute.smul_right (Commute.one_right _) _)).sub_left
      (Commute.smul_left (Commute.one_left _) _))).smul_left _ |>.smul_right _
  have e : (∑ k ∈ Finset.range (n + 1), w ^ k • a k) = algebraMap ℂ _ c * (1 + c⁻¹ • N) := by
    rw [mul_add, mul_one, ← Algebra.smul_def, smul_smul, mul_inv_cancel₀ hw, one_smul, hN, hc, Algebra.algebraMap_eq_smul_one,
      Finset.sum_smul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_sub, smul_smul, mul_comm, add_sub_cancel]
  rw [e]
  exact ((Units.mk0 c hw).isUnit.map (algebraMap ℂ (Module.End ℂ M))).mul (IsNilpotent.isUnit_one_add (hNn.smul _))

end Poly

section Piece

variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem comm_sub {x y : Module.End ℂ M} (h : Commute x y) (c d : ℂ) : Commute (x - c • 1) (y - d • 1) :=
  ((h.sub_right (Commute.smul_right (Commute.one_right _) _)).sub_left
    ((Commute.smul_left (Commute.one_left _) _).sub_right (Commute.smul_right (Commute.one_right _) _)))

theorem apply_eig (n : ℕ) (a : ℕ → Module.End ℂ M) (χ : ℕ → ℂ) (y : M)
    (hy : ∀ k ∈ Finset.range (n + 1), a k y = χ k • y) (u : ℂ) :
    (∑ k ∈ Finset.range (n + 1), u ^ k • a k) y = (∑ k ∈ Finset.range (n + 1), u ^ k * χ k) • y := by
  rw [LinearMap.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [LinearMap.smul_apply, hy k hk, smul_smul]

def spoly (n : ℕ) (χ : ℕ → ℂ) : ℂ[X] := X ^ n + ∑ i : Fin n, C (χ i) * X ^ (i : ℕ)

theorem spoly_monic (n : ℕ) (χ : ℕ → ℂ) : (spoly n χ).Monic :=
  monic_X_pow_add (degree_sum_fin_lt _)

theorem spoly_natDegree (n : ℕ) (χ : ℕ → ℂ) : (spoly n χ).natDegree = n := by
  rw [spoly, natDegree_add_eq_left_of_degree_lt]
  · simp
  · exact (degree_sum_fin_lt _).trans_eq (by simp)

theorem spoly_eval (n : ℕ) (χ : ℕ → ℂ) (h : χ n = 1) (u : ℂ) :
    (spoly n χ).eval u = ∑ k ∈ Finset.range (n + 1), u ^ k * χ k := by
  rw [spoly, eval_add, eval_finsetSum, Finset.sum_range_succ, h, mul_one, add_comm,
    ← Fin.sum_univ_eq_sum_range (fun k => u ^ k * χ k)]
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem piece [Nontrivial M] (r s : ℕ) (a b : ℕ → Module.End ℂ M) (haa : ∀ k l, Commute (a k) (a l))
    (hab : ∀ k l, Commute (a k) (b l)) (hbb : ∀ k l, Commute (b k) (b l))
    (ha : a r = 1) (hb : b s = 1) (m : Multiset ℂ) (hm : m.Nodup)
    (hrel : ∀ u : ℂ, (∑ k ∈ Finset.range (r + 1), u ^ k • a k) * (∑ l ∈ Finset.range (s + 1), u ^ l • b l) =
      (m.map (u + ·)).prod • (1 : Module.End ℂ M))
    (χa χb : ℕ → ℂ) (hna : ∀ k, IsNilpotent (a k - χa k • 1)) (hnb : ∀ l, IsNilpotent (b l - χb l • 1)) :
    ∃ σ : Multiset ℂ, σ ≤ m ∧ Multiset.card σ = r ∧ ∀ u : ℂ,
      (∑ k ∈ Finset.range (r + 1), u ^ k • a k) = (σ.map (u + ·)).prod • 1 ∧
      (∑ l ∈ Finset.range (s + 1), u ^ l • b l) = ((m - σ).map (u + ·)).prod • 1 := by
  classical

  set L : List (Module.End ℂ M) := ((List.range (r + 1)).map fun k => a k - χa k • 1) ++
    (List.range (s + 1)).map fun l => b l - χb l • 1 with hL
  have hLn : ∀ N ∈ L, IsNilpotent N := by
    intro N hN
    rcases List.mem_append.1 hN with h | h
    · obtain ⟨k, -, rfl⟩ := List.mem_map.1 h; exact hna k
    · obtain ⟨l, -, rfl⟩ := List.mem_map.1 h; exact hnb l
  have hLc : ∀ N ∈ L, ∀ N' ∈ L, Commute N N' := by
    intro N hN N' hN'
    rcases List.mem_append.1 hN with h | h <;> rcases List.mem_append.1 hN' with h' | h'
    · obtain ⟨k, -, rfl⟩ := List.mem_map.1 h; obtain ⟨l, -, rfl⟩ := List.mem_map.1 h'
      exact comm_sub (haa k l) _ _
    · obtain ⟨k, -, rfl⟩ := List.mem_map.1 h; obtain ⟨l, -, rfl⟩ := List.mem_map.1 h'
      exact comm_sub (hab k l) _ _
    · obtain ⟨k, -, rfl⟩ := List.mem_map.1 h; obtain ⟨l, -, rfl⟩ := List.mem_map.1 h'
      exact comm_sub (hab l k).symm _ _
    · obtain ⟨k, -, rfl⟩ := List.mem_map.1 h; obtain ⟨l, -, rfl⟩ := List.mem_map.1 h'
      exact comm_sub (hbb k l) _ _
  obtain ⟨y, -, hy0, hyL⟩ := common_ker L hLn hLc ⊤ top_ne_bot (fun _ _ _ _ => Submodule.mem_top)
  have hya : ∀ k ∈ Finset.range (r + 1), a k y = χa k • y := fun k hk => by
    have := hyL _ (List.mem_append_left _ (List.mem_map.2 ⟨k, List.mem_range.2 (Finset.mem_range.1 hk), rfl⟩))
    rwa [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at this
  have hyb : ∀ l ∈ Finset.range (s + 1), b l y = χb l • y := fun l hl => by
    have := hyL _ (List.mem_append_right _ (List.mem_map.2 ⟨l, List.mem_range.2 (Finset.mem_range.1 hl), rfl⟩))
    rwa [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at this
  have hχa : χa r = 1 := by
    have h1 := hya r (Finset.self_mem_range_succ r)
    rw [ha, Module.End.one_apply] at h1
    exact (smul_left_injective ℂ hy0 (h1.symm.trans (one_smul ℂ y).symm))
  have hχb : χb s = 1 := by
    have h1 := hyb s (Finset.self_mem_range_succ s)
    rw [hb, Module.End.one_apply] at h1
    exact (smul_left_injective ℂ hy0 (h1.symm.trans (one_smul ℂ y).symm))

  set pC := spoly r χa with hpC
  set pD := spoly s χb with hpD
  set S : ℂ[X] := (m.map fun x => X - C (-x)).prod with hS
  have hSe : ∀ u, S.eval u = (m.map (u + ·)).prod := fun u => by
    simp [hS, eval_multiset_prod, Multiset.map_map, sub_neg_eq_add]
  have hscal : ∀ u, pC.eval u * pD.eval u = S.eval u := by
    intro u
    have h1 := congrArg (fun T : Module.End ℂ M => T y) (hrel u)
    simp only [Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply] at h1
    rw [apply_eig s b χb y hyb, map_smul, apply_eig r a χa y hya, smul_smul] at h1
    rw [spoly_eval r χa hχa, spoly_eval s χb hχb, hSe, mul_comm]
    exact smul_left_injective ℂ hy0 h1
  have hCD : pC * pD = S := Polynomial.funext fun u => by rw [eval_mul, hscal]
  have hSm : S.Monic := monic_multiset_prod_of_monic _ _ fun x _ => monic_X_sub_C _
  have hS0 : S ≠ 0 := hSm.ne_zero
  have hSr : S.roots = m.map Neg.neg := by
    have e : (m.map fun x => X - C (-x)) = (m.map Neg.neg).map (fun x => X - C x) := by
      rw [Multiset.map_map]; rfl
    rw [hS, e, roots_multiset_prod_X_sub_C]
  have hroots : pC.roots + pD.roots = m.map Neg.neg := by
    rw [← roots_mul (hCD ▸ hS0), hCD, hSr]
  have hnd : (pC.roots + pD.roots).Nodup := hroots ▸ hm.map neg_injective
  have hdisj := (Multiset.nodup_add.1 hnd).2.2
  have hpC0 : pC ≠ 0 := (spoly_monic r χa).ne_zero
  have hpD0 : pD ≠ 0 := (spoly_monic s χb).ne_zero

  set σ := pC.roots.map Neg.neg with hσ
  have hσm : σ ≤ m := by
    have h1 : pC.roots ≤ m.map Neg.neg := hroots ▸ Multiset.le_add_right _ _
    have h2 := Multiset.map_le_map (f := Neg.neg) h1
    rwa [Multiset.map_map, show (Neg.neg ∘ Neg.neg : ℂ → ℂ) = id from funext neg_neg, Multiset.map_id] at h2
  have hσc : Multiset.card σ = r := by
    rw [hσ, Multiset.card_map, IsAlgClosed.card_roots_eq_natDegree, spoly_natDegree]
  have hσn : σ.Nodup := Multiset.nodup_of_le hσm hm
  have hCr : pC.roots = σ.map Neg.neg := by
    rw [hσ, Multiset.map_map, show (Neg.neg ∘ Neg.neg : ℂ → ℂ) = id from funext neg_neg, Multiset.map_id]
  set τ := m - σ with hτ
  have hmστ : m = σ + τ := (add_tsub_cancel_of_le hσm).symm
  have hDr : pD.roots = τ.map Neg.neg := by
    have h1 : pC.roots + pD.roots = pC.roots + τ.map Neg.neg := by
      rw [hroots, hCr, ← Multiset.map_add, ← hmστ]
    exact add_left_cancel h1
  have hτn : τ.Nodup := Multiset.nodup_of_le tsub_le_self hm
  have hmc : Multiset.card m = r + s := by
    have h1 := congrArg natDegree hCD
    rw [natDegree_mul hpC0 hpD0, spoly_natDegree, spoly_natDegree] at h1
    rw [h1, ← IsAlgClosed.card_roots_eq_natDegree, hSr, Multiset.card_map]
  have hτc : Multiset.card τ = s := by
    rw [hτ, Multiset.card_sub hσm, hmc, hσc]; omega

  have hCe : ∀ w, (∑ k ∈ Finset.range (r + 1), w ^ k * χa k) = pC.eval w := fun w => (spoly_eval r χa hχa w).symm
  have hDe : ∀ w, (∑ k ∈ Finset.range (s + 1), w ^ k * χb k) = pD.eval w := fun w => (spoly_eval s χb hχb w).symm
  have hzero : ∀ x ∈ m, (∑ k ∈ Finset.range (r + 1), (-x) ^ k • a k) * (∑ l ∈ Finset.range (s + 1), (-x) ^ l • b l) = 0 := by
    intro x hx
    rw [hrel, Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨x, hx, by ring⟩), zero_smul]
  refine ⟨σ, hσm, hσc, fun u => ⟨?_, ?_⟩⟩
  · refine poly_eq r a ha σ hσn hσc (fun x hx => ?_) u
    have hD : IsUnit (∑ l ∈ Finset.range (s + 1), (-x) ^ l • b l) := by
      refine isUnit_poly s b χb hbb hnb (-x) ?_
      rw [hDe]
      intro h0
      have h1 : -x ∈ pD.roots := (mem_roots hpD0).2 h0
      have h2 : -x ∈ pC.roots := by rw [hCr]; exact Multiset.mem_map.2 ⟨x, hx, rfl⟩
      exact Multiset.disjoint_left.1 hdisj h2 h1
    exact (hD.mul_left_eq_zero).1 (hzero x (Multiset.mem_of_le hσm hx))
  · refine poly_eq s b hb τ hτn hτc (fun x hx => ?_) u
    have hC : IsUnit (∑ k ∈ Finset.range (r + 1), (-x) ^ k • a k) := by
      refine isUnit_poly r a χa haa hna (-x) ?_
      rw [hCe]
      intro h0
      have h1 : -x ∈ pC.roots := (mem_roots hpC0).2 h0
      have h2 : -x ∈ pD.roots := by rw [hDr]; exact Multiset.mem_map.2 ⟨x, hx, rfl⟩
      exact Multiset.disjoint_left.1 hdisj h1 h2
    exact (hC.mul_right_eq_zero).1 (hzero x (Multiset.mem_of_le tsub_le_self hx))

end Piece

section Main

theorem decomp {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [Fintype ι] (r s : ℕ)
    (A B : ι → ℕ → Module.End ℂ V) (m : ι → Multiset ℂ) (W : Submodule ℂ V) [FiniteDimensional ℂ W]
    (hAW : ∀ i k, ∀ w ∈ W, A i k w ∈ W) (hBW : ∀ i k, ∀ w ∈ W, B i k w ∈ W)
    (hAA : ∀ i k j l, ∀ w ∈ W, A i k (A j l w) = A j l (A i k w))
    (hAB : ∀ i k j l, ∀ w ∈ W, A i k (B j l w) = B j l (A i k w))
    (hBB : ∀ i k j l, ∀ w ∈ W, B i k (B j l w) = B j l (B i k w))
    (hA1 : ∀ i, ∀ w ∈ W, A i r w = w) (hB1 : ∀ i, ∀ w ∈ W, B i s w = w)
    (hm : ∀ i, (m i).Nodup) (v : V) (hv : v ∈ W)
    (hrel : ∀ i (u : ℂ), (∑ k ∈ Finset.range (r + 1), u ^ k • A i k) ((∑ l ∈ Finset.range (s + 1), u ^ l • B i l) v) =
      ((m i).map (u + ·)).prod • v) :
    ∃ (S : Finset (ι → Multiset ℂ)) (x : (ι → Multiset ℂ) → V), (∀ σ ∈ S, x σ ∈ W) ∧ v = ∑ σ ∈ S, x σ ∧
      ∀ σ ∈ S, ∀ i, σ i ≤ m i ∧ Multiset.card (σ i) = r ∧ ∀ u : ℂ,
        (∑ k ∈ Finset.range (r + 1), u ^ k • A i k) (x σ) = ((σ i).map (u + ·)).prod • x σ ∧
        (∑ l ∈ Finset.range (s + 1), u ^ l • B i l) (x σ) = ((m i - σ i).map (u + ·)).prod • x σ := by
  classical

  let A' : ι → ℕ → Module.End ℂ W := fun i k => (A i k).restrict (fun w hw => hAW i k w hw)
  let B' : ι → ℕ → Module.End ℂ W := fun i k => (B i k).restrict (fun w hw => hBW i k w hw)
  have cAA : ∀ i k j l, Commute (A' i k) (A' j l) := fun i k j l =>
    LinearMap.ext fun w => Subtype.ext (hAA i k j l w.1 w.2)
  have cAB : ∀ i k j l, Commute (A' i k) (B' j l) := fun i k j l =>
    LinearMap.ext fun w => Subtype.ext (hAB i k j l w.1 w.2)
  have cBB : ∀ i k j l, Commute (B' i k) (B' j l) := fun i k j l =>
    LinearMap.ext fun w => Subtype.ext (hBB i k j l w.1 w.2)
  let Gs : Set (Module.End ℂ W) :=
    Set.range (fun p : ι × ℕ => A' p.1 p.2) ∪ Set.range (fun p : ι × ℕ => B' p.1 p.2)
  have hGs : ∀ x ∈ Gs, ∀ y ∈ Gs, Commute x y := by
    rintro _ (⟨⟨i, k⟩, rfl⟩ | ⟨⟨i, k⟩, rfl⟩) _ (⟨⟨j, l⟩, rfl⟩ | ⟨⟨j, l⟩, rfl⟩)
    · exact cAA i k j l
    · exact cAB i k j l
    · exact (cAB j l i k).symm
    · exact cBB i k j l
  let R := Algebra.adjoin ℂ Gs
  have hRc : ∀ x ∈ R, ∀ y ∈ R, Commute x y := fun x hx y hy =>
    Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy fun b hb =>
      (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx fun c hc => hGs b hb c hc).symm
  have hAR : ∀ i k, A' i k ∈ R := fun i k => Algebra.subset_adjoin (Or.inl ⟨(i, k), rfl⟩)
  have hBR : ∀ i k, B' i k ∈ R := fun i k => Algebra.subset_adjoin (Or.inr ⟨(i, k), rfl⟩)
  let Cop : ι → ℂ → Module.End ℂ W := fun i u => ∑ k ∈ Finset.range (r + 1), u ^ k • A' i k
  let Dop : ι → ℂ → Module.End ℂ W := fun i u => ∑ l ∈ Finset.range (s + 1), u ^ l • B' i l
  have hCR : ∀ i u, Cop i u ∈ R := fun i u => R.sum_mem fun k _ => R.smul_mem (hAR i k) _
  have hDR : ∀ i u, Dop i u ∈ R := fun i u => R.sum_mem fun k _ => R.smul_mem (hBR i k) _
  have hCv : ∀ i u (w : W), ((Cop i u w : W) : V) = (∑ k ∈ Finset.range (r + 1), u ^ k • A i k) w := by
    intro i u w
    simp [Cop, A', LinearMap.sum_apply, Submodule.coe_sum]
  have hDv : ∀ i u (w : W), ((Dop i u w : W) : V) = (∑ l ∈ Finset.range (s + 1), u ^ l • B i l) w := by
    intro i u w
    simp [Dop, B', LinearMap.sum_apply, Submodule.coe_sum]

  let v' : W := ⟨v, hv⟩
  let W' : Submodule ℂ W := (Subalgebra.toSubmodule R).map (LinearMap.applyₗ v')
  have hW'm : ∀ w, w ∈ W' ↔ ∃ a ∈ R, a v' = w := fun w => Submodule.mem_map.trans Iff.rfl
  have hW'inv : ∀ x ∈ R, ∀ w ∈ W', x w ∈ W' := by
    intro x hx w hw
    obtain ⟨a, ha, rfl⟩ := (hW'm w).1 hw
    exact (hW'm _).2 ⟨x * a, R.mul_mem hx ha, rfl⟩
  have hrelv : ∀ i u, Cop i u (Dop i u v') = ((m i).map (u + ·)).prod • v' := fun i u =>
    Subtype.ext (by rw [hCv, hDv]; exact hrel i u)
  have hrelW' : ∀ i u, ∀ w ∈ W', Cop i u (Dop i u w) = ((m i).map (u + ·)).prod • w := by
    intro i u w hw
    obtain ⟨a, ha, rfl⟩ := (hW'm w).1 hw
    have e1 : Dop i u (a v') = a (Dop i u v') := by
      rw [← Module.End.mul_apply, (hRc _ (hDR i u) _ ha).eq, Module.End.mul_apply]
    have e2 : Cop i u (a (Dop i u v')) = a (Cop i u (Dop i u v')) := by
      rw [← Module.End.mul_apply, (hRc _ (hCR i u) _ ha).eq, Module.End.mul_apply]
    rw [e1, e2, hrelv, map_smul]

  let f : (ι × ℕ) ⊕ (ι × ℕ) → Module.End ℂ W' := Sum.elim
    (fun p => (A' p.1 p.2).restrict (fun w hw => hW'inv _ (hAR p.1 p.2) w hw))
    (fun p => (B' p.1 p.2).restrict (fun w hw => hW'inv _ (hBR p.1 p.2) w hw))
  have hfR : ∀ j, ∃ x ∈ R, ∀ w : W', (f j w : W) = x w := by
    rintro (⟨i, k⟩ | ⟨i, k⟩)
    · exact ⟨A' i k, hAR i k, fun w => rfl⟩
    · exact ⟨B' i k, hBR i k, fun w => rfl⟩
  have hfc : ∀ j j', Commute (f j) (f j') := by
    intro j j'
    obtain ⟨x, hx, hxe⟩ := hfR j
    obtain ⟨y, hy, hye⟩ := hfR j'
    refine LinearMap.ext fun w => Subtype.ext ?_
    change (f j (f j' w) : W) = (f j' (f j w) : W)
    rw [hxe, hye, hye, hxe, ← Module.End.mul_apply, (hRc x hx y hy).eq, Module.End.mul_apply]
  have hT := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
    (fun j j' _ => hfc j j') (fun j => Module.End.iSup_maxGenEigenspace_eq_top _)
  let v'' : W' := ⟨v', (hW'm v').2 ⟨1, R.one_mem, rfl⟩⟩
  have hv'' : v'' ∈ ⨆ χ : (ι × ℕ) ⊕ (ι × ℕ) → ℂ, ⨅ j, (f j).maxGenEigenspace (χ j) := by
    rw [hT]; exact Submodule.mem_top
  obtain ⟨Fs, hFs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hv''
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ _).1 hFs
  let P : ((ι × ℕ) ⊕ (ι × ℕ) → ℂ) → Submodule ℂ W' := fun χ => ⨅ j, (f j).maxGenEigenspace (χ j)
  have hPf : ∀ χ j, ∀ x ∈ P χ, f j x ∈ P χ := by
    intro χ j x hx
    simp only [P, Submodule.mem_iInf] at hx ⊢
    intro j'
    exact Module.End.mapsTo_maxGenEigenspace_of_comm (hfc j' j) (χ j') (hx j')
  let xx : ((ι × ℕ) ⊕ (ι × ℕ) → ℂ) → V := fun χ => (((μ χ : W') : W) : V)
  have key : ∀ χ : (ι × ℕ) ⊕ (ι × ℕ) → ℂ, ∃ σ : ι → Multiset ℂ, (μ χ : W') ≠ 0 → ∀ i, σ i ≤ m i ∧
      Multiset.card (σ i) = r ∧ ∀ u : ℂ,
        (∑ k ∈ Finset.range (r + 1), u ^ k • A i k) (xx χ) = ((σ i).map (u + ·)).prod • xx χ ∧
        (∑ l ∈ Finset.range (s + 1), u ^ l • B i l) (xx χ) = ((m i - σ i).map (u + ·)).prod • xx χ := by
    intro χ
    by_cases h0 : (μ χ : W') = 0
    · exact ⟨fun _ => 0, fun h => absurd h0 h⟩
    have hpc : ∀ i, ∃ σi : Multiset ℂ, σi ≤ m i ∧ Multiset.card σi = r ∧ ∀ u : ℂ,
        (∑ k ∈ Finset.range (r + 1), u ^ k • A i k) (xx χ) = (σi.map (u + ·)).prod • xx χ ∧
        (∑ l ∈ Finset.range (s + 1), u ^ l • B i l) (xx χ) = ((m i - σi).map (u + ·)).prod • xx χ := by
      intro i
      have : Nontrivial (P χ) := ⟨⟨μ χ, 0, fun h => h0 (congrArg Subtype.val h)⟩⟩
      let a : ℕ → Module.End ℂ (P χ) := fun k => (f (Sum.inl (i, k))).restrict (hPf χ _)
      let b : ℕ → Module.End ℂ (P χ) := fun l => (f (Sum.inr (i, l))).restrict (hPf χ _)
      have hcr : ∀ j j', Commute ((f j).restrict (hPf χ j)) ((f j').restrict (hPf χ j')) := fun j j' =>
        LinearMap.ext fun w => Subtype.ext (LinearMap.congr_fun (hfc j j').eq w.1)
      have ha : a r = 1 := LinearMap.ext fun w => Subtype.ext (Subtype.ext (Subtype.ext (hA1 i _ w.1.1.2)))
      have hb : b s = 1 := LinearMap.ext fun w => Subtype.ext (Subtype.ext (Subtype.ext (hB1 i _ w.1.1.2)))
      have hval : ∀ u (w : P χ), ((((∑ k ∈ Finset.range (r + 1), u ^ k • a k) w : P χ) : W') : W) = Cop i u w := by
        intro u w
        simp [a, f, Cop, LinearMap.sum_apply, Submodule.coe_sum]
      have hvalD : ∀ u (w : P χ), ((((∑ l ∈ Finset.range (s + 1), u ^ l • b l) w : P χ) : W') : W) = Dop i u w := by
        intro u w
        simp [b, f, Dop, LinearMap.sum_apply, Submodule.coe_sum]
      have hrelP : ∀ u : ℂ, (∑ k ∈ Finset.range (r + 1), u ^ k • a k) * (∑ l ∈ Finset.range (s + 1), u ^ l • b l) =
          ((m i).map (u + ·)).prod • (1 : Module.End ℂ (P χ)) := by
        intro u
        refine LinearMap.ext fun w => Subtype.ext (Subtype.ext ?_)
        rw [Module.End.mul_apply, hval]
        have e : ((((∑ l ∈ Finset.range (s + 1), u ^ l • b l) w : P χ) : W')) =
            ⟨Dop i u w, hW'inv _ (hDR i u) _ w.1.2⟩ := Subtype.ext (hvalD u w)
        rw [e]
        change Cop i u (Dop i u w.1.1) = _
        rw [hrelW' i u _ w.1.2]
        rfl
      have hnil : ∀ j, IsNilpotent ((f j).restrict (hPf χ j) - χ j • 1) := by
        intro j
        have h1 := Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap (f j) (χ j)
        have hp : Set.MapsTo (f j - algebraMap ℂ (Module.End ℂ W') (χ j)) (P χ) (P χ) := fun x hx => by
          simp only [LinearMap.sub_apply, Module.algebraMap_end_apply]
          exact (P χ).sub_mem (hPf χ j x hx) ((P χ).smul_mem _ hx)
        have e : (f j).restrict (hPf χ j) - χ j • 1 = (f j - algebraMap ℂ (Module.End ℂ W') (χ j)).restrict hp := by
          refine LinearMap.ext fun w => Subtype.ext ?_
          rfl
        rw [e]
        exact Module.End.isNilpotent_restrict_of_le (hp := hp) (iInf_le _ j) h1
      obtain ⟨σi, h1, h2, h3⟩ := piece r s a b (fun k l => hcr _ _) (fun k l => hcr _ _) (fun k l => hcr _ _) ha hb
        (m i) (hm i) hrelP (fun k => χ (Sum.inl (i, k))) (fun l => χ (Sum.inr (i, l))) (fun k => hnil _)
        (fun l => hnil _)
      refine ⟨σi, h1, h2, fun u => ⟨?_, ?_⟩⟩
      · have e := congrArg (fun T : Module.End ℂ (P χ) => ((((T (μ χ) : P χ) : W') : W) : V)) (h3 u).1
        rw [hval, hCv] at e
        rw [e]
        rfl
      · have e := congrArg (fun T : Module.End ℂ (P χ) => ((((T (μ χ) : P χ) : W') : W) : V)) (h3 u).2
        rw [hvalD, hDv] at e
        rw [e]
        rfl
    choose σ hσ using hpc
    exact ⟨σ, fun _ i => hσ i⟩
  choose sig hsig using key
  set Fs' := Fs.filter (fun χ => (μ χ : W') ≠ 0) with hFs'
  refine ⟨Fs'.image sig, fun σ => ∑ χ ∈ Fs'.filter (fun χ => sig χ = σ), xx χ, ?_, ?_, ?_⟩
  · intro σ _
    exact W.sum_mem fun χ _ => ((μ χ : W') : W).2
  · rw [Finset.sum_fiberwise_of_maps_to (fun χ hχ => Finset.mem_image_of_mem sig hχ)]
    have e1 : v = (((v'' : W') : W) : V) := rfl
    rw [e1, ← hμ, Submodule.coe_sum, Submodule.coe_sum, hFs', Finset.sum_filter]
    refine Finset.sum_congr rfl fun χ _ => ?_
    split_ifs with h
    · rfl
    · rw [not_not] at h
      simp [h]
  · rintro σ hσ i
    obtain ⟨χ₀, hχ₀, rfl⟩ := Finset.mem_image.1 hσ
    obtain ⟨h1, h2, -⟩ := hsig χ₀ (Finset.mem_filter.1 hχ₀).2 i
    refine ⟨h1, h2, fun u => ⟨?_, ?_⟩⟩
    · rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun χ hχ => ?_
      obtain ⟨hχF, hχe⟩ := Finset.mem_filter.1 hχ
      rw [← hχe]
      exact ((hsig χ (Finset.mem_filter.1 hχF).2 i).2.2 u).1
    · rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun χ hχ => ?_
      obtain ⟨hχF, hχe⟩ := Finset.mem_filter.1 hχ
      rw [← hχe]
      exact ((hsig χ (Finset.mem_filter.1 hχF).2 i).2.2 u).2

end Main

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra

end
