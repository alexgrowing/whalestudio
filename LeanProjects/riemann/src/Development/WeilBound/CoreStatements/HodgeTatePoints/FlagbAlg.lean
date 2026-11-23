import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrIsGenAt

noncomputable section

namespace PositivityTheory.HtPt.Flagb

open GlobalTheory.CompanionTheory.Ar

section Glue

variable {A Ω W : Type} [CommRing A] [Field Ω] [Algebra A Ω] [AddCommGroup W] [Module Ω W] [Module A W]
  [IsScalarTower A Ω W]

theorem one_mem_of_max (I : Ideal A) (h : ∀ m : Ideal A, m.IsMaximal → ∃ s ∈ I, s ∉ m) : (1 : A) ∈ I := by
  by_contra h1
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I ((Ideal.ne_top_iff_one I).2 h1)
  obtain ⟨s, hs, hs'⟩ := h m hm
  exact hs' (hle hs)

theorem map_smul_alg (φ : W →ₗ[Ω] Ω) (a : A) (w : W) : φ (a • w) = algebraMap A Ω a * φ w := by
  rw [← algebraMap_smul Ω a w, map_smul, smul_eq_mul]

theorem exists_basis (hinj : Function.Injective (algebraMap A Ω)) (N : Submodule A W) {r : ℕ}
    (φ : Fin r → W →ₗ[Ω] Ω) (t : Fin r → Ω) (ht : ∀ i, t i ≠ 0)
    (hφ : ∀ w ∈ N, (∀ j, φ j w = 0) → w = 0)
    (ha : ∀ m : Ideal A, m.IsMaximal → ∀ i, ∃ s ∉ m, ∃ n ∈ N, (∀ j < i, φ j n = 0) ∧ φ i n = algebraMap A Ω s * t i)
    (hb : ∀ m : Ideal A, m.IsMaximal → ∀ i, ∀ n ∈ N, (∀ j < i, φ j n = 0) →
      ∃ s ∉ m, ∃ a : A, algebraMap A Ω s * φ i n = algebraMap A Ω a * t i) :
    ∃ b : Module.Basis (Fin r) A N, ∀ i, (∀ j < i, φ j (b i) = 0) ∧ φ i (b i) = t i := by
  have h1 : ∀ i, ∃ n ∈ N, (∀ j < i, φ j n = 0) ∧ φ i n = t i := by
    intro i
    let I : Ideal A :=
      { carrier := {s | ∃ n ∈ N, (∀ j < i, φ j n = 0) ∧ φ i n = algebraMap A Ω s * t i}
        add_mem' := by
          rintro a b ⟨n, hn, h0, h⟩ ⟨n', hn', h0', h'⟩
          refine ⟨n + n', N.add_mem hn hn', fun j hj => by rw [map_add, h0 j hj, h0' j hj, add_zero], ?_⟩
          rw [map_add, map_add, h, h', add_mul]
        zero_mem' := ⟨0, N.zero_mem, fun j _ => map_zero _, by simp⟩
        smul_mem' := by
          rintro c a ⟨n, hn, h0, h⟩
          refine ⟨c • n, N.smul_mem c hn, fun j hj => by rw [map_smul_alg, h0 j hj, mul_zero], ?_⟩
          rw [map_smul_alg, h, smul_eq_mul, map_mul, mul_assoc] }
    have := one_mem_of_max I fun m hm => by
      obtain ⟨s, hs, h⟩ := ha m hm i
      exact ⟨s, h, hs⟩
    obtain ⟨n, hn, h0, h⟩ := this
    exact ⟨n, hn, h0, by simpa using h⟩
  have h2 : ∀ i, ∀ n ∈ N, (∀ j < i, φ j n = 0) → ∃ a : A, φ i n = algebraMap A Ω a * t i := by
    intro i n hn h0
    let I : Ideal A :=
      { carrier := {s | ∃ a : A, algebraMap A Ω s * φ i n = algebraMap A Ω a * t i}
        add_mem' := by
          rintro a b ⟨x, h⟩ ⟨y, h'⟩
          exact ⟨x + y, by rw [map_add, map_add, add_mul, add_mul, h, h']⟩
        zero_mem' := ⟨0, by simp⟩
        smul_mem' := by
          rintro c a ⟨x, h⟩
          exact ⟨c * x, by rw [smul_eq_mul, map_mul, map_mul, mul_assoc, h, mul_assoc]⟩ }
    have := one_mem_of_max I fun m hm => by
      obtain ⟨s, hs, h⟩ := hb m hm i n hn h0
      exact ⟨s, h, hs⟩
    obtain ⟨a, h⟩ := this
    exact ⟨a, by simpa using h⟩
  choose n hn hn0 hnt using h1
  let n' : Fin r → N := fun i => ⟨n i, hn i⟩
  have hli : LinearIndependent A n' := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hg' : ∑ j, g j • n j = 0 := by simpa [n'] using congrArg Subtype.val hg
    induction i using WellFoundedLT.induction with
    | _ i ih =>
      have := congrArg (φ i) hg'
      rw [map_sum, map_zero, Finset.sum_eq_single i] at this
      · rw [map_smul_alg, hnt] at this
        exact hinj (by rw [map_zero]; exact (mul_eq_zero.1 this).resolve_right (ht i))
      · intro j _ hj
        rcases lt_or_gt_of_ne hj with h | h
        · rw [ih j h, zero_smul, map_zero]
        · rw [map_smul_alg, hn0 j i h, mul_zero]
      · simp
  have hsp : ∀ k : ℕ, ∀ x : N, (∀ j : Fin r, (j : ℕ) + k < r → φ j x = 0) → x ∈ Submodule.span A (Set.range n') := by
    intro k
    induction k with
    | zero =>
      intro x hx
      have : x = 0 := Subtype.ext (hφ x x.2 fun j => hx j (by simp))
      rw [this]; exact Submodule.zero_mem _
    | succ k ih =>
      intro x hx
      by_cases hk : k < r
      · let i : Fin r := ⟨r - k - 1, by omega⟩
        have hi : (i : ℕ) = r - k - 1 := rfl
        have h0 : ∀ j < i, φ j x = 0 := fun j hj => hx j (by have : (j : ℕ) < i := hj; omega)
        obtain ⟨a, ha⟩ := h2 i x x.2 h0
        have := ih (x - a • n' i) fun j hj => by
          have hji : j ≤ i := by show (j : ℕ) ≤ i; omega
          show φ j ((x : W) - a • n i) = 0
          rw [map_sub, map_smul_alg]
          rcases hji.lt_or_eq with h | h
          · rw [h0 j h, hn0 i j h, mul_zero, sub_zero]
          · rw [h, ha, hnt, sub_self]
        have h3 := Submodule.add_mem _ this (Submodule.smul_mem _ a (Submodule.subset_span ⟨i, rfl⟩ :
          n' i ∈ Submodule.span A (Set.range n')))
        rwa [sub_add_cancel] at h3
      · exact ih x fun j hj => by omega
  refine ⟨Module.Basis.mk hli fun x _ => hsp r x fun j hj => by omega, fun i => ?_⟩
  rw [Module.Basis.mk_apply]
  exact ⟨hn0 i, hnt i⟩

theorem exists_smul_mem (m : Ideal A) [hm : m.IsPrime] (R : Subring Ω)
    (hR : ∀ x ∈ R, ∃ s ∉ m, ∃ a : A, algebraMap A Ω s * x = algebraMap A Ω a) (N : Submodule A W) (w : W)
    (hw : w ∈ Submodule.span R (N : Set W)) : ∃ s ∉ m, s • w ∈ N := by
  have h1 : (1 : A) ∉ m := (Ideal.ne_top_iff_one m).1 hm.ne_top
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, h1, by rwa [one_smul]⟩
  | zero => exact ⟨1, h1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hx⟩ := hx
    obtain ⟨u, hu, hy⟩ := hy
    refine ⟨s * u, fun h => (hm.mem_or_mem h).elim hs hu, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact N.smul_mem _ hx
    · rw [mul_smul]; exact N.smul_mem _ hy
  | smul c x _ hx =>
    obtain ⟨s, hs, hx⟩ := hx
    obtain ⟨u, hu, a, ha⟩ := hR c c.2
    refine ⟨u * s, fun h => (hm.mem_or_mem h).elim hu hs, ?_⟩
    have : (u * s) • c • x = a • s • x := by
      show (u * s) • (c : Ω) • x = _
      rw [← algebraMap_smul Ω (u * s), ← algebraMap_smul Ω a, ← algebraMap_smul Ω s, smul_smul, smul_smul, ← ha,
        map_mul]
      congr 1; ring
    rw [this]; exact N.smul_mem _ hx

end Glue

section Frames

variable {o Ω L : Type} [CommRing o] [Field Ω] [Algebra o Ω] {A : Subalgebra o Ω} [AddCommGroup L] [Module Ω L]

theorem vanish_step {r : ℕ} (b : Fin r → L) (i : ℕ) (w : Module.Dual Ω L) :
    (∀ e ∈ flagStep Ω b i, w e = 0) ↔ ∀ j : Fin r, (j : ℕ) < i → w (b j) = 0 := by
  refine ⟨fun h j hj => h _ (Submodule.subset_span ⟨j, hj, rfl⟩), fun h e he => ?_⟩
  have : flagStep Ω b i ≤ LinearMap.ker w := Submodule.span_le.2 (by rintro _ ⟨j, hj, rfl⟩; exact h j hj)
  exact this he

theorem flagStep_top {r : ℕ} (b : Fin r → L) : flagStep Ω b r = Submodule.span Ω (Set.range b) := by
  unfold flagStep
  congr 1
  ext x
  simp

def LocFrame (m : Ideal A) (P : L →ₗ[Ω] L) {r : ℕ} (b₀ : Fin r → L) (N : Submodule A (Module.Dual Ω L)) (d : Ω)
    (g : Fin r → Ω) : Prop :=
  ∃ R : Subring Ω, (∀ x ∈ R, ∃ s ∉ m, ∃ a : A, algebraMap A Ω s * x = algebraMap A Ω a) ∧
    ∃ b : Fin r → L, LinearIndependent Ω b ∧ (∀ i, flagStep Ω b i = flagStep Ω b₀ i) ∧
      (∀ i : Fin r, ∃ τ : Ω, b i - τ • b₀ i ∈ flagStep Ω b₀ i ∧ τ / g i ∈ R ∧ g i / τ ∈ R ∧ τ ≠ 0) ∧
      (∀ w ∈ N, ∀ i, d * w (b i) ∈ R) ∧
      ∀ w : Module.Dual Ω L, w ∘ₗ P = w → (∀ i, d * w (b i) ∈ R) → ∃ s ∉ m, s • w ∈ N

theorem exists_basis_frames (P : L →ₗ[Ω] L) {r : ℕ} (b₀ : Fin r → L)
    (hP : ∀ e, P e ∈ Submodule.span Ω (Set.range b₀)) (hP' : ∀ e ∈ Submodule.span Ω (Set.range b₀), P e = e)
    (N : Submodule A (Module.Dual Ω L)) (hN : ∀ w ∈ N, w ∘ₗ P = w) (d : Ω) (hd : d ≠ 0) (g : Fin r → Ω)
    (hg : ∀ i, g i ≠ 0) (h : ∀ m : Ideal A, m.IsMaximal → LocFrame m P b₀ N d g) :
    ∃ n : Module.Basis (Fin r) A N, ∀ i, (∀ j < i, (n i).1 (b₀ j) = 0) ∧ (n i).1 (b₀ i) = (d * g i)⁻¹ := by
  refine exists_basis (Ω := Ω) Subtype.val_injective N (fun j => Module.Dual.eval Ω L (b₀ j)) (fun i => (d * g i)⁻¹)
    (fun i => inv_ne_zero (mul_ne_zero hd (hg i))) ?_ ?_ ?_
  · intro w hw h0
    rw [← hN w hw]
    ext e
    have := (vanish_step b₀ r w).2 (fun j _ => h0 j) (P e) (by rw [flagStep_top]; exact hP e)
    simpa using this
  · intro m hm i
    obtain ⟨R, hR, b, hb, hF, hτ, -, h2⟩ := h m hm
    obtain ⟨τ, hτ, h3, -, hτ0⟩ := hτ i
    obtain ⟨φ, h1, h0⟩ := FlagGrGen.exists_coord hb i
    have hbP : ∀ j, P (b j) = b j := fun j => hP' _ (by
      rw [← flagStep_top, ← hF, flagStep_top]; exact Submodule.subset_span ⟨j, rfl⟩)
    have hPP : P ∘ₗ P = P := LinearMap.ext fun e => hP' _ (hP e)
    let w : Module.Dual Ω L := (d⁻¹ * (τ / g i)) • (φ ∘ₗ P)
    have hw : ∀ j, w (b j) = d⁻¹ * (τ / g i) * φ (b j) := fun j => by simp [w, hbP]
    obtain ⟨s, hs, hsw⟩ := h2 w (by rw [LinearMap.smul_comp, LinearMap.comp_assoc, hPP]) fun j => by
      rw [hw]
      by_cases hj : j = i
      · rw [hj, h1, mul_one, mul_inv_cancel_left₀ hd]; exact h3
      · rw [h0 j hj, mul_zero, mul_zero]; exact R.zero_mem
    have hv : ∀ e ∈ flagStep Ω b₀ i, w e = 0 := by
      rw [← hF, vanish_step]
      intro j hj
      rw [hw, h0 j (fun e => by simp [e] at hj), mul_zero]
    refine ⟨s, hs, s • w, hsw, fun j hj => ?_, ?_⟩
    · refine (map_smul_alg _ s w).trans ?_
      rw [Module.Dual.eval_apply, (vanish_step b₀ i w).1 hv j hj, mul_zero]
    · refine (map_smul_alg _ s w).trans ?_
      rw [Module.Dual.eval_apply]
      congr 1
      have := hv _ hτ
      rw [map_sub, map_smul, hw, h1, smul_eq_mul, sub_eq_zero] at this
      have hg' := hg i
      apply mul_left_cancel₀ hτ0
      rw [← this]; field_simp
  · intro m hm i n hn h0
    obtain ⟨R, hR, b, hb, hF, hτ, h1, -⟩ := h m hm
    obtain ⟨τ, hτ, -, h3, hτ0⟩ := hτ i
    have hv := (vanish_step b₀ i n).2 (fun j hj => h0 j hj) _ hτ
    rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at hv
    obtain ⟨s, hs, a, ha⟩ := hR _ (R.mul_mem (h1 n hn i) h3)
    refine ⟨s, hs, a, ?_⟩
    have hg' := hg i
    rw [← ha, hv, Module.Dual.eval_apply]
    field_simp

theorem shape_M (P : L →ₗ[Ω] L) {r : ℕ} (b₀ : Fin r → L) (hb₀ : LinearIndependent Ω b₀)
    (hP : ∀ e, P e ∈ Submodule.span Ω (Set.range b₀))
    (e : Fin r → Ω) (he : ∀ a, e a ≠ 0) :
    ∃ wM : Fin r → Module.Dual Ω L, ∀ (A : Subalgebra o Ω) (N : Submodule A (Module.Dual Ω L)), (∀ w ∈ N, w ∘ₗ P = w) →
      ∀ (c : Fin r → Ω) (n : Module.Basis (Fin r) A N),
        (∀ i, (∀ j < i, (n i).1 (b₀ j) = 0) ∧ (n i).1 (b₀ i) = c i.rev * e i.rev) →
        ∃ bM : Module.Basis (Fin r) A N, ∀ a, ∃ cf : Fin r → Ω, (∀ a', a < a' → cf a' = 0) ∧ cf a = c a ∧
          (bM a).1 = ∑ a', cf a' • wM a' := by
  choose φ h1 h0 using fun i => FlagGrGen.exists_coord hb₀ i
  refine ⟨fun a => e a • (φ a.rev ∘ₗ P), fun A N hN c n hn => ⟨n.reindex Fin.revPerm, fun a => ?_⟩⟩
  refine ⟨fun a' => (n a.rev).1 (b₀ a'.rev) / e a', fun a' h => ?_, ?_, ?_⟩
  · show _ / _ = _
    rw [(hn a.rev).1 _ (Fin.rev_lt_rev.2 h), zero_div]
  · show _ / _ = _
    rw [(hn a.rev).2, Fin.rev_rev, mul_div_cancel_right₀ _ (he a)]
  · rw [Module.Basis.reindex_apply]
    show (n a.rev).1 = _
    set w := (n a.rev).1
    have hw : w ∘ₗ P = w := hN w (n a.rev).2
    have key : ∀ x ∈ Submodule.span Ω (Set.range b₀), w x = ∑ a' : Fin r, w (b₀ a'.rev) * φ a'.rev x := by
      intro x hx
      have : Submodule.span Ω (Set.range b₀) ≤ LinearMap.ker (w - ∑ a' : Fin r, w (b₀ a'.rev) • φ a'.rev) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨j, rfl⟩
        show (w - ∑ a' : Fin r, w (b₀ a'.rev) • φ a'.rev) (b₀ j) = 0
        rw [LinearMap.sub_apply, LinearMap.sum_apply, Finset.sum_eq_single j.rev]
        · simp [h1]
        · intro k _ hk
          rw [LinearMap.smul_apply, h0 k.rev j (by rintro rfl; simp at hk), smul_zero]
        · simp
      have h := this hx
      simpa [sub_eq_zero] using h
    ext x
    rw [← hw, LinearMap.comp_apply, hw, key _ (hP x), LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun a' _ => ?_
    have := he a'
    simp only [LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply]
    field_simp

theorem shape_alt {r : ℕ} (b₀ : Fin r → L) (e : Fin r → Ω) (he : ∀ a, e a ≠ 0)
    (N : Submodule A (Module.Dual Ω L)) (c : Fin r → Ω) (hc : ∀ a, c a ≠ 0) (n : Module.Basis (Fin r) A N)
    (hn : ∀ i, (∀ j < i, (n i).1 (b₀ j) = 0) ∧ (n i).1 (b₀ i) = (c i * e i)⁻¹) :
    ∃ bW : Module.Basis (Fin r) A (Module.Dual A N), ∀ a, ∃ cf : Fin r → Ω, (∀ a', a < a' → cf a' = 0) ∧
      cf a = c a ∧ ∀ z : N, algebraMap A Ω (bW a z) = ∑ a', cf a' * Module.Dual.eval Ω L (e a' • b₀ a') z.1 := by
  classical
  let U : Matrix (Fin r) (Fin r) Ω := fun i j => (n i).1 (b₀ j)
  have hU : U.BlockTriangular id := fun i j h => (hn i).1 j h
  have hdet : U.det ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular hU]
    exact Finset.prod_ne_zero_iff.2 fun i _ => by
      show (n i).1 (b₀ i) ≠ 0
      rw [(hn i).2]; exact inv_ne_zero (mul_ne_zero (hc i) (he i))
  letI := U.invertibleOfIsUnitDet (IsUnit.mk0 _ hdet)
  have hU' : U⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hU
  have hmul : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U (IsUnit.mk0 _ hdet)
  refine ⟨n.dualBasis, fun a => ⟨fun a' => U⁻¹ a' a / e a', fun a' h => ?_, ?_, fun z => ?_⟩⟩
  · show _ / _ = _
    rw [hU' (show id a < id a' from h), zero_div]
  · have := congrFun (congrFun hmul a) a
    rw [Matrix.mul_apply, Finset.sum_eq_single a, Matrix.one_apply_eq] at this
    · have h2 : U a a = (c a * e a)⁻¹ := (hn a).2
      rw [h2] at this
      have h3 := hc a
      have h4 := he a
      show _ / _ = _
      field_simp at this ⊢
      linear_combination this
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hU (show id k < id a from h), zero_mul]
      · rw [hU' (show id a < id k from h), mul_zero]
    · simp
  · have hz : (z : Module.Dual Ω L) = ∑ i, n.repr z i • (n i).1 := by
      have := congrArg N.subtype (n.sum_repr z)
      rw [map_sum] at this
      exact this.symm
    rw [Module.Basis.dualBasis_apply, hz]
    simp only [map_sum, Finset.mul_sum]
    simp only [fun a' i => map_smul_alg (Module.Dual.eval Ω L (e a' • b₀ a')) (n.repr z i) (n i).1]
    rw [Finset.sum_comm]
    have : ∀ i, ∑ a', U⁻¹ a' a / e a' * (algebraMap A Ω (n.repr z i) * Module.Dual.eval Ω L (e a' • b₀ a') (n i).1) =
        algebraMap A Ω (n.repr z i) * (U * U⁻¹) i a := by
      intro i
      rw [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a' _ => ?_
      have := he a'
      rw [Module.Dual.eval_apply, map_smul, smul_eq_mul]
      change _ = _ * ((n i).1 (b₀ a') * _)
      field_simp
    rw [Finset.sum_congr rfl fun i _ => this i, hmul]
    simp [Matrix.one_apply]

end Frames

end PositivityTheory.HtPt.Flagb
