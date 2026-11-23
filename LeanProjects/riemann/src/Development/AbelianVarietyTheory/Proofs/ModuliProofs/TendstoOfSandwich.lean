import Mathlib

namespace GlobalTheory.VolFin

open Module Filter Topology

section Alg

variable {K F F' : Type} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] {ι : Type}

def piece (R : ι → Subalgebra K F) (γ : ι → F) (e : ℕ) : Submodule K F where
  carrier := {f | ∀ i, f * γ i ^ e ∈ R i}
  add_mem' ha hb i := by rw [add_mul]; exact (R i).add_mem (ha i) (hb i)
  zero_mem' i := by rw [zero_mul]; exact (R i).zero_mem
  smul_mem' c a ha i := by rw [smul_mul_assoc]; exact (R i).smul_mem (ha i) c

theorem mem_piece {R : ι → Subalgebra K F} {γ : ι → F} {e : ℕ} {f : F} :
    f ∈ piece R γ e ↔ ∀ i, f * γ i ^ e ∈ R i := Iff.rfl

theorem mul_mem_piece {R : ι → Subalgebra K F} {γ : ι → F} {e e' : ℕ} {a b : F}
    (ha : a ∈ piece R γ e) (hb : b ∈ piece R γ e') : a * b ∈ piece R γ (e + e') := mem_piece.2 fun i => by
  have hab := (R i).mul_mem (mem_piece.1 ha i) (mem_piece.1 hb i)
  rw [pow_add]
  convert hab using 1
  ring

def Den (R : ι → Subalgebra K F) (γ : ι → F) : Prop :=
  ∀ u : F, ∃ c, ∃ q ∈ piece R γ c, q ≠ 0 ∧ q * u ∈ piece R γ c

theorem Den.finset {R : ι → Subalgebra K F} {γ : ι → F} (h : Den R γ) (s : Finset F) :
    ∃ c, ∃ q ∈ piece R γ c, q ≠ 0 ∧ ∀ u ∈ s, q * u ∈ piece R γ c := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 1, mem_piece.2 fun i => by simp, one_ne_zero, by simp⟩
  | insert u s hu ih =>
    obtain ⟨c, q, hq, hq0, hs⟩ := ih
    obtain ⟨c', q', hq', hq'0, hu'⟩ := h u
    refine ⟨c + c', q * q', mul_mem_piece hq hq', mul_ne_zero hq0 hq'0, ?_⟩
    intro v hv
    rcases Finset.mem_insert.1 hv with rfl | hv
    · rw [mul_assoc]
      exact mul_mem_piece hq hu'
    · rw [mul_right_comm]
      exact mul_mem_piece (hs v hv) hq'

theorem Den.family {R : ι → Subalgebra K F} {γ : ι → F} (h : Den R γ) {κ : Type} [Finite κ]
    (u : κ → F) : ∃ c, ∃ q ∈ piece R γ c, q ≠ 0 ∧ ∀ k, q * u k ∈ piece R γ c := by
  classical
  have := Fintype.ofFinite κ
  obtain ⟨c, q, hq, hq0, hs⟩ := h.finset (Finset.univ.image u)
  exact ⟨c, q, hq, hq0, fun k => hs _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))⟩

variable [Algebra F F'] [IsScalarTower K F F'] [Module.Finite F F'] [Finite ι]

theorem upper {R : ι → Subalgebra K F} {γ : ι → F} {R' : ι → Subalgebra K F'} (h : Den R γ)
    (hG : ∀ i, ∃ (n : ℕ) (g : Fin n → F'), ∀ t ∈ R' i, ∃ w : Fin n → F,
      (∀ l, w l ∈ R i) ∧ t = ∑ l, w l • g l)
    (hfin : ∀ e, Module.Finite K (piece R γ e)) :
    ∃ c, ∀ e, Module.Finite K (piece R' (fun i => algebraMap F F' (γ i)) e) ∧
      finrank K (piece R' (fun i => algebraMap F F' (γ i)) e) ≤
        finrank F F' * finrank K (piece R γ (e + c)) := by
  classical
  choose n g hg using hG
  have b : Basis (Fin (finrank F F')) F F' := Module.finBasis F F'
  obtain ⟨c, q, -, hq0, hu⟩ := h.family (κ := Σ i : ι, Fin (n i) × Fin (finrank F F'))
    (fun k => b.repr (g k.1 k.2.1) k.2.2)
  refine ⟨c, fun e => ?_⟩
  have := hfin (e + c)
  have key : ∀ f ∈ piece R' (fun i => algebraMap F F' (γ i)) e, ∀ j,
      q * b.repr f j ∈ piece R γ (e + c) := by
    intro f hf j
    refine mem_piece.2 fun i => ?_
    obtain ⟨w, hw, hfw⟩ := hg i _ (mem_piece.1 hf i)
    have hfw' : (γ i ^ e) • f = ∑ l, w l • g i l := by
      rw [Algebra.smul_def, map_pow, mul_comm]
      exact hfw
    have h1 : γ i ^ e * b.repr f j = ∑ l, w l * b.repr (g i l) j := by
      have := congrArg (fun x => b.repr x j) hfw'
      simpa [map_sum, Finsupp.finsetSum_apply] using this
    have h2 : q * b.repr f j * γ i ^ (e + c) = ∑ l, w l * (q * b.repr (g i l) j * γ i ^ c) := by
      rw [pow_add, show q * b.repr f j * (γ i ^ e * γ i ^ c)
        = (γ i ^ e * b.repr f j) * (q * γ i ^ c) by ring, h1, Finset.sum_mul]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [h2]
    exact Subalgebra.sum_mem _ fun l _ => (R i).mul_mem (hw l) (mem_piece.1 (hu ⟨i, l, j⟩) i)
  let Φ : piece R' (fun i => algebraMap F F' (γ i)) e →ₗ[K] (Fin (finrank F F') → piece R γ (e + c)) :=
    { toFun := fun f j => ⟨q * b.repr f j, key f f.2 j⟩
      map_add' := fun f f' => by
        funext j
        apply Subtype.ext
        simp [mul_add]
      map_smul' := fun a f => by
        funext j
        apply Subtype.ext
        simp only [SetLike.val_smul, RingHom.id_apply, Pi.smul_apply]
        rw [← algebraMap_smul F a (f : F'), map_smul, Finsupp.smul_apply, smul_eq_mul,
          Algebra.smul_def]
        ring }
  have hinj : Function.Injective Φ := by
    intro f f' hff
    apply Subtype.ext
    apply b.repr.injective
    ext j
    have := congrArg (fun x => ((x j : piece R γ (e + c)) : F)) hff
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk] at this
    exact mul_left_cancel₀ hq0 this
  have : Module.Finite K (piece R' (fun i => algebraMap F F' (γ i)) e) :=
    Module.Finite.of_injective Φ hinj
  refine ⟨this, ?_⟩
  calc finrank K (piece R' (fun i => algebraMap F F' (γ i)) e)
      ≤ finrank K (Fin (finrank F F') → piece R γ (e + c)) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = finrank F F' * finrank K (piece R γ (e + c)) := by
        simp [Module.finrank_pi_fintype]

omit [IsScalarTower K F F'] [Module.Finite F F'] in
theorem mem_span_of_frac (S : Subalgebra K F') (hS : ∀ t : F', ∃ a ∈ S, ∃ b ∈ S, b ≠ 0 ∧ t * b = a)
    (halg : ∀ b ∈ S, IsAlgebraic F b) (t : F') : t ∈ Submodule.span F (S : Set F') := by
  obtain ⟨a, ha, b, hb, hb0, htb⟩ := hS t
  have hsub : ((Submonoid.closure (S : Set F') : Submonoid F') : Set F') ⊆
      (Submodule.span F (S : Set F') : Set F') := by
    intro x hx
    have hx' : x ∈ S.toSubmonoid :=
      (Submonoid.closure_le (S := S.toSubmonoid)).2 (fun y hy => hy) hx
    exact Submodule.subset_span hx'
  rw [← Algebra.adjoin_eq_span_of_subset F hsub, Subalgebra.mem_toSubmodule]
  have hbinv : b⁻¹ ∈ Algebra.adjoin F (S : Set F') :=
    Algebra.adjoin_mono (Set.singleton_subset_iff.2 hb) (halg b hb).isIntegral.inv_mem_adjoin
  have ht : t = a * b⁻¹ := by rw [← htb, mul_assoc, mul_inv_cancel₀ hb0, mul_one]
  rw [ht]
  exact Subalgebra.mul_mem _ (Algebra.subset_adjoin ha) hbinv

omit [IsScalarTower K F F'] [Module.Finite F F'] in
theorem finite_of_frac (S : Subalgebra K F') (hS : ∀ t : F', ∃ a ∈ S, ∃ b ∈ S, b ≠ 0 ∧ t * b = a)
    {n : ℕ} (g : Fin n → F') (hg : ∀ t ∈ S, ∃ w : Fin n → F, t = ∑ l, w l • g l) :
    Module.Finite F F' := by
  have hle : Submodule.span F (S : Set F') ≤ Submodule.span F (Set.range g) := by
    rw [Submodule.span_le]
    intro t ht
    obtain ⟨w, rfl⟩ := hg t ht
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  have hsub : ((Submonoid.closure (S : Set F') : Submonoid F') : Set F') ⊆
      (Submodule.span F (S : Set F') : Set F') := by
    intro x hx
    have hx' : x ∈ S.toSubmonoid :=
      (Submonoid.closure_le (S := S.toSubmonoid)).2 (fun y hy => hy) hx
    exact Submodule.subset_span hx'
  have : FiniteDimensional F (Submodule.span F (Set.range g)) :=
    FiniteDimensional.span_of_finite F (Set.finite_range g)
  have : FiniteDimensional F (Submodule.span F (S : Set F')) :=
    Submodule.finiteDimensional_of_le hle
  have halg : ∀ b ∈ S, IsAlgebraic F b := by
    intro b hb
    refine (IsIntegral.of_mem_of_fg (Algebra.adjoin F (S : Set F')) ?_ b
      (Algebra.subset_adjoin hb)).isAlgebraic
    rw [Algebra.adjoin_eq_span_of_subset F hsub]
    exact Module.Finite.iff_fg.1 inferInstance
  have htop : Submodule.span F (Set.range g) = ⊤ :=
    eq_top_iff.2 fun t _ => hle (mem_span_of_frac S hS halg t)
  exact Module.finite_def.2 (Submodule.fg_def.2 ⟨_, Set.finite_range g, htop⟩)

theorem lower {R : ι → Subalgebra K F} {γ : ι → F} {R' : ι → Subalgebra K F'} (h : Den R γ)
    (hR : ∀ i, ∀ a ∈ R i, algebraMap F F' a ∈ R' i)
    (hS : ∀ i, ∀ t : F', ∃ a ∈ R' i, ∃ b ∈ R' i, b ≠ 0 ∧ t * b = a)
    (hfin : ∀ e, Module.Finite K (piece R' (fun i => algebraMap F F' (γ i)) e)) :
    ∃ c, ∀ e, Module.Finite K (piece R γ e) → finrank F F' * finrank K (piece R γ e) ≤
      finrank K (piece R' (fun i => algebraMap F F' (γ i)) (e + c)) := by
  classical
  have b : Basis (Fin (finrank F F')) F F' := Module.finBasis F F'
  have hspan : ∀ i, ∀ t : F', t ∈ Submodule.span F (R' i : Set F') := fun i t =>
    mem_span_of_frac (R' i) (hS i) (fun x _ => (IsIntegral.of_finite F x).isAlgebraic) t
  choose n f s hfs using fun p : ι × Fin (finrank F F') =>
    Submodule.mem_span_set'.1 (hspan p.1 (b p.2))
  obtain ⟨c, q, -, hq0, hu⟩ := h.family (κ := Σ p : ι × Fin (finrank F F'), Fin (n p))
    (fun k => f k.1 k.2)
  let v : Fin (finrank F F') → F' := fun j => q • b j
  have hv : ∀ j, v j ∈ piece R' (fun i => algebraMap F F' (γ i)) c := by
    intro j
    refine mem_piece.2 fun i => ?_
    have hvj : v j * algebraMap F F' (γ i) ^ c =
        ∑ l, algebraMap F F' (q * f (i, j) l * γ i ^ c) * (s (i, j) l : F') := by
      simp only [v]
      rw [show b j = _ from (hfs (i, j)).symm, Finset.smul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [Algebra.smul_def, map_mul, map_pow]
      ring
    rw [hvj]
    exact Subalgebra.sum_mem _ fun l _ =>
      (R' i).mul_mem (hR i _ (mem_piece.1 (hu ⟨(i, j), l⟩) i)) (s (i, j) l).2
  refine ⟨c, fun e hP => ?_⟩
  have := hP
  have := hfin (e + c)
  have key : ∀ x : Fin (finrank F F') → piece R γ e,
      ∑ j, (x j : F) • v j ∈ piece R' (fun i => algebraMap F F' (γ i)) (e + c) := by
    intro x
    refine mem_piece.2 fun i => ?_
    rw [Finset.sum_mul]
    refine Subalgebra.sum_mem _ fun j _ => ?_
    have hxj : (x j : F) • v j * algebraMap F F' (γ i) ^ (e + c) =
        algebraMap F F' ((x j : F) * γ i ^ e) * (v j * algebraMap F F' (γ i) ^ c) := by
      rw [Algebra.smul_def, map_mul, map_pow, pow_add]
      ring
    rw [hxj]
    exact (R' i).mul_mem (hR i _ (mem_piece.1 (x j).2 i)) (mem_piece.1 (hv j) i)
  let Φ : (Fin (finrank F F') → piece R γ e) →ₗ[K]
      piece R' (fun i => algebraMap F F' (γ i)) (e + c) :=
    { toFun := fun x => ⟨∑ j, (x j : F) • v j, key x⟩
      map_add' := fun x y => by
        apply Subtype.ext
        simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a x => by
        apply Subtype.ext
        simp [Finset.smul_sum, smul_assoc] }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 : ∑ j, ((x j : F) * q) • b j = 0 := by
      have := congrArg Subtype.val hx
      simpa [Φ, v, smul_smul] using this
    funext j
    have hj := (Fintype.linearIndependent_iff.1 b.linearIndependent) _ h0 j
    exact Subtype.ext (by simpa using (mul_eq_zero.1 hj).resolve_right hq0)
  calc finrank F F' * finrank K (piece R γ e)
      = finrank K (Fin (finrank F F') → piece R γ e) := by
        simp [Module.finrank_pi_fintype]
    _ ≤ _ := LinearMap.finrank_le_finrank_of_injective hinj

end Alg

theorem tendsto_of_sandwich (h h' : ℕ → ℕ) (D g c c' : ℕ) (δ : ℝ)
    (hh : Tendsto (fun e : ℕ => (h e : ℝ) / (e : ℝ) ^ g) atTop (𝓝 δ))
    (lo : ∀ e, D * h e ≤ h' (e + c)) (up : ∀ e, h' e ≤ D * h (e + c')) :
    Tendsto (fun e : ℕ => (h' e : ℝ) / (e : ℝ) ^ g) atTop (𝓝 (D * δ)) := by
  have hr : ∀ k : ℕ, Tendsto (fun e : ℕ => (((e + k : ℕ) : ℝ) / (e : ℝ)) ^ g) atTop (𝓝 1) := by
    intro k
    have h2 := ((tendsto_natCast_div_add_atTop (k : ℝ)).inv₀ one_ne_zero).pow g
    rw [inv_one, one_pow] at h2
    refine h2.congr fun e => ?_
    rw [inv_div, Nat.cast_add]
  refine (tendsto_add_atTop_iff_nat c).1 ?_
  have hL : Tendsto (fun e : ℕ => (D : ℝ) * ((h e : ℝ) / (e : ℝ) ^ g) /
      (((e + c : ℕ) : ℝ) / (e : ℝ)) ^ g) atTop (𝓝 (D * δ)) := by
    have := (hh.const_mul (D : ℝ)).div (hr c) one_ne_zero
    rwa [div_one] at this
  have hU : Tendsto (fun e : ℕ => (D : ℝ) * ((h (e + (c + c')) : ℝ) /
      ((e + (c + c') : ℕ) : ℝ) ^ g) * ((((e + c) + c' : ℕ) : ℝ) / ((e + c : ℕ) : ℝ)) ^ g)
      atTop (𝓝 (D * δ)) := by
    have := ((hh.comp (tendsto_add_atTop_nat (c + c'))).const_mul (D : ℝ)).mul
      ((hr c').comp (tendsto_add_atTop_nat c))
    rw [mul_one] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with e he
    have he0 : (0 : ℝ) < e := by exact_mod_cast he
    have hcast : ((D * h e : ℕ) : ℝ) ≤ (h' (e + c) : ℝ) := by exact_mod_cast lo e
    push_cast at hcast ⊢
    have hc0 : (0 : ℝ) < (e : ℝ) + c := by positivity
    have heq : (D : ℝ) * ((h e : ℝ) / (e : ℝ) ^ g) / (((e : ℝ) + c) ^ g / (e : ℝ) ^ g)
        = (D : ℝ) * (h e : ℝ) / ((e : ℝ) + c) ^ g := by
      field_simp
    rw [div_pow, heq]
    gcongr
  · filter_upwards [eventually_ge_atTop 1] with e he
    have he0 : (0 : ℝ) < e := by exact_mod_cast he
    have hcast : (h' (e + c) : ℝ) ≤ ((D * h (e + c + c') : ℕ) : ℝ) := by exact_mod_cast up (e + c)
    rw [show e + (c + c') = e + c + c' from (add_assoc _ _ _).symm]
    push_cast at hcast ⊢
    have hc0 : (0 : ℝ) < (e : ℝ) + c := by positivity
    have hcc0 : (0 : ℝ) < (e : ℝ) + c + c' := by positivity
    have heq : (D : ℝ) * ((h (e + c + c') : ℝ) / ((e : ℝ) + c + c') ^ g) *
        (((e : ℝ) + c + c') ^ g / ((e : ℝ) + c) ^ g)
        = (D : ℝ) * (h (e + c + c') : ℝ) / ((e : ℝ) + c) ^ g := by
      field_simp
    rw [div_pow, heq]
    gcongr

end GlobalTheory.VolFin
