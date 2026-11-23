import ReciprocityTheory.SemistableReduction.SemiDegSt

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Module

def waR {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (x : Fin r → K) :
    (Fin r → K) →ₗ[K] K where
  toFun y := S.h x y
  map_add' y z := by
    simp only [HermForm.h, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a y := by
    simp only [HermForm.h, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem waR_apply {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y : Fin r → K) : waR S x y = S.h x y := rfl

theorem wa_symm {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y : Fin r → K) : S.h y x = S.c (S.h x y) := by
  unfold HermForm.h
  simp only [map_sum, map_mul, S.c_invol, S.G_herm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem wa_sub_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y z : Fin r → K) : S.h x (y - z) = S.h x y - S.h x z := by
  simp only [HermForm.h, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem wa_smul_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (a : K) (x y : Fin r → K) : S.h x (a • y) = a * S.h x y := by
  simp only [HermForm.h, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem wa_zero_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x : Fin r → K) : S.h x 0 = 0 := by
  simp [HermForm.h]

theorem wa_sub_left {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y z : Fin r → K) : S.h (x - y) z = S.h x z - S.h y z := by
  simp only [HermForm.h, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem wa_smul_left {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (a : K) (x y : Fin r → K) : S.h (a • x) y = S.c a * S.h x y := by
  simp only [HermForm.h, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem wa_sum_right {K : Type} [Field K] [NumberField K] {r n : ℕ} (S : HermForm K r)
    (x : Fin r → K) (t : Fin n → K) (b : Fin n → Fin r → K) :
    S.h x (∑ i, t i • b i) = ∑ i, t i * S.h x (b i) := by
  rw [← waR_apply S x, map_sum]
  simp only [map_smul, smul_eq_mul, waR_apply]

theorem wa_sum_left {K : Type} [Field K] [NumberField K] {r n : ℕ} (S : HermForm K r)
    (y : Fin r → K) (t : Fin n → K) (b : Fin n → Fin r → K) :
    S.h (∑ i, t i • b i) y = ∑ i, S.c (t i) * S.h (b i) y := by
  rw [wa_symm S y, wa_sum_right, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← wa_symm S y (b i)]

theorem wa_finrank_inf_ker {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W : Submodule K V) (f : V →ₗ[K] K) (z : V) (hz : z ∈ W)
    (hfz : f z ≠ 0) : finrank K ↥(W ⊓ LinearMap.ker f) + 1 = finrank K W := by
  have hsup : W ⊔ LinearMap.ker f = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : v = (f v / f z) • z + (v - (f v / f z) • z) := by abel
    rw [hv]
    refine Submodule.add_mem_sup (W.smul_mem _ hz) ?_
    rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hfz, sub_self]
  have hker : finrank K (LinearMap.ker f) + 1 = finrank K V := by
    have h := LinearMap.finrank_range_add_finrank_ker f
    have hr : LinearMap.range f = ⊤ := by
      rw [eq_top_iff]
      intro a _
      exact ⟨(a / f z) • z, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hfz]⟩
    rw [hr, finrank_top, Module.finrank_self] at h
    omega
  have h := Submodule.finrank_sup_add_finrank_inf_eq W (LinearMap.ker f)
  rw [hsup, finrank_top] at h
  omega

theorem wa_diag {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) :
    ∀ (n : ℕ) (W : Submodule K (Fin r → K)), finrank K W = n →
      (∀ x ∈ W, S.h x x = 0 → x = 0) →
      ∃ b : Fin n → Fin r → K, (∀ i, b i ∈ W) ∧ (∀ i, b i ≠ 0) ∧
        ∀ i j, i ≠ j → S.h (b i) (b j) = 0 := by
  intro n
  induction n with
  | zero =>
    intro W _ _
    exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    intro W hW han
    have hne : W ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hW
      omega
    obtain ⟨z, hzW, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hzz : S.h z z ≠ 0 := fun h => hz0 (han z hzW h)
    have hW' : finrank K ↥(W ⊓ LinearMap.ker (waR S z)) = n := by
      have h := wa_finrank_inf_ker W (waR S z) z hzW (by rw [waR_apply]; exact hzz)
      omega
    obtain ⟨b, hbW, hb0, hbo⟩ := ih (W ⊓ LinearMap.ker (waR S z)) hW' (fun x hx hxx => han x hx.1 hxx)
    have hk : ∀ k, S.h z (b k) = 0 := fun k => (hbW k).2
    refine ⟨Fin.cons z b, fun i => ?_, fun i => ?_, fun i j hij => ?_⟩
    · cases i using Fin.cases with
      | zero => simpa using hzW
      | succ i => simpa using (hbW i).1
    · cases i using Fin.cases with
      | zero => simpa using hz0
      | succ i => simpa using hb0 i
    · cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j => simpa using hk j
      | succ i =>
        cases j using Fin.cases with
        | zero =>
          simp only [Fin.cons_succ, Fin.cons_zero]
          rw [wa_symm S z (b i), hk i, map_zero]
        | succ j =>
          simp only [Fin.cons_succ]
          exact hbo i j fun h => hij (by rw [h])

theorem wa_hyp {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (W : Submodule K (Fin r → K)) (hnd : ∀ x ∈ W, (∀ y ∈ W, S.h x y = 0) → x = 0)
    (x : Fin r → K) (hxW : x ∈ W) (hx0 : x ≠ 0) (hxx : S.h x x = 0) :
    ∃ y ∈ W, S.h x y = 1 ∧ S.h y y = 0 := by
  obtain ⟨w, hwW, hw⟩ : ∃ w ∈ W, S.h x w ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hx0 (hnd x hxW hc)
  obtain ⟨u, hu⟩ : ∃ u, u = (S.h x w)⁻¹ • w := ⟨_, rfl⟩
  have huW : u ∈ W := hu ▸ W.smul_mem _ hwW
  have hxu : S.h x u = 1 := by rw [hu, wa_smul_right, inv_mul_cancel₀ hw]
  have hux : S.h u x = 1 := by rw [wa_symm S x u, hxu, map_one]
  have hcuu : S.c (S.h u u) = S.h u u := (wa_symm S u u).symm
  obtain ⟨t, ht⟩ : ∃ t, t = S.h u u / 2 := ⟨_, rfl⟩
  have hct : S.c t = t := by rw [ht, map_div₀, hcuu, map_ofNat]
  refine ⟨u - t • x, W.sub_mem huW (W.smul_mem _ hxW), ?_, ?_⟩
  · rw [wa_sub_right, hxu, wa_smul_right, hxx, mul_zero, sub_zero]
  · simp only [wa_sub_left, wa_sub_right, wa_smul_left, wa_smul_right, hux, hxu, hxx, hct]
    rw [ht]
    ring

theorem wa_perp_nondeg {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (W : Submodule K (Fin r → K)) (hnd : ∀ x ∈ W, (∀ y ∈ W, S.h x y = 0) → x = 0)
    (x y : Fin r → K) (hxW : x ∈ W) (hyW : y ∈ W) (hxx : S.h x x = 0) (hxy : S.h x y = 1)
    (hyy : S.h y y = 0) :
    ∀ z ∈ W ⊓ LinearMap.ker (waR S x) ⊓ LinearMap.ker (waR S y),
      (∀ w ∈ W ⊓ LinearMap.ker (waR S x) ⊓ LinearMap.ker (waR S y), S.h z w = 0) → z = 0 := by
  intro z hz hzo
  obtain ⟨⟨hzW, hzx⟩, hzy⟩ := hz
  have hzx : S.h x z = 0 := hzx
  have hzy : S.h y z = 0 := hzy
  apply hnd z hzW
  intro w hwW
  have hyx : S.h y x = 1 := by rw [wa_symm S x y, hxy, map_one]
  have hw' : w - S.h y w • x - S.h x w • y ∈ W ⊓ LinearMap.ker (waR S x) ⊓ LinearMap.ker (waR S y) := by
    refine ⟨⟨W.sub_mem (W.sub_mem hwW (W.smul_mem _ hxW)) (W.smul_mem _ hyW), ?_⟩, ?_⟩
    · show S.h x _ = 0
      simp only [wa_sub_right, wa_smul_right, hxx, hxy]
      ring
    · show S.h y _ = 0
      simp only [wa_sub_right, wa_smul_right, hyx, hyy]
      ring
  have h1 := hzo _ hw'
  have hzx' : S.h z x = 0 := by rw [wa_symm S x z, hzx, map_zero]
  have hzy' : S.h z y = 0 := by rw [wa_symm S y z, hzy, map_zero]
  simp only [wa_sub_right, wa_smul_right, hzx', hzy', mul_zero, sub_zero] at h1
  exact h1

end ReciprocityTheory.MultiplicativeHeights
