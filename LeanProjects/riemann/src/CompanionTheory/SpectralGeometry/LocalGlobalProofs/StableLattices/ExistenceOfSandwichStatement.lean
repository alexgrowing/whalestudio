import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich

open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.RgFl.MaxLat

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L]
  {V : Type} [AddCommGroup V] [Module L V]

theorem herm_add_left {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) (x y z : V) :
    h (x + y) z = h x z + h y z := by
  rw [hh.2.2.1 z (x + y), hh.1, map_add, ← hh.2.2.1 z x, ← hh.2.2.1 z y]

def hLin {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) (z : V) : V →ₗ[L] L where
  toFun := h z
  map_add' := hh.1 z
  map_smul' a y := by simpa using hh.2.1 a z y

theorem herm_eq_sum {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) {ι : Type} [Fintype ι]
    (b : Module.Basis ι L V) (z y : V) : h z y = ∑ j, b.repr y j * h z (b j) := by
  calc h z y = hLin hh z y := rfl
    _ = hLin hh z (∑ j, b.repr y j • b j) := by rw [b.sum_repr]
    _ = ∑ j, b.repr y j * h z (b j) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul]
      rfl

theorem norm_sub_le_max_of_ultrametric_field (a b : L) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  simpa [sub_eq_add_neg] using IsUltrametricDist.norm_add_le_max a (-b)

theorem norm_herm_le_delta {s : L →+* L} {δ : L} {h : V → V → L} (hδ : IsDelta s δ)
    (hh : IsHerm s h) {M : AddSubgroup V} (hO : ∀ a : L, ‖a‖ ≤ 1 → ∀ x ∈ M, a • x ∈ M)
    (hM : ∀ x ∈ M, ‖h x x‖ ≤ 1) {x y : V} (hx : x ∈ M) (hy : y ∈ M) : ‖h x y‖ ≤ ‖δ‖ := by
  refine (hδ.2.1 (h x y)).1 fun t ht => ?_
  have hy' : t • y ∈ M := hO t ht y hy
  have e1 : h x (t • y) = h x y * t := by rw [hh.2.1, mul_comm]
  have e2 : h (t • y) x = s (h x y * t) := by rw [hh.2.2.1 x (t • y), e1]
  have e3 : h (x + t • y) (x + t • y)
      = h x x + (h x y * t + s (h x y * t)) + h (t • y) (t • y) := by
    rw [herm_add_left hh, hh.1, hh.1, e1, e2]; ring
  have e4 : h x y * t + s (h x y * t)
      = h (x + t • y) (x + t • y) - h x x - h (t • y) (t • y) := by
    rw [e3]; ring
  rw [e4]
  exact (norm_sub_le_max_of_ultrametric_field _ _).trans (max_le
    ((norm_sub_le_max_of_ultrametric_field _ _).trans
      (max_le (hM _ (M.add_mem hx hy')) (hM _ hx))) (hM _ hy'))

theorem exists_basis_herm_le_one [FiniteDimensional L V] {s : L →+* L} {h : V → V → L}
    (hs : IsInv s) (hh : IsHerm s h) :
    ∃ (m : ℕ) (b : Module.Basis (Fin m) L V), ∀ i j, ‖h (b i) (b j)‖ ≤ 1 := by
  let e := Module.finBasis L V
  let K : ℝ := ∑ i, ∑ j, ‖h (e i) (e j)‖
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hKij : ∀ i j, ‖h (e i) (e j)‖ ≤ K := fun i j =>
    (Finset.single_le_sum (f := fun j => ‖h (e i) (e j)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, ‖h (e i) (e j)‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  obtain ⟨t, ht0, ht⟩ := NormedField.exists_norm_lt L (show (0 : ℝ) < 1 / (K + 1) by positivity)
  have htK : ‖t‖ * (K + 1) ≤ 1 := by
    rw [lt_div_iff₀ (by positivity)] at ht
    exact ht.le
  have ht1 : ‖t‖ ≤ 1 := by nlinarith [norm_nonneg t]
  have htK' : ‖t‖ * K ≤ 1 := by nlinarith [norm_nonneg t]
  have tne : t ≠ 0 := norm_pos_iff.1 ht0
  have hu : ∀ i : Fin (Module.finrank L V), IsUnit ((fun _ => t) i : L) :=
    fun _ => isUnit_iff_ne_zero.2 tne
  refine ⟨_, e.isUnitSMul hu, fun i j => ?_⟩
  simp only [Module.Basis.isUnitSMul_apply]
  have e1 : h (t • e i) (t • e j) = t * (s t * h (e i) (e j)) := by
    rw [hh.2.1, hh.2.2.1 (e j) (t • e i), hh.2.1, map_mul, ← hh.2.2.1 (e j) (e i)]
  rw [e1, norm_mul, norm_mul, hs.2.1]
  calc ‖t‖ * (‖t‖ * ‖h (e i) (e j)‖) ≤ 1 * (‖t‖ * K) := by
        gcongr
        exact hKij i j
    _ ≤ 1 := by linarith

def ball {ι : Type} (b : Module.Basis ι L V) : AddSubgroup V where
  carrier := {x | ∀ i, ‖b.repr x i‖ ≤ 1}
  add_mem' {x y} hx hy i := by
    simpa using (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx i) (hy i))
  zero_mem' i := by simp
  neg_mem' {x} hx i := by simpa using hx i

theorem basis_mem_ball {ι : Type} [DecidableEq ι] (b : Module.Basis ι L V) (j : ι) :
    b j ∈ ball b := by
  intro i
  rw [b.repr_self, Finsupp.single_apply]
  split_ifs <;> simp

theorem IsLat.smul_mem {Λ : AddSubgroup V} (hΛ : IsLat L Λ) {a : L} (ha : ‖a‖ ≤ 1) {x : V}
    (hx : x ∈ Λ) : a • x ∈ Λ := by
  obtain ⟨m, b, hb⟩ := hΛ
  rw [hb] at hx ⊢
  intro i
  simpa using mul_le_one₀ ha (norm_nonneg _) (hx i)

theorem ball_absorbing {m : ℕ} (b : Module.Basis (Fin m) L V) (x : V) :
    ∃ a : L, a ≠ 0 ∧ a • x ∈ ball b := by
  let K : ℝ := ∑ i, ‖b.repr x i‖
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => norm_nonneg _
  obtain ⟨t, ht0, ht⟩ := NormedField.exists_norm_lt L (show (0 : ℝ) < 1 / (K + 1) by positivity)
  have htK : ‖t‖ * (K + 1) ≤ 1 := by
    rw [lt_div_iff₀ (by positivity)] at ht
    exact ht.le
  refine ⟨t, norm_pos_iff.1 ht0, fun i => ?_⟩
  have hi : ‖b.repr x i‖ ≤ K :=
    Finset.single_le_sum (f := fun i => ‖b.repr x i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
  nlinarith [norm_nonneg t, norm_nonneg (b.repr x i)]

theorem norm_herm_ball_le_one {s : L →+* L} {h : V → V → L} (hs : IsInv s) (hh : IsHerm s h)
    {m : ℕ} (b : Module.Basis (Fin m) L V) (hb : ∀ i j, ‖h (b i) (b j)‖ ≤ 1) {x : V}
    (hx : x ∈ ball b) : ‖h x x‖ ≤ 1 := by
  have h1 : ∀ j, ‖h (b j) x‖ ≤ 1 := fun j => by
    rw [herm_eq_sum hh b]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (hx i) (norm_nonneg _) (hb j i)
  rw [herm_eq_sum hh b]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun j _ => ?_
  rw [norm_mul, hh.2.2.1 (b j) x, hs.2.1]
  exact mul_le_one₀ (hx j) (norm_nonneg _) (h1 j)

theorem exists_scale {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) (B : ℝ) (hB : 0 ≤ B)
    {m : ℕ} (b : Module.Basis (Fin m) L V) :
    ∃ c : L, c ≠ 0 ∧ ∀ x, (∀ j, ‖h (b j) x‖ ≤ B) → c • x ∈ ball b := by
  let T : V →ₗ[L] (Fin m → L) := LinearMap.pi fun j => hLin hh (b j)
  have hT : LinearMap.ker T = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun x hx => hh.2.2.2 x fun y => ?_
    have hj : ∀ j, h (b j) x = 0 := fun j => congrFun hx j
    rw [herm_eq_sum hh b]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hh.2.2.1 (b j) x, hj j, map_zero, mul_zero]
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective T hT
  let w : Fin m → V := fun k => g fun j => if k = j then 1 else 0
  have hx : ∀ x, x = ∑ k, h (b k) x • w k := fun x => by
    have h1 : g (T x) = x := by simpa using LinearMap.congr_fun hg x
    have h2 := LinearMap.pi_apply_eq_sum_univ g (T x)
    rw [h1] at h2
    exact h2
  let C : ℝ := ∑ k, ∑ i, ‖b.repr (w k) i‖
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hCki : ∀ k i, ‖b.repr (w k) i‖ ≤ C := fun k i =>
    (Finset.single_le_sum (f := fun i => ‖b.repr (w k) i‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun k => ∑ i, ‖b.repr (w k) i‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ k))
  obtain ⟨c, hc0, hc⟩ :=
    NormedField.exists_norm_lt L (show (0 : ℝ) < 1 / (B * C + 1) by positivity)
  have hcK : ‖c‖ * (B * C + 1) ≤ 1 := by
    rw [lt_div_iff₀ (by positivity)] at hc
    exact hc.le
  refine ⟨c, norm_pos_iff.1 hc0, fun x hxB i => ?_⟩
  have hr : b.repr x i = ∑ k, h (b k) x * b.repr (w k) i := by
    conv_lhs => rw [hx x]
    simp [map_sum, Finsupp.finset_sum_apply]
  have hbound : ‖b.repr x i‖ ≤ B * C := by
    rw [hr]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k _ => ?_
    rw [norm_mul]
    exact mul_le_mul (hxB k) (hCki k i) (norm_nonneg _) hB
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
  nlinarith [norm_nonneg c, norm_nonneg (b.repr x i)]

theorem stExists_of_stSandwich : StSandwich → StExists := by
  intro hSw
  unfold StExists ForAll
  intro L _ _ _ _ s hs δ hδ V _ _ _ h hh
  obtain ⟨m, b, hb⟩ := exists_basis_herm_le_one hs hh
  obtain ⟨c, hc0, hc⟩ := exists_scale hh ‖δ‖ (norm_nonneg _) b
  let S : Set (AddSubgroup V) :=
    {Λ | (∀ a : L, ‖a‖ ≤ 1 → ∀ x ∈ Λ, a • x ∈ Λ) ∧ ∀ x ∈ Λ, ‖h x x‖ ≤ 1}
  have hlat0 : IsLat L (ball b) := ⟨m, b, fun _ => Iff.rfl⟩
  have hS0 : ball b ∈ S :=
    ⟨fun a ha x hx => IsLat.smul_mem hlat0 ha hx, fun x hx => norm_herm_ball_le_one hs hh b hb hx⟩
  have hchain : ∀ C ⊆ S, IsChain (· ≤ ·) C → ∀ y ∈ C, ∃ ub ∈ S, ∀ z ∈ C, z ≤ ub := by
    intro C hCS hC y hy
    have hmem : ∀ x, x ∈ sSup C ↔ ∃ t ∈ C, x ∈ t := fun x =>
      AddSubgroup.mem_sSup_of_directedOn ⟨y, hy⟩ hC.directedOn
    refine ⟨sSup C, ⟨fun a ha x hx => ?_, fun x hx => ?_⟩, fun z hz => le_sSup hz⟩
    · obtain ⟨t, ht, hxt⟩ := (hmem x).1 hx
      exact (hmem _).2 ⟨t, ht, (hCS ht).1 a ha x hxt⟩
    · obtain ⟨t, ht, hxt⟩ := (hmem x).1 hx
      exact (hCS ht).2 x hxt
  obtain ⟨M, hM0, hMax⟩ := zorn_le_nonempty₀ S hchain (ball b) hS0
  have hMlat : IsLat L M := by
    refine hSw L V (ball b) M c hlat0 hc0 (fun x hx => hc x fun j => ?_) (fun x => ?_) hMax.prop.1
    · exact norm_herm_le_delta hδ hh hMax.prop.1 hMax.prop.2 (hM0 (basis_mem_ball b j)) hx
    · obtain ⟨a, ha, hax⟩ := ball_absorbing b x
      exact ⟨a, ha, hM0 hax⟩
  refine ⟨M, hMlat, hMax.prop.2, fun Λ' hL hI hle => ?_⟩
  exact le_antisymm (hMax.2 ⟨fun a ha x hx => IsLat.smul_mem hL ha hx, hI⟩ hle) hle

end GlobalTheory.CompanionTheory.RgFl.MaxLat

end
