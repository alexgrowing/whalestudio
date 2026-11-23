import Mathlib

open Filter Topology

namespace GlobalTheory.CosetEuler

variable {G ι : Type} [Group G] {L : ι → Type} [∀ v, Group (L v)]

section
variable (e : ∀ v, L v →* G) (p : ∀ v, G →* L v) (K : ∀ v, Subgroup (L v)) (J H : Subgroup G)

def offSet (T : Finset ι) : Set (H ⧸ J.subgroupOf H) :=
  {y | ∀ v ∉ T, p v ((y.out : H) : G) ∈ K v}

def shift (v : ι) (g : G) : G := g * (e v (p v g))⁻¹

end

theorem e_mem_J {e : ∀ v, L v →* G} {p : ∀ v, G →* L v} {K : ∀ v, Subgroup (L v)} {J H : Subgroup G}
    (hpe : ∀ v a, p v (e v a) = a) (hpe' : ∀ u v, u ≠ v → ∀ a, p u (e v a) = 1)
    (he : ∀ v a, e v a ∈ H) (hJ : ∀ g ∈ H, g ∈ J ↔ ∀ v, p v g ∈ K v)
    (v : ι) (k : L v) (hk : k ∈ K v) : e v k ∈ J := by
  refine (hJ _ (he v k)).2 fun u => ?_
  by_cases h : u = v
  · subst h; rw [hpe]; exact hk
  · rw [hpe' u v h]; exact (K u).one_mem

theorem cls_eq {p : ∀ v, G →* L v} {K : ∀ v, Subgroup (L v)} {J H : Subgroup G}
    (hJ : ∀ g ∈ H, g ∈ J ↔ ∀ v, p v g ∈ K v) (g h : H) :
    ((g : H ⧸ J.subgroupOf H) = h) ↔ ∀ v, (p v g)⁻¹ * p v h ∈ K v := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, hJ _ (g⁻¹ * h).2]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]

theorem out_mul {J H : Subgroup G} (hJH : J ≤ H) (g : H) :
    ∃ k ∈ J, (((g : H ⧸ J.subgroupOf H).out : H) : G) = g * k := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (J.subgroupOf H) g
  exact ⟨((k : H) : G), Subgroup.mem_subgroupOf.1 k.2, by rw [hk]; rfl⟩

theorem inv_out {E : Type} {J H : Subgroup G} (hJH : J ≤ H) (f : G → E)
    (hf : ∀ g ∈ H, ∀ k ∈ J, f (g * k) = f g) (g : H) :
    f (((g : H ⧸ J.subgroupOf H).out : H) : G) = f g := by
  obtain ⟨k, hk, h⟩ := out_mul hJH g
  rw [h, hf _ g.2 _ hk]

theorem mem_offSet_mk {p : ∀ v, G →* L v} {K : ∀ v, Subgroup (L v)} {J H : Subgroup G}
    (hJH : J ≤ H) (hJ : ∀ g ∈ H, g ∈ J ↔ ∀ v, p v g ∈ K v) (T : Finset ι) (g : H) :
    (g : H ⧸ J.subgroupOf H) ∈ offSet p K J H T ↔ ∀ v ∉ T, p v g ∈ K v := by
  obtain ⟨k, hk, h⟩ := out_mul hJH g
  have hk' := (hJ k (hJH hk)).1 hk
  simp only [offSet, Set.mem_setOf_eq, h, map_mul]
  exact forall₂_congr fun v _ => Subgroup.mul_mem_cancel_right _ (hk' v)

theorem p_shift_self {e : ∀ v, L v →* G} {p : ∀ v, G →* L v} (hpe : ∀ v a, p v (e v a) = a)
    (v : ι) (g : G) : p v (shift e p v g) = 1 := by
  simp [shift, hpe]

theorem p_shift_ne {e : ∀ v, L v →* G} {p : ∀ v, G →* L v}
    (hpe' : ∀ u v, u ≠ v → ∀ a, p u (e v a) = 1) {u v : ι} (h : u ≠ v) (g : G) :
    p u (shift e p v g) = p u g := by
  simp [shift, hpe' u v h]

theorem shift_mem {e : ∀ v, L v →* G} {p : ∀ v, G →* L v} {H : Subgroup G}
    (he : ∀ v a, e v a ∈ H) (v : ι) {g : G} (hg : g ∈ H) : shift e p v g ∈ H :=
  H.mul_mem hg (H.inv_mem (he _ _))

theorem shift_val {E : Type} {e : ∀ v, L v →* G} {p : ∀ v, G →* L v} {K : ∀ v, Subgroup (L v)}
    {J H : Subgroup G}
    (hpe : ∀ v a, p v (e v a) = a) (hpe' : ∀ u v, u ≠ v → ∀ a, p u (e v a) = 1)
    (he : ∀ v a, e v a ∈ H) (hJ : ∀ g ∈ H, g ∈ J ↔ ∀ v, p v g ∈ K v) (f : G → E)
    (hf : ∀ g ∈ H, ∀ k ∈ J, f (g * k) = f g) (v : ι) {g : G} (hg : g ∈ H) (hv : p v g ∈ K v) :
    f (shift e p v g) = f g := by
  rw [shift, ← map_inv]
  exact hf g hg _ (e_mem_J hpe hpe' he hJ v _ ((K v).inv_mem hv))

noncomputable def stepMap (e : ∀ v, L v →* G) (p : ∀ v, G →* L v) (K : ∀ v, Subgroup (L v)) (J H : Subgroup G)
    (he : ∀ v a, e v a ∈ H) (T : Finset ι) (v : ι) :
    offSet p K J H T × (L v ⧸ K v) → H ⧸ J.subgroupOf H :=
  fun x => ((⟨shift e p v ((x.1.1.out : H) : G) * e v x.2.out,
    H.mul_mem (shift_mem he v (x.1.1.out).2) (he _ _)⟩ : H) : H ⧸ J.subgroupOf H)

section step
variable [DecidableEq ι] {e : ∀ v, L v →* G} {p : ∀ v, G →* L v} {K : ∀ v, Subgroup (L v)} {J H : Subgroup G}
    (hJH : J ≤ H) (hpe : ∀ v a, p v (e v a) = a) (hpe' : ∀ u v, u ≠ v → ∀ a, p u (e v a) = 1)
    (he : ∀ v a, e v a ∈ H) (hJ : ∀ g ∈ H, g ∈ J ↔ ∀ v, p v g ∈ K v)
include hJH hpe hpe' he hJ

theorem stepMap_mem (T : Finset ι) (v : ι) (x : offSet p K J H T × (L v ⧸ K v)) :
    stepMap e p K J H he T v x ∈ offSet p K J H (insert v T) := by
  refine (mem_offSet_mk hJH hJ _ _).2 fun u hu => ?_
  rw [Finset.mem_insert, not_or] at hu
  simp only [map_mul, p_shift_ne hpe' hu.1, hpe' u v hu.1, mul_one]
  exact x.1.2 u hu.2

theorem stepMap_injective (T : Finset ι) (v : ι) (hv : v ∉ T) :
    Function.Injective (stepMap e p K J H he T v) := by
  rintro ⟨y1, a1⟩ ⟨y2, a2⟩ h
  have h' := (cls_eq hJ _ _).1 h
  have ha : a1 = a2 := by
    have := h' v
    simp only [map_mul, p_shift_self hpe, hpe, one_mul] at this
    rw [← QuotientGroup.out_eq' a1, ← QuotientGroup.out_eq' a2]
    exact QuotientGroup.eq.2 this
  have hy : y1 = y2 := by
    apply Subtype.ext
    rw [← QuotientGroup.out_eq' y1.1, ← QuotientGroup.out_eq' y2.1]
    refine (cls_eq hJ _ _).2 fun u => ?_
    rcases eq_or_ne u v with rfl | hu
    · exact (K u).mul_mem ((K u).inv_mem (y1.2 u hv)) (y2.2 u hv)
    · have := h' u
      simpa only [map_mul, p_shift_ne hpe' hu, hpe' u v hu, mul_one] using this
  exact Prod.ext hy ha

theorem mem_range_stepMap (T : Finset ι) (v : ι) (y : H ⧸ J.subgroupOf H)
    (hy : y ∈ offSet p K J H (insert v T)) : y ∈ Set.range (stepMap e p K J H he T v) := by
  set g : H := y.out with hg
  let h : H := ⟨shift e p v g, shift_mem he v g.2⟩
  have hh : (h : H ⧸ J.subgroupOf H) ∈ offSet p K J H T := by
    refine (mem_offSet_mk hJH hJ _ _).2 fun u hu => ?_
    rcases eq_or_ne u v with rfl | huv
    · show p u (shift e p u g) ∈ K u
      rw [p_shift_self hpe]; exact (K u).one_mem
    · show p u (shift e p v g) ∈ K u
      rw [p_shift_ne hpe' huv]
      exact hy u (by simp [huv, hu])
  refine ⟨(⟨_, hh⟩, (p v g : L v ⧸ K v)), ?_⟩
  rw [← QuotientGroup.out_eq' y]
  refine (cls_eq hJ _ _).2 fun u => ?_
  obtain ⟨k, hk, hk'⟩ := out_mul hJH h
  rcases eq_or_ne u v with rfl | huv
  · simp only [map_mul, p_shift_self hpe, hpe, one_mul]
    exact QuotientGroup.eq.1 (QuotientGroup.out_eq' (p u g : L u ⧸ K u))
  · simp only [map_mul, p_shift_ne hpe' huv, hpe' u v huv, mul_one, hk']
    have e1 : p u (h : G) = p u (y.out : G) := p_shift_ne hpe' huv _
    simp only [mul_inv_rev, mul_assoc, e1, inv_mul_cancel, mul_one]
    exact (K u).inv_mem ((hJ k (hJH hk)).1 hk u)

theorem comp_stepMap {E : Type} [Zero E] (f : G → E) (hf : ∀ g ∈ H, ∀ k ∈ J, f (g * k) = f g)
    (T : Finset ι) (v : ι) (x : offSet p K J H T × (L v ⧸ K v)) :
    ((offSet p K J H (insert v T)).indicator (fun y => f ((y.out : H) : G)) ∘
      stepMap e p K J H he T v) x = f (shift e p v ((x.1.1.out : H) : G) * e v x.2.out) := by
  simp only [Function.comp, Set.indicator_of_mem (stepMap_mem hJH hpe hpe' he hJ T v x)]
  exact inv_out hJH f hf _

theorem zero_off_stepMap {E : Type} [Zero E] (f : G → E) (T : Finset ι) (v : ι) :
    ∀ x ∉ Set.range (stepMap e p K J H he T v),
      (offSet p K J H (insert v T)).indicator (fun y => f ((y.out : H) : G)) x = 0 :=
  fun x hx => Set.indicator_of_notMem (fun h => hx (mem_range_stepMap hJH hpe hpe' he hJ T v x h)) _

theorem hasSum_step {E : Type} [NormedField E] (f : G → E)
    (hf : ∀ g ∈ H, ∀ k ∈ J, f (g * k) = f g)
    (c : E) (T : Finset ι) (v : ι) (hv : v ∉ T)
    (hfib : ∀ g ∈ H, p v g = 1 → HasSum (fun a : L v ⧸ K v => f (g * e v a.out)) (c * f g))
    {s : E} (hs : HasSum ((offSet p K J H T).indicator fun y => f ((y.out : H) : G)) s)
    (hsum : Summable ((offSet p K J H (insert v T)).indicator fun y => f ((y.out : H) : G))) :
    HasSum ((offSet p K J H (insert v T)).indicator fun y => f ((y.out : H) : G)) (c * s) := by
  have hinj := stepMap_injective hJH hpe hpe' he hJ T v hv
  have hzero := zero_off_stepMap hJH hpe hpe' he hJ f T v
  have h1 := (hinj.hasSum_iff hzero).2 hsum.hasSum
  have h2 : HasSum (fun y : offSet p K J H T => c * f ((y.1.out : H) : G))
      (∑' y, (offSet p K J H (insert v T)).indicator (fun y => f ((y.out : H) : G)) y) := by
    refine h1.prod_fiberwise fun y => ?_
    have := hfib _ (shift_mem he v (y.1.out).2) (p_shift_self hpe v _)
    rw [shift_val hpe hpe' he hJ f hf v (y.1.out).2 (y.2 v hv)] at this
    simpa only [comp_stepMap hJH hpe hpe' he hJ f hf] using this
  have h3 : HasSum (fun y : offSet p K J H T => c * f ((y.1.out : H) : G)) (c * s) :=
    (hasSum_subtype_iff_indicator.2 hs).mul_left c
  rw [h2.unique h3] at h1
  exact (hinj.hasSum_iff hzero).1 h1

theorem summable_step (f : G → ℝ) (hf0 : ∀ g ∈ H, 0 ≤ f g)
    (hf : ∀ g ∈ H, ∀ k ∈ J, f (g * k) = f g)
    (c : ℝ) (T : Finset ι) (v : ι) (hv : v ∉ T)
    (hfib : ∀ g ∈ H, p v g = 1 → HasSum (fun a : L v ⧸ K v => f (g * e v a.out)) (c * f g))
    {s : ℝ} (hs : HasSum ((offSet p K J H T).indicator fun y => f ((y.out : H) : G)) s) :
    Summable ((offSet p K J H (insert v T)).indicator fun y => f ((y.out : H) : G)) := by
  have hinj := stepMap_injective hJH hpe hpe' he hJ T v hv
  have hzero := zero_off_stepMap hJH hpe hpe' he hJ f T v
  refine (hinj.summable_iff hzero).1 ?_
  have hnn : 0 ≤ (offSet p K J H (insert v T)).indicator (fun y => f ((y.out : H) : G)) ∘
      stepMap e p K J H he T v :=
    fun x => Set.indicator_nonneg (fun y _ => hf0 _ (y.out).2) _
  have hfib' : ∀ y : offSet p K J H T, HasSum
      (fun a : L v ⧸ K v => f (shift e p v ((y.1.out : H) : G) * e v a.out))
      (c * f ((y.1.out : H) : G)) := fun y => by
    have := hfib _ (shift_mem he v (y.1.out).2) (p_shift_self hpe v _)
    rwa [shift_val hpe hpe' he hJ f hf v (y.1.out).2 (y.2 v hv)] at this
  refine (summable_prod_of_nonneg hnn).2 ⟨fun y => ?_, ?_⟩
  · simpa only [comp_stepMap hJH hpe hpe' he hJ f hf] using (hfib' y).summable
  · simp only [comp_stepMap hJH hpe hpe' he hJ f hf, fun y => (hfib' y).tsum_eq]
    exact ((hasSum_subtype_iff_indicator.2 hs).mul_left c).summable
end step

section ind
variable [DecidableEq ι] {e : ∀ v, L v →* G} {p : ∀ v, G →* L v} {K : ∀ v, Subgroup (L v)}
    {J H : Subgroup G}
    (hJH : J ≤ H) (hpe : ∀ v a, p v (e v a) = a) (hpe' : ∀ u v, u ≠ v → ∀ a, p u (e v a) = 1)
    (he : ∀ v a, e v a ∈ H) (hJ : ∀ g ∈ H, g ∈ J ↔ ∀ v, p v g ∈ K v)
include hJH hJ

theorem offSet_empty : offSet p K J H ∅ = {((1 : H) : H ⧸ J.subgroupOf H)} := by
  ext y
  rw [Set.mem_singleton_iff, ← QuotientGroup.out_eq' y, mem_offSet_mk hJH hJ, cls_eq hJ]
  simp

theorem hasSum_base {E : Type} [AddCommMonoid E] [TopologicalSpace E] (f : G → E)
    (hf : ∀ g ∈ H, ∀ k ∈ J, f (g * k) = f g) :
    HasSum ((offSet p K J H ∅).indicator fun y => f ((y.out : H) : G)) (f 1) := by
  rw [offSet_empty hJH hJ]
  have := hasSum_single
    (f := ({((1 : H) : H ⧸ J.subgroupOf H)} : Set (H ⧸ J.subgroupOf H)).indicator
      fun y => f ((y.out : H) : G))
    ((1 : H) : H ⧸ J.subgroupOf H) (fun b hb => Set.indicator_of_notMem (Set.mem_singleton_iff.not.2 hb) _)
  rw [Set.indicator_of_mem (Set.mem_singleton _), inv_out hJH f hf] at this
  exact this

include hpe hpe' he

theorem hasSum_offSet_nonneg (f : G → ℝ) (hf0 : ∀ g ∈ H, 0 ≤ f g)
    (hf : ∀ g ∈ H, ∀ k ∈ J, f (g * k) = f g) (A : ι → ℝ)
    (hA : ∀ v, ∀ g ∈ H, p v g = 1 → HasSum (fun a : L v ⧸ K v => f (g * e v a.out)) (A v * f g))
    (T : Finset ι) :
    HasSum ((offSet p K J H T).indicator fun y => f ((y.out : H) : G)) ((∏ v ∈ T, A v) * f 1) := by
  induction T using Finset.induction_on with
  | empty => simpa using hasSum_base hJH hJ f hf
  | @insert v T hv ih =>
    rw [Finset.prod_insert hv, mul_assoc]
    exact hasSum_step hJH hpe hpe' he hJ f hf (A v) T v hv (hA v) ih
      (summable_step hJH hpe hpe' he hJ f hf0 hf (A v) T v hv (hA v) ih)

theorem hasSum_offSet_summable {E : Type} [NormedField E] [CompleteSpace E] (f : G → E)
    (hf : ∀ g ∈ H, ∀ k ∈ J, f (g * k) = f g) (Z : ι → E)
    (hZ : ∀ v, ∀ g ∈ H, p v g = 1 → HasSum (fun a : L v ⧸ K v => f (g * e v a.out)) (Z v * f g))
    (hsum : Summable fun y : H ⧸ J.subgroupOf H => f ((y.out : H) : G)) (T : Finset ι) :
    HasSum ((offSet p K J H T).indicator fun y => f ((y.out : H) : G)) ((∏ v ∈ T, Z v) * f 1) := by
  induction T using Finset.induction_on with
  | empty => simpa using hasSum_base hJH hJ f hf
  | @insert v T hv ih =>
    rw [Finset.prod_insert hv, mul_assoc]
    exact hasSum_step hJH hpe hpe' he hJ f hf (Z v) T v hv (hZ v) ih (hsum.indicator _)
end ind

theorem hasSum_cosets_eulerProduct : ∀ {G ι : Type} [Group G] {L : ι → Type} [∀ v, Group (L v)] (e : ∀ v, L v →* G) (p : ∀ v, G →* L v) (K : ∀ v, Subgroup (L v)) (J H : Subgroup G), J ≤ H → (∀ v a, p v (e v a) = a) → (∀ u v, u ≠ v → ∀ a, p u (e v a) = 1) → (∀ v a, e v a ∈ H) → (∀ v a g, p v g = 1 → Commute (e v a) g) → (∀ g ∈ H, g ∈ J ↔ ∀ v, p v g ∈ K v) → (∀ g ∈ H, {v | p v g ∉ K v}.Finite) → ∀ (Ψ : G → ℂ) (Φ : G → ℝ) (Z : ι → ℂ) (A : ι → ℝ) (z : ℂ), (∀ g ∈ H, ∀ k ∈ J, Ψ (g * k) = Ψ g) → (∀ g ∈ H, ∀ k ∈ J, Φ (g * k) = Φ g) → (∀ g ∈ H, ‖Ψ g‖ ≤ Φ g) → (∀ v, ∀ g ∈ H, p v g = 1 → HasSum (fun a : L v ⧸ K v => Ψ (g * e v a.out)) (Z v * Ψ g)) → (∀ v, ∀ g ∈ H, p v g = 1 → HasSum (fun a : L v ⧸ K v => Φ (g * e v a.out)) (A v * Φ g)) → Summable (fun v => A v - 1) → HasProd Z z → HasSum (fun y : H ⧸ J.subgroupOf H => Ψ (y.out : H)) (z * Ψ 1) := by
  intro G ι _ L _ e p K J H hJH hpe hpe' he _ hJ hfin Ψ Φ Z A z hΨ hΦ hΨΦ hZ hA hA1 hz
  classical
  have hΦ0 : ∀ g ∈ H, 0 ≤ Φ g := fun g hg => (norm_nonneg _).trans (hΨΦ g hg)
  have hphi := hasSum_offSet_nonneg hJH hpe hpe' he hJ Φ hΦ0 hΦ A hA
  have hsA : Summable (fun v => |A v - 1|) := hA1.abs
  have hφ : Summable fun y : H ⧸ J.subgroupOf H => Φ ((y.out : H) : G) := by
    refine summable_of_sum_le (c := Real.exp (∑' v, |A v - 1|) * Φ 1)
      (fun y => hΦ0 _ (y.out).2) fun u => ?_
    let T : Finset ι := u.biUnion fun y => (hfin _ (y.out).2).toFinset
    have hu : ∀ y ∈ u, y ∈ offSet p K J H T := fun y hy v hv => by
      by_contra h
      exact hv (Finset.mem_biUnion.2 ⟨y, hy, (Set.Finite.mem_toFinset _).2 h⟩)
    calc ∑ y ∈ u, Φ ((y.out : H) : G)
        = ∑ y ∈ u, (offSet p K J H T).indicator (fun y => Φ ((y.out : H) : G)) y :=
          Finset.sum_congr rfl fun y hy =>
            (Set.indicator_of_mem (hu y hy) (fun y => Φ ((y.out : H) : G))).symm
      _ ≤ (∏ v ∈ T, A v) * Φ 1 :=
          sum_le_hasSum u (fun y _ => Set.indicator_nonneg (fun y _ => hΦ0 _ (y.out).2) _) (hphi T)
      _ ≤ Real.exp (∑' v, |A v - 1|) * Φ 1 := by
        refine mul_le_mul_of_nonneg_right ?_ (hΦ0 1 H.one_mem)
        calc ∏ v ∈ T, A v ≤ ∏ v ∈ T, |A v| := (le_abs_self _).trans (Finset.abs_prod _ _).le
          _ ≤ ∏ v ∈ T, Real.exp |A v - 1| :=
              Finset.prod_le_prod (fun v _ => abs_nonneg _) fun v _ => by
                have h1 := Real.add_one_le_exp |A v - 1|
                have h2 := abs_sub_abs_le_abs_sub (A v) 1
                rw [abs_one] at h2
                linarith
          _ = Real.exp (∑ v ∈ T, |A v - 1|) := (Real.exp_sum _ _).symm
          _ ≤ Real.exp (∑' v, |A v - 1|) :=
              Real.exp_le_exp.2 (hsA.sum_le_tsum T fun v _ => abs_nonneg _)
  have hψ : Summable fun y : H ⧸ J.subgroupOf H => Ψ ((y.out : H) : G) :=
    Summable.of_norm_bounded hφ fun y => hΨΦ _ (y.out).2
  have hpsi := hasSum_offSet_summable hJH hpe hpe' he hJ Ψ hΨ Z hZ hψ
  have hlim : Tendsto (fun T : Finset ι =>
      ∑' y, (offSet p K J H T).indicator (fun y => Ψ ((y.out : H) : G)) y) atTop
      (𝓝 (∑' y : H ⧸ J.subgroupOf H, Ψ ((y.out : H) : G))) := by
    refine tendsto_tsum_of_dominated_convergence hφ (fun y => ?_)
      (Eventually.of_forall fun T y => ?_)
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (hfin _ (y.out).2).toFinset] with T hT
      refine (Set.indicator_of_mem (show y ∈ offSet p K J H T from fun v hv => ?_)
        (fun y => Ψ ((y.out : H) : G))).symm
      by_contra h
      exact hv (hT ((Set.Finite.mem_toFinset _).2 h))
    · exact (norm_indicator_le_norm_self _ _).trans (hΨΦ _ (y.out).2)
  have hlim2 : Tendsto (fun T : Finset ι =>
      ∑' y, (offSet p K J H T).indicator (fun y => Ψ ((y.out : H) : G)) y) atTop
      (𝓝 (z * Ψ 1)) := by
    simp only [fun T => (hpsi T).tsum_eq]
    exact (hz : Tendsto (fun s : Finset ι => ∏ b ∈ s, Z b) atTop (𝓝 z)).mul_const _
  rw [← tendsto_nhds_unique hlim hlim2]
  exact hψ.hasSum

end GlobalTheory.CosetEuler
