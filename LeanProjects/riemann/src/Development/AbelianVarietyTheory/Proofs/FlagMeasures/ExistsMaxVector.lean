import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.MassOrth

section Abstract

variable {K V Γ : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)

def biInt : Subring K where
  carrier := {k | v k ≤ 1 ∧ v (star k) ≤ 1}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    rintro a b ⟨a1, a2⟩ ⟨b1, b2⟩
    exact ⟨v.map_add_le a1 b1, by rw [star_add]; exact v.map_add_le a2 b2⟩
  mul_mem' := by
    rintro a b ⟨a1, a2⟩ ⟨b1, b2⟩
    exact ⟨by rw [map_mul]; exact mul_le_one' a1 b1,
      by rw [star_mul, map_mul]; exact mul_le_one' b2 a2⟩
  neg_mem' := by
    rintro a ⟨a1, a2⟩
    exact ⟨by simpa using a1, by simpa using a2⟩

theorem mem_biInt {k : K} : k ∈ biInt v ↔ v k ≤ 1 ∧ v (star k) ≤ 1 := Iff.rfl

theorem bound_of_span (h : V →ₗ⋆[K] V →ₗ[K] K) (T : Set V) (m : Γ)
    (hT : ∀ x ∈ T, ∀ y ∈ T, v (h x y) ≤ m) :
    ∀ x ∈ Submodule.span (biInt v) T, ∀ y ∈ Submodule.span (biInt v) T, v (h x y) ≤ m := by
  have h1 : ∀ x ∈ T, ∀ y ∈ Submodule.span (biInt v) T, v (h x y) ≤ m := by
    intro x hx y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hT x hx y hy
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact v.map_add_le ha hb
    | smul r a _ ha =>
      rw [Subring.smul_def, map_smul, smul_eq_mul, map_mul]
      exact (mul_le_mul' r.2.1 ha).trans (by simp)
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem x hx => exact h1 x hx y hy
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply]; exact v.map_add_le ha hb
  | smul r a _ ha =>
    rw [Subring.smul_def, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul]
    exact (mul_le_mul' r.2.2 ha).trans (by simp)

theorem exists_max_vector (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (θ : K) (hθ : θ ∈ biInt v)
    (hθ' : v (θ - star θ) = 1) (Λ : Submodule (biInt v) V) (hΛ : Λ.FG) :
    ∃ x ∈ Λ, ∀ y ∈ Λ, ∀ z ∈ Λ, v (h y z) ≤ v (h x x) := by
  obtain ⟨T, rfl⟩ := hΛ
  rcases T.eq_empty_or_nonempty with rfl | hT
  · refine ⟨0, Submodule.zero_mem _, fun y hy z hz => ?_⟩
    have : y = 0 := by simpa using hy
    simp [this]
  obtain ⟨⟨x, y⟩, hxy, hmax⟩ := (T ×ˢ T).exists_max_image (fun p => v (h p.1 p.2)) (hT.product hT)
  obtain ⟨hx, hy⟩ := Finset.mem_product.1 hxy
  have hb := bound_of_span v h (T : Set V) (v (h x y))
    (fun a ha b hb => hmax (a, b) (Finset.mem_product.2 ⟨ha, hb⟩))
  by_contra hcon
  have hlt : ∀ w ∈ Submodule.span (biInt v) (T : Set V), v (h w w) < v (h x y) := by
    intro w hw
    by_contra hn
    exact hcon ⟨w, hw, fun a ha b hb' => (hb a ha b hb').trans (not_lt.1 hn)⟩
  have hx' : x ∈ Submodule.span (biInt v) (T : Set V) := Submodule.subset_span hx
  have hy' : y ∈ Submodule.span (biInt v) (T : Set V) := Submodule.subset_span hy
  have hyx : h y x = star (h x y) := (hs.eq x y).symm
  have key : ∀ c ∈ biInt v, v (c * h x y + star c * star (h x y)) < v (h x y) := by
    intro c hc
    have hcy : c • y ∈ Submodule.span (biInt v) (T : Set V) :=
      Submodule.smul_mem _ (⟨c, hc⟩ : biInt v) hy'
    have e : c * h x y + star c * star (h x y) =
        h (x + c • y) (x + c • y) - h x x - h (c • y) (c • y) := by
      simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
        RingHom.id_apply, hyx, starRingEnd_apply]
      ring
    rw [e]
    exact v.map_sub_lt (v.map_sub_lt (hlt _ (Submodule.add_mem _ hx' hcy)) (hlt _ hx')) (hlt _ hcy)
  have k1 := key 1 (biInt v).one_mem
  have k2 := key θ hθ
  have k3 : v (star θ * (1 * h x y + star 1 * star (h x y))) < v (h x y) := by
    rw [map_mul]
    exact lt_of_le_of_lt ((mul_le_mul' hθ.2 le_rfl).trans (by simp)) k1
  have k4 := v.map_sub_lt k2 k3
  have e : θ * h x y + star θ * star (h x y) - star θ * (1 * h x y + star 1 * star (h x y)) =
      (θ - star θ) * h x y := by
    rw [star_one]; ring
  rw [e, map_mul, hθ', one_mul] at k4
  exact lt_irrefl _ k4

theorem exists_orth_gens [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (θ : K)
    (hθ : θ ∈ biInt v) (hθ' : v (θ - star θ) = 1) (n : ℕ) :
    ∀ (Λ : Submodule (biInt v) V), Λ.FG → Module.finrank K (Submodule.span K (Λ : Set V)) = n →
      (∀ x ∈ Λ, (∀ y ∈ Λ, h x y = 0) → x = 0) →
      ∃ (m : ℕ) (e : Fin m → V), (∀ i l, i ≠ l → h (e i) (e l) = 0) ∧ (∀ i, h (e i) (e i) ≠ 0) ∧
        Submodule.span (biInt v) (Set.range e) = Λ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Λ hfg hn hnd
  obtain ⟨x, hx, hmax⟩ := exists_max_vector v h hs θ hθ hθ' Λ hfg
  by_cases h0 : h x x = 0
  · refine ⟨0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, ?_⟩
    symm
    rw [Set.range_eq_empty, Submodule.span_empty, eq_bot_iff]
    intro y hy
    refine hnd y hy fun z hz => ?_
    have := hmax y hy z hz
    rw [h0, map_zero] at this
    exact v.zero_iff.1 (le_antisymm this zero_le)
  have hv0 : 0 < v (h x x) := zero_lt_iff.2 (v.ne_zero_iff.2 h0)
  have hxx : star (h x x) = h x x := hs.eq x x
  have hc : ∀ y ∈ Λ, h x y / h x x ∈ biInt v := by
    intro y hy
    refine ⟨?_, ?_⟩
    · rw [map_div₀, div_le_one₀ hv0]; exact hmax x hx y hy
    · have : star (h x y) = h y x := hs.eq x y
      rw [star_div₀, hxx, this, map_div₀, div_le_one₀ hv0]; exact hmax y hy x hx
  let p : V →ₗ[K] V := LinearMap.id - (LinearMap.toSpanSingleton K V x).comp ((h x x)⁻¹ • h x)
  have hp : ∀ y, p y = y - (h x y / h x x) • x := by
    intro y; simp [p, div_eq_inv_mul]
  have hxp : ∀ y, h x (p y) = 0 := by
    intro y; rw [hp, map_sub, map_smul, smul_eq_mul]; field_simp; ring
  have hcx : ∀ y ∈ Λ, (h x y / h x x) • x ∈ Λ := fun y hy =>
    Λ.smul_mem (⟨_, hc y hy⟩ : biInt v) hx
  let Λ' : Submodule (biInt v) V := Λ.map (p.restrictScalars (biInt v))
  have hle : Λ' ≤ Λ := by
    rintro _ ⟨y, hy, rfl⟩
    change p y ∈ Λ
    rw [hp]; exact Λ.sub_mem hy (hcx y hy)
  have horth : ∀ y ∈ Λ', h x y = 0 := by
    rintro _ ⟨y, hy, rfl⟩
    exact hxp y
  have horth' : ∀ y ∈ Λ', h y x = 0 := by
    intro y hy
    have : star (h x y) = h y x := hs.eq x y
    rw [← this, horth y hy, star_zero]
  have hlt : Submodule.span K (Λ' : Set V) < Submodule.span K (Λ : Set V) := by
    refine lt_of_le_of_ne (Submodule.span_mono hle) fun heq => h0 ?_
    have h1 : Submodule.span K (Λ' : Set V) ≤ LinearMap.ker (h x) :=
      Submodule.span_le.2 fun y hy => horth y hy
    exact h1 (heq ▸ Submodule.subset_span hx)
  obtain ⟨m, e, he1, he2, he3⟩ := ih _ (hn ▸ Submodule.finrank_lt_finrank_of_lt hlt) Λ'
    (hfg.map _) rfl (by
      intro y hy hyz
      refine hnd y (hle hy) fun z hz => ?_
      have h1 := hyz (p z) ⟨z, hz, rfl⟩
      rw [hp, map_sub, map_smul, horth' y hy] at h1
      simpa using h1)
  have hem : ∀ i, e i ∈ Λ' := fun i => he3 ▸ Submodule.subset_span ⟨i, rfl⟩
  refine ⟨m + 1, Fin.cons x e, ?_, ?_, ?_⟩
  · intro i l hil
    induction i using Fin.cases with
    | zero =>
      induction l using Fin.cases with
      | zero => exact absurd rfl hil
      | succ l => simpa using horth _ (hem l)
    | succ i =>
      induction l using Fin.cases with
      | zero => simpa using horth' _ (hem i)
      | succ l => simpa using he1 i l fun hh => hil (by rw [hh])
  · intro i
    induction i using Fin.cases with
    | zero => simpa using h0
    | succ i => simpa using he2 i
  · rw [Fin.range_cons, Submodule.span_insert, he3]
    refine le_antisymm (sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 hx) hle) fun y hy => ?_
    have e1 : y = (h x y / h x x) • x + p y := by rw [hp]; abel
    rw [e1]
    refine Submodule.add_mem_sup ?_ ⟨y, hy, rfl⟩
    exact Submodule.smul_mem _ (⟨_, hc y hy⟩ : biInt v) (Submodule.mem_span_singleton_self x)

end Abstract

section NumberField

open IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] [StarRing K]

noncomputable def starInt : 𝓞 K →+* 𝓞 K := RingOfIntegers.mapRingHom (starRingEnd K)

omit [NumberField K] in
theorem coe_starInt (s : 𝓞 K) : algebraMap (𝓞 K) K (starInt s) = star (algebraMap (𝓞 K) K s) := rfl

omit [NumberField K] in
theorem mem_hcompl_iff (P : Ideal (𝓞 K)) (hP : P.IsPrime) (s : 𝓞 K) :
    s ∈ hcompl (K := K) P ↔ s ∉ P ∧ starInt s ∉ P := by
  constructor
  · intro hs
    induction hs using Submonoid.closure_induction with
    | mem x hx => exact ⟨hx.1, hx.2 _ (coe_starInt x)⟩
    | one =>
      rw [map_one, and_self]
      exact fun h => hP.ne_top ((Ideal.eq_top_iff_one P).2 h)
    | mul a b _ _ ha hb =>
      rw [map_mul]
      exact ⟨fun h => (hP.mem_or_mem h).elim ha.1 hb.1, fun h => (hP.mem_or_mem h).elim ha.2 hb.2⟩
  · rintro ⟨h1, h2⟩
    refine Submonoid.subset_closure ⟨h1, fun t ht => ?_⟩
    have : t = starInt s := RingOfIntegers.coe_injective (ht.trans (coe_starInt s).symm)
    rwa [this]

theorem int_mem_biInt (w : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) :
    algebraMap (𝓞 K) K a ∈ biInt (w.valuation K) :=
  ⟨w.valuation_le_one a, by rw [← coe_starInt]; exact w.valuation_le_one _⟩

theorem inv_mem_biInt (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K}
    (hs : s ∈ hcompl (K := K) w.asIdeal) :
    algebraMap (𝓞 K) K s ≠ 0 ∧ (algebraMap (𝓞 K) K s)⁻¹ ∈ biInt (w.valuation K) := by
  obtain ⟨h1, h2⟩ := (mem_hcompl_iff _ w.isPrime s).1 hs
  have v1 : w.valuation K (algebraMap (𝓞 K) K s) = 1 := w.valuation_eq_one_iff_notMem.2 h1
  have v2 : w.valuation K (algebraMap (𝓞 K) K (starInt s)) = 1 := w.valuation_eq_one_iff_notMem.2 h2
  refine ⟨fun h => ?_, ?_, ?_⟩
  · rw [h, map_zero] at v1; exact zero_ne_one v1
  · rw [map_inv₀, v1, inv_one]
  · rw [star_inv₀, map_inv₀, ← coe_starInt, v2, inv_one]

theorem exists_denom (w : HeightOneSpectrum (𝓞 K)) {k : K} (hk : k ∈ biInt (w.valuation K)) :
    ∃ s ∈ hcompl (K := K) w.asIdeal, ∃ a : 𝓞 K, algebraMap (𝓞 K) K s * k = algebraMap (𝓞 K) K a := by
  let D : Ideal (𝓞 K) := (1 : Submodule (𝓞 K) K).comap (LinearMap.toSpanSingleton (𝓞 K) K k)
  have hD : ∀ s, s ∈ D ↔ ∃ a : 𝓞 K, algebraMap (𝓞 K) K s * k = algebraMap (𝓞 K) K a := by
    intro s
    simp only [D, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, Submodule.mem_one,
      Algebra.smul_def, eq_comm]
  obtain ⟨n, d, hnd⟩ := w.exists_primeCompl_mul_eq_of_integer k hk.1
  obtain ⟨n', d', hnd'⟩ := w.exists_primeCompl_mul_eq_of_integer (star k) hk.2
  have h1 : ¬ D ≤ w.asIdeal := fun h => d.2 (h ((hD d).2 ⟨n, by rw [mul_comm]; exact hnd⟩))
  have hss : ∀ s : 𝓞 K, starInt (starInt s) = s := fun s =>
    RingOfIntegers.coe_injective (by rw [coe_starInt, coe_starInt, star_star])
  have h2 : ¬ D ≤ w.asIdeal.comap starInt := fun h => d'.2 (by
    have := h ((hD (starInt (d' : 𝓞 K))).2 ⟨starInt n', by
      rw [coe_starInt, coe_starInt, ← hnd', star_mul, star_star]⟩)
    rwa [Ideal.mem_comap, hss] at this)
  have h3 : ¬ ((D : Set (𝓞 K)) ⊆ w.asIdeal ∪ (w.asIdeal.comap starInt : Ideal (𝓞 K))) := by
    rw [Ideal.subset_union]; tauto
  obtain ⟨s, hs, hs'⟩ := Set.not_subset.1 h3
  refine ⟨s, (mem_hcompl_iff _ w.isPrime s).2 ⟨fun h => hs' (Or.inl h), fun h => hs' (Or.inr h)⟩,
    (hD s).1 hs⟩

theorem mem_loc_span_iff {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (w : HeightOneSpectrum (𝓞 K)) (S : Set V) (x : V) :
    x ∈ loc (K := K) w.asIdeal (Submodule.span (𝓞 K) S) ↔
      x ∈ Submodule.span (biInt (w.valuation K)) S := by
  constructor
  · rintro ⟨s, hs, hx⟩
    have h1 : ∀ y ∈ Submodule.span (𝓞 K) S, y ∈ Submodule.span (biInt (w.valuation K)) S := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span hy
      | zero => exact Submodule.zero_mem _
      | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
      | smul r a _ ha =>
        rw [← algebraMap_smul K r a]
        exact Submodule.smul_mem _ (⟨_, int_mem_biInt w r⟩ : biInt (w.valuation K)) ha
    obtain ⟨s0, s1⟩ := inv_mem_biInt w hs
    have h2 : (algebraMap (𝓞 K) K s)⁻¹ • (s • x) ∈ Submodule.span (biInt (w.valuation K)) S :=
      Submodule.smul_mem _ (⟨_, s1⟩ : biInt (w.valuation K)) (h1 _ hx)
    rwa [← algebraMap_smul K s x, inv_smul_smul₀ s0] at h2
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact ⟨1, Submonoid.one_mem _, by simpa using Submodule.subset_span hy⟩
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
    | smul r y _ hy =>
      obtain ⟨t, ht, a, hta⟩ := exists_denom w r.2
      obtain ⟨s, hs, hsy⟩ := hy
      refine ⟨s * t, Submonoid.mul_mem _ hs ht, ?_⟩
      have e : (s * t) • r • y = a • s • y := by
        rw [Subring.smul_def, mul_smul, ← algebraMap_smul K t, smul_smul (algebraMap (𝓞 K) K t), hta,
          algebraMap_smul, smul_comm]
      rw [e]
      exact Submodule.smul_mem _ a hsy

theorem mem_locR_iff (w : HeightOneSpectrum (𝓞 K)) (k : K) :
    k ∈ locR (K := K) w.asIdeal ↔ k ∈ biInt (w.valuation K) := by
  rw [locR, Submodule.one_eq_span, mem_loc_span_iff, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    rw [Subring.smul_def, smul_eq_mul, mul_one]; exact a.2
  · intro hk
    exact ⟨⟨k, hk⟩, by rw [Subring.smul_def, smul_eq_mul, mul_one]⟩

end NumberField

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ (M : Submodule (𝓞 K) V), Submodule.IsLattice K M → ∀ P : Ideal (𝓞 K), P.IsMaximal → ∃ b : Module.Basis (Fin (Module.finrank K V)) K V, (∀ i l, i ≠ l → h (b i) (b l) = 0) ∧ ∀ x, x ∈ loc (K := K) P M ↔ ∀ i, b.repr x i ∈ locR (K := K) P := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hnd M hM P hP
  let w : IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
    ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)⟩
  obtain ⟨θ, t, ht, hθ⟩ := hK.2.2 P hP
  obtain ⟨S, hS⟩ := hM.fg
  have hsp := hM.span_eq_top
  let Λ : Submodule (biInt (w.valuation K)) V := Submodule.span _ (S : Set V)
  have hΛ : ∀ x, x ∈ loc (K := K) P M ↔ x ∈ Λ := fun x => by
    rw [← hS]; exact mem_loc_span_iff w _ x
  have htop : Submodule.span K (Λ : Set V) = ⊤ := by
    rw [eq_top_iff, ← hsp]
    refine Submodule.span_mono fun x hx => (hΛ x).1 ⟨1, Submonoid.one_mem _, by simpa using hx⟩
  obtain ⟨m, e, he1, he2, he3⟩ := exists_orth_gens (w.valuation K) h hs (algebraMap (𝓞 K) K θ)
    (int_mem_biInt w θ) (by
      rw [← ht, ← map_sub]; exact w.valuation_eq_one_iff_notMem.2 hθ) _ Λ
    (Submodule.fg_span S.finite_toSet) rfl (by
      intro x _ hx
      refine hnd.1 x fun y => ?_
      have h1 : Submodule.span K (Λ : Set V) ≤ LinearMap.ker (h x) :=
        Submodule.span_le.2 fun y hy => hx y hy
      exact h1 (htop ▸ Submodule.mem_top))
  have hli : LinearIndependent K e := LinearMap.linearIndependent_of_isOrthoᵢ (B := h)
    (fun i l hil => he1 i l hil) he2
  have hspan : ⊤ ≤ Submodule.span K (Set.range e) := by
    rw [← htop, ← he3, Submodule.span_span_of_tower]
  let b0 := Module.Basis.mk hli hspan
  have hm : m = Module.finrank K V := by
    rw [Module.finrank_eq_card_basis b0, Fintype.card_fin]
  subst hm
  have hb : ⇑b0 = e := Module.Basis.coe_mk hli hspan
  refine ⟨b0, by rw [hb]; exact he1, fun x => ?_⟩
  rw [hΛ, ← he3, ← hb, Module.Basis.mem_span_iff_repr_mem]
  refine forall_congr' fun i => ?_
  rw [show locR (K := K) P = locR (K := K) w.asIdeal from rfl, mem_locR_iff]
  constructor
  · rintro ⟨a, ha⟩
    rw [← ha]; exact a.2
  · intro hk
    exact ⟨⟨_, hk⟩, rfl⟩

end GlobalTheory.MassOrth
