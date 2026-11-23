import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeOperatorsSpanAndFaithful

open CompanionTheory.Rg.Fl

noncomputable section

namespace GlobalTheory.CompanionTheory.HeckeBern

variable {G : Type} [Group G] {K : Subgroup G}

def dd (K : Subgroup G) : (G ⧸ K) →₀ ℂ := Finsupp.single ((1 : G) : G ⧸ K) 1

def eps (K : Subgroup G) : ((G ⧸ K) →₀ ℂ) →ₗ[ℂ] ℂ := Finsupp.linearCombination ℂ (fun _ => (1 : ℂ))

theorem smul_mk (g x : G) : g • (x : G ⧸ K) = ((g * x : G) : G ⧸ K) := rfl

theorem lam_single (g : G) (x : G ⧸ K) (c : ℂ) :
    lam K g (Finsupp.single x c) = Finsupp.single (g • x) c := by
  simp [lam, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem eps_single (x : G ⧸ K) (c : ℂ) : eps K (Finsupp.single x c) = c := by
  simp [eps]

theorem eps_lam (g : G) (v : (G ⧸ K) →₀ ℂ) : eps K (lam K g v) = eps K v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single x c => rw [lam_single, eps_single, eps_single]

theorem hk_comm (A : Hk K) (g : G) (v : (G ⧸ K) →₀ ℂ) : A.1 (lam K g v) = lam K g (A.1 v) := by
  have h : lam K g * A.1 = A.1 * lam K g :=
    (Subalgebra.mem_centralizer_iff ℂ).1 A.2 _ ⟨g, rfl⟩
  exact (LinearMap.congr_fun h v).symm

theorem lam_out_dd (y : G ⧸ K) : lam K (Quotient.out y) (dd K) = Finsupp.single y 1 := by
  rw [dd, lam_single, smul_mk, mul_one, QuotientGroup.out_eq']

theorem lam_dd {k : G} (hk : k ∈ K) : lam K k (dd K) = dd K := by
  rw [dd, lam_single, smul_mk, mul_one]
  congr 1
  exact QuotientGroup.eq.2 (by simpa using K.inv_mem hk)

theorem hk_fixed (A : Hk K) {k : G} (hk : k ∈ K) : lam K k (A.1 (dd K)) = A.1 (dd K) := by
  rw [← hk_comm, lam_dd hk]

theorem fixed_eq_smul (w : (G ⧸ K) →₀ ℂ) (hw : ∀ k ∈ K, lam K k w = w) (u : G) (S : Finset (G ⧸ K))
    (hS : (↑S : Set (G ⧸ K)) = MulAction.orbit K (u : G ⧸ K))
    (hsupp : ∀ y, y ∉ S → w y = 0) :
    w = w (u : G ⧸ K) • ∑ y ∈ S, Finsupp.single y (1 : ℂ) := by
  classical
  ext y
  have hsum : (∑ x ∈ S, Finsupp.single x (1 : ℂ)) y = if y ∈ S then 1 else 0 := by
    rw [Finsupp.finsetSum_apply]
    simp [Finsupp.single_apply]
  rw [Finsupp.smul_apply, hsum]
  by_cases hy : y ∈ S
  · have hy' : y ∈ MulAction.orbit K (u : G ⧸ K) := by rw [← hS]; exact hy
    obtain ⟨k, rfl⟩ := hy'
    have h1 : (lam K (k : G) w) ((k : G) • (u : G ⧸ K)) = w (u : G ⧸ K) :=
      Finsupp.mapDomain_apply (MulAction.injective (k : G)) _ _
    rw [hw k k.2] at h1
    rw [if_pos hy, smul_eq_mul, mul_one]
    exact h1
  · rw [if_neg hy, hsupp y hy]; simp

section Main

variable (T : G → Hk K) (hp : IsHeckePair K)

def q (hp : IsHeckePair K) (g : G) : ℂ := ((hp g).toFinset.card : ℂ)

theorem q_ne (g : G) : q hp g ≠ 0 := by
  rw [q, Nat.cast_ne_zero, Finset.card_ne_zero]
  exact ⟨(g : G ⧸ K), (hp g).mem_toFinset.2 (MulAction.mem_orbit_self _)⟩

def R (T : G → Hk K) (hp : IsHeckePair K) (g : G) : Hk K := (q hp g)⁻¹ • T g

variable (h1 : ∀ (g : G) (S : Finset (G ⧸ K)), (↑S : Set (G ⧸ K)) = MulAction.orbit K (g : G ⧸ K) →
    (T g : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (Finsupp.single ((1 : G) : G ⧸ K) 1) =
      ∑ y ∈ S, Finsupp.single y (1 : ℂ))
  (h3 : ∀ h : Hk K, (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (Finsupp.single ((1 : G) : G ⧸ K) 1) = 0 → h = 0)

include h1

theorem T_dd (g : G) : (T g).1 (dd K) = ∑ y ∈ (hp g).toFinset, Finsupp.single y (1 : ℂ) :=
  h1 g _ (by simp)

theorem augmentation_of_hecke_operator (g : G) : eps K ((T g).1 (dd K)) = q hp g := by
  rw [T_dd T hp h1, map_sum]
  simp [eps_single, q]

include h3

theorem ext_dd {A B : Hk K} (h : A.1 (dd K) = B.1 (dd K)) : A = B := by
  rw [← sub_eq_zero]
  apply h3
  show (A.1 - B.1) (dd K) = 0
  rw [LinearMap.sub_apply, h, sub_self]

theorem mul_of {g h u : G} (H : ∀ k ∈ K, ∃ a ∈ K, ∃ b ∈ K, h * k * g = a * u * b) :
    T g * T h = (q hp g * q hp h / q hp u) • T u := by
  have hw : (T g * T h).1 (dd K) =
      ∑ y ∈ (hp h).toFinset, lam K (Quotient.out y) ((T g).1 (dd K)) := by
    show (T g).1 ((T h).1 (dd K)) = _
    rw [T_dd T hp h1 h, map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← lam_out_dd, hk_comm]
  have key : ∀ y ∈ (hp h).toFinset, ∀ z ∈ (hp g).toFinset,
      (Quotient.out y) • z ∈ (hp u).toFinset := by
    intro y hy z hz
    obtain ⟨k1, rfl⟩ := (hp h).mem_toFinset.1 hy
    obtain ⟨k3, rfl⟩ := (hp g).mem_toFinset.1 hz
    set y0 : G ⧸ K := k1 • (h : G ⧸ K) with hy0
    have hout : ((Quotient.out y0 : G) : G ⧸ K) = ((k1 * h : G) : G ⧸ K) := by
      rw [QuotientGroup.out_eq']; rfl
    have hk2 : ((k1 : G) * h)⁻¹ * Quotient.out y0 ∈ K := QuotientGroup.eq.1 hout.symm
    obtain ⟨a, ha, b, hb, hab⟩ := H _ (K.mul_mem hk2 k3.2)
    rw [(hp u).mem_toFinset]
    refine ⟨⟨(k1 : G) * a, K.mul_mem k1.2 ha⟩, ?_⟩
    show (((k1 : G) * a * u : G) : G ⧸ K) = (Quotient.out y0 * ((k3 : G) * g) : G)
    rw [QuotientGroup.eq]
    have e : Quotient.out y0 * ((k3 : G) * g) = (k1 : G) * (h * ((((k1 : G) * h)⁻¹ * Quotient.out y0) * k3) * g) := by
      group
    rw [e, hab]
    have e2 : ((k1 : G) * a * u)⁻¹ * ((k1 : G) * (a * u * b)) = b := by group
    rw [e2]; exact hb
  have hsupp : ∀ y, y ∉ (hp u).toFinset → ((T g * T h).1 (dd K)) y = 0 := by
    classical
    intro y hy
    rw [hw, Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [T_dd T hp h1 g, map_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun z hz => ?_
    rw [lam_single, Finsupp.single_apply, if_neg]
    intro e
    exact hy (e ▸ key x hx z hz)
  have hfix := fixed_eq_smul ((T g * T h).1 (dd K)) (fun k hk => hk_fixed (T g * T h) hk) u
    (hp u).toFinset (by simp) hsupp
  set c : ℂ := ((T g * T h).1 (dd K)) (u : G ⧸ K) with hc
  have heq : T g * T h = c • T u := by
    apply ext_dd T h1 h3
    rw [hfix, ← T_dd T hp h1 u]
    rfl
  have hq : c * q hp u = q hp g * q hp h := by
    have e1 : eps K ((T g * T h).1 (dd K)) = c * q hp u := by
      rw [hfix, map_smul, ← T_dd T hp h1 u, augmentation_of_hecke_operator T hp h1, smul_eq_mul]
    have e2 : eps K ((T g * T h).1 (dd K)) = q hp g * q hp h := by
      rw [hw, map_sum]
      simp only [eps_lam, augmentation_of_hecke_operator T hp h1]
      simp [q, mul_comm]
    rw [← e1, e2]
  rw [heq, eq_div_of_mul_eq (q_ne hp u) hq]

theorem R_mul {g h u : G} (H : ∀ k ∈ K, ∃ a ∈ K, ∃ b ∈ K, h * k * g = a * u * b) :
    R T hp g * R T hp h = R T hp u := by
  have hg := q_ne hp g
  have hh := q_ne hp h
  have hu := q_ne hp u
  rw [R, R, R, smul_mul_smul_comm, mul_of T hp h1 h3 H, smul_smul]
  congr 1
  field_simp

theorem T_congr {g : G} {k k' : G} (hk : k ∈ K) (hk' : k' ∈ K) : T (k * g * k') = T g ∧ q hp (k * g * k') = q hp g := by
  have e : ((k * g * k' : G) : G ⧸ K) = (⟨k, hk⟩ : K) • (g : G ⧸ K) := by
    show ((k * g * k' : G) : G ⧸ K) = ((k * g : G) : G ⧸ K)
    rw [QuotientGroup.eq]
    have : (k * g * k')⁻¹ * (k * g) = k'⁻¹ := by group
    rw [this]; exact K.inv_mem hk'
  have ho : MulAction.orbit K ((k * g * k' : G) : G ⧸ K) = MulAction.orbit K (g : G ⧸ K) := by
    rw [e, MulAction.orbit_smul]
  have hf : (hp (k * g * k')).toFinset = (hp g).toFinset := by
    ext x; simp [ho]
  refine ⟨ext_dd T h1 h3 ?_, by simp only [q, hf]⟩
  rw [T_dd T hp h1, T_dd T hp h1, hf]

theorem R_congr {g : G} {k k' : G} (hk : k ∈ K) (hk' : k' ∈ K) : R T hp (k * g * k') = R T hp g := by
  obtain ⟨a, b⟩ := T_congr T hp h1 h3 (g := g) hk hk'
  rw [R, R, a, b]

theorem R_one : R T hp 1 = 1 := by
  have hf : (hp 1).toFinset = {((1 : G) : G ⧸ K)} := by
    ext x
    simp only [Set.Finite.mem_toFinset, Finset.mem_singleton]
    constructor
    · rintro ⟨k, rfl⟩
      exact QuotientGroup.eq.2 (by simp)
    · rintro rfl; exact MulAction.mem_orbit_self _
  have hq : q hp (1 : G) = 1 := by simp [q, hf]
  rw [R, hq, inv_one, one_smul]
  apply ext_dd T h1 h3
  rw [T_dd T hp h1, hf, Finset.sum_singleton]
  rfl

end Main

theorem stHecke : StHecke := by
  intro G _ K d l hp hcart
  obtain ⟨c, t, hc, ht, hdec, hmon⟩ := hcart
  obtain ⟨T, h1, h2, h3⟩ := GlobalTheory.CompanionTheory.HeckeBasis.heckeBasis G K hp
  have hcinv : ∀ i, ∀ k ∈ K, (c i)⁻¹ * k * c i ∈ K := by
    intro i k hk
    rw [hc i]
    have : c i * ((c i)⁻¹ * k * c i) * (c i)⁻¹ = k := by group
    rwa [this]
  have hmul : ∀ s ∈ Submonoid.closure (Set.range t), ∀ s' ∈ Submonoid.closure (Set.range t),
      R T hp s' * R T hp s = R T hp (s * s') := fun s hs s' hs' =>
    R_mul T hp h1 h3 (hmon s hs s' hs')
  have hcomm : ∀ i j, Commute (R T hp (t i)) (R T hp (t j)) := by
    intro i j
    have mi : t i ∈ Submonoid.closure (Set.range t) := Submonoid.subset_closure (Set.mem_range_self i)
    have mj : t j ∈ Submonoid.closure (Set.range t) := Submonoid.subset_closure (Set.mem_range_self j)
    show R T hp (t i) * R T hp (t j) = R T hp (t j) * R T hp (t i)
    rw [hmul _ mj _ mi, hmul _ mi _ mj, (ht i j).eq]
  have hadj : ∀ s ∈ Submonoid.closure (Set.range t),
      R T hp s ∈ Algebra.adjoin ℂ (Set.range (R T hp ∘ t)) := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Algebra.subset_adjoin ⟨i, rfl⟩
    | one => rw [R_one T hp h1 h3]; exact Subalgebra.one_mem _
    | mul x y hx hy ihx ihy =>
      rw [← hmul x hx y hy]
      exact Subalgebra.mul_mem _ ihy ihx
  have hprod : ∀ i j, ∀ s ∈ Submonoid.closure (Set.range t),
      R T hp (c i * s * c j) = R T hp (c j) * R T hp s * R T hp (c i) := by
    intro i j s _
    have e1 : R T hp s * R T hp (c i) = R T hp (c i * s) := by
      refine R_mul T hp h1 h3 fun k hk => ⟨c i * k * (c i)⁻¹, (hc i k).1 hk, 1, K.one_mem, ?_⟩
      group
    have e2 : R T hp (c j) * R T hp (c i * s) = R T hp (c i * s * c j) := by
      refine R_mul T hp h1 h3 fun k hk => ⟨1, K.one_mem, (c j)⁻¹ * k * c j, hcinv j k hk, ?_⟩
      group
    rw [mul_assoc (R T hp (c j)), e1, e2]
  refine ⟨R T hp ∘ c, R T hp ∘ c, R T hp ∘ t, hcomm, ?_⟩
  rw [eq_top_iff, ← h2, Submodule.span_le]
  rintro _ ⟨g, rfl⟩
  obtain ⟨i, j, s, hs, k, hk, k', hk', rfl⟩ := hdec g
  have hT : T (k * c i * s * c j * k') = q hp (k * c i * s * c j * k') • R T hp (k * c i * s * c j * k') := by
    rw [R, smul_smul, mul_inv_cancel₀ (q_ne hp _), one_smul]
  rw [hT]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, i, R T hp s, hadj s hs, ?_⟩)
  have e : k * c i * s * c j * k' = k * (c i * s * c j) * k' := by group
  rw [e, R_congr T hp h1 h3 hk hk', hprod i j s hs]
  rfl

end GlobalTheory.CompanionTheory.HeckeBern

end
