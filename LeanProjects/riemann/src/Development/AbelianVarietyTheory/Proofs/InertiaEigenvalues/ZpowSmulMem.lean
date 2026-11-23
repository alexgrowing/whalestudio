import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SubIdBijOfContracting

noncomputable section
namespace GlobalTheory.PhiGam.TwistShift
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

variable {k : Type} [Field k]

theorem zpow_one_add (c : k⟦X⟧) (s : ℤ) :
    ∃ d : k⟦X⟧, (1 + (c : k⸨X⸩) * vv k ^ 2) ^ s = 1 + (d : k⸨X⸩) * vv k ^ 2 := by
  have hw : (1 + c * PowerSeries.X ^ 2) * PowerSeries.invOfUnit (1 + c * PowerSeries.X ^ 2) 1 = 1 :=
    PowerSeries.mul_invOfUnit _ _ (by simp)
  set w := PowerSeries.invOfUnit (1 + c * PowerSeries.X ^ 2) 1
  have hw' := congrArg (fun a : k⟦X⟧ => (a : k⸨X⸩)) hw
  simp only [map_mul, map_add, map_one, map_pow, ← vv_eq_coe_X] at hw'
  have hne : 1 + (c : k⸨X⸩) * vv k ^ 2 ≠ 0 := left_ne_zero_of_mul_eq_one hw'
  induction s using Int.induction_on with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨d, hd⟩ := ih
    refine ⟨d + c + d * c * PowerSeries.X ^ 2, ?_⟩
    rw [zpow_add_one₀ hne, hd]
    simp only [map_mul, map_add, map_pow, ← vv_eq_coe_X]
    ring
  | pred n ih =>
    obtain ⟨d, hd⟩ := ih
    refine ⟨(d - c) * w, ?_⟩
    rw [zpow_sub_one₀ hne, hd, ← eq_inv_of_mul_eq_one_right hw']
    simp only [map_mul, map_sub]
    linear_combination hw'

theorem one_add_pow (j : ℕ) :
    ∃ e : k⟦X⟧, (1 + vv k) ^ j = 1 + j * vv k + (e : k⸨X⸩) * vv k ^ 2 := by
  induction j with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨e + (n : k⟦X⟧) + e * PowerSeries.X, ?_⟩
    rw [pow_succ, he]
    simp only [map_mul, map_add, map_natCast, ← vv_eq_coe_X]
    push_cast
    ring

variable {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [IsScalarTower k⟦X⟧ k⸨X⸩ V]

theorem coe_smul_mem {N : Submodule k⟦X⟧ V} (a : k⟦X⟧) {x : V} (hx : x ∈ N) : (a : k⸨X⸩) • x ∈ N := by
  have := N.smul_mem a hx
  rwa [← algebraMap_smul k⸨X⸩ a x] at this

theorem zpow_smul_mem {N : Submodule k⟦X⟧ V} (a : ℤ) {s t : ℤ} (h : a + s = t) {x : V} (hx : x ∈ sh s N) :
    vv k ^ a • x ∈ sh t N := by
  rw [← h, ← sh_sh_eq]
  exact mem_sh_iff_exists.2 ⟨x, hx, rfl⟩

variable [Module k V]

theorem sub_mem_sh {σ : k⸨X⸩ →ₐ[k] k⸨X⸩} {g : V →ₗ[k] V} (hg : Semi σ g)
    (hv : ∃ c : k⟦X⟧, σ (vv k) = vv k * (1 + (c : k⸨X⸩) * vv k ^ 2)) {N : Submodule k⟦X⟧ V}
    (hN : ∀ x ∈ N, g x - x ∈ sh 2 N) {s : ℤ} {y : V} (hy : y ∈ sh s N) : g y - y ∈ sh (s + 2) N := by
  obtain ⟨c, hc⟩ := hv
  obtain ⟨d, hd⟩ := zpow_one_add c s
  obtain ⟨x, hx, rfl⟩ := mem_sh_iff_exists.1 hy
  have h1 : g (vv k ^ s • x) - vv k ^ s • x =
      ((1 + d * PowerSeries.X ^ 2 : k⟦X⟧) : k⸨X⸩) • vv k ^ s • (g x - x) +
        (d : k⸨X⸩) • vv k ^ (2 : ℤ) • vv k ^ s • x := by
    rw [hg, map_zpow₀, hc, mul_zpow, hd, zpow_ofNat]
    simp only [map_mul, map_add, map_one, map_pow, ← vv_eq_coe_X, smul_sub, smul_smul]
    rw [sub_eq_iff_eq_add, mul_comm (vv k ^ s), add_assoc, ← add_smul,
      add_mul _ _ (vv k ^ s), one_mul, mul_assoc, add_comm (_ * _) (vv k ^ s), sub_add_cancel]
  rw [h1]
  exact Submodule.add_mem _ (coe_smul_mem _ (zpow_smul_mem s rfl (hN x hx)))
    (coe_smul_mem _ (zpow_smul_mem 2 (add_comm _ _) hy))

theorem bijOn_twist : ∀ {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (σ : k⸨X⸩ →ₐ[k] k⸨X⸩) (g : V →ₗ[k] V), Semi σ g → (∀ a : k⟦X⟧, ∃ b : k⟦X⟧, σ (a : k⸨X⸩) = b) → (∃ c : k⟦X⟧, σ (vv k) = vv k * (1 + (c : k⸨X⸩) * vv k ^ 2)) → ∀ N : Submodule k⟦X⟧ V, IsLat N → (∀ x ∈ N, g x - x ∈ sh 2 N) → ∀ j : ℕ, (j : k) ≠ 0 → ∀ s : ℤ, Set.BijOn (fun y => (1 + vv k) ^ j • g y - y) (sh s N) (sh (s + 1) N) := by
  intro k _ V _ _ _ _ _ _ _ _ σ g hg _ hv N hL hN j hj s
  have hv0 := vv_ne_zero k
  obtain ⟨e, he⟩ := one_add_pow (k := k) j
  obtain ⟨r, hr⟩ : ∃ r : k⟦X⟧, (r : k⸨X⸩) * j = 1 :=
    ⟨PowerSeries.C (j : k)⁻¹, by
      rw [← map_natCast (HahnSeries.ofPowerSeries ℤ k), ← map_mul, ← map_natCast (PowerSeries.C (R := k)),
        ← map_mul, inv_mul_cancel₀ hj, map_one, map_one]⟩
  have hvv : vv k ^ (-1 : ℤ) * vv k = 1 := by rw [zpow_neg_one, inv_mul_cancel₀ hv0]
  let θ : V →+ V :=
    { toFun := fun y => (1 + vv k) ^ j • g y - y
      map_zero' := by simp
      map_add' := fun a b => by simp only [map_add, smul_add]; abel }
  have hθ : ∀ y, θ y = (1 + vv k) ^ j • g y - y := fun _ => rfl
  let E : V →+ V :=
    { toFun := fun y => y - (r : k⸨X⸩) • vv k ^ (-1 : ℤ) • θ y
      map_zero' := by simp
      map_add' := fun a b => by simp only [map_add, smul_add]; abel }
  have hE : ∀ y, E y = y - (r : k⸨X⸩) • vv k ^ (-1 : ℤ) • θ y := fun _ => rfl
  have hθE : ∀ y, θ y = ((j : k⟦X⟧) : k⸨X⸩) • vv k ^ (1 : ℤ) • (y - E y) := by
    intro y
    rw [hE, sub_sub_cancel, smul_smul, smul_smul, smul_smul, map_natCast, zpow_one]
    rw [show (j : k⸨X⸩) * vv k * r * vv k ^ (-1 : ℤ) = 1 by linear_combination (r * j) * hvv + hr, one_smul]
  have hEm : ∀ (t : ℤ), ∀ y ∈ sh t N, E y ∈ sh (t + 1) N := by
    intro t y hy
    have h1 : θ y = (((1 + PowerSeries.X) ^ j : k⟦X⟧) : k⸨X⸩) • (g y - y) + (e : k⸨X⸩) • vv k ^ (2 : ℤ) • y
        + (j * vv k) • y := by
      rw [hθ, map_pow, map_add, map_one, ← vv_eq_coe_X, smul_sub, zpow_ofNat]
      generalize (1 + vv k) ^ j • g y = z
      rw [he, add_smul, add_smul, one_smul, mul_smul (e : k⸨X⸩)]
      abel
    have h2 : E y = -((r : k⸨X⸩) • vv k ^ (-1 : ℤ) • ((((1 + PowerSeries.X) ^ j : k⟦X⟧) : k⸨X⸩) • (g y - y) +
        (e : k⸨X⸩) • vv k ^ (2 : ℤ) • y)) := by
      rw [hE, h1, smul_add _ _ ((j * vv k) • y), smul_add _ _ (_ • (j * vv k) • y),
        smul_smul _ (j * vv k), smul_smul _ (_ * (j * vv k)),
        show (r : k⸨X⸩) * (vv k ^ (-1 : ℤ) * (j * vv k)) = 1 by linear_combination (r * j) * hvv + hr, one_smul]
      abel
    rw [h2]
    refine Submodule.neg_mem _ (coe_smul_mem _ (zpow_smul_mem (s := t + 2) _ (by ring) ?_))
    exact Submodule.add_mem _ (coe_smul_mem _ (sub_mem_sh hg hv hN hy))
      (coe_smul_mem _ (zpow_smul_mem 2 (add_comm _ _) hy))
  have hEs : ∀ y ∈ sh s N, E y ∈ sh s N := fun y hy => sh_le_sh_of_le (by omega) N (hEm s y hy)
  let T : sh s N →+ sh s N :=
    { toFun := fun m => ⟨E m, hEs _ m.2⟩
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }
  have hT : ∀ m, ((T m : sh s N) : V) = E m := fun _ => rfl
  haveI : Module.Finite k⟦X⟧ (sh s N) := Module.Finite.iff_fg.2 (hL.shift s).1
  haveI : IsPrecomplete (Ideal.span {(PowerSeries.X : k⟦X⟧)}) (sh s N) :=
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isPrecomplete_finite_module _ _
  haveI : IsHausdorff (Ideal.span {(PowerSeries.X : k⟦X⟧)}) (sh s N) := by
    rw [← PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  have hXs : ∀ (i : ℕ) (x : V), (PowerSeries.X ^ i : k⟦X⟧) • x = vv k ^ (i : ℤ) • x := by
    intro i x
    rw [← algebraMap_smul k⸨X⸩ (PowerSeries.X ^ i : k⟦X⟧) x, zpow_natCast, map_pow, vv_eq_coe_X]
    rfl
  have hfil : ∀ (i : ℕ) (m : sh s N),
      m ∈ (Ideal.span {(PowerSeries.X : k⟦X⟧)} ^ i • ⊤ : Submodule k⟦X⟧ (sh s N)) ↔ (m : V) ∈ sh (i + s) N := by
    intro i m
    rw [mem_span_pow_smul_top, ← sh_sh_eq, mem_sh_iff_exists]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.2, (hXs i y).symm⟩
    · rintro ⟨y, hy, h⟩
      exact ⟨⟨y, hy⟩, Subtype.ext ((hXs i y).trans h)⟩
  have key := sub_id_bij_of_contracting (Ideal.span {(PowerSeries.X : k⟦X⟧)}) T (by
    intro i m hm
    rw [hfil] at hm ⊢
    have := hEm _ _ hm
    rw [hT]
    convert this using 2
    push_cast
    ring)
  change Set.BijOn θ _ _
  refine ⟨fun y hy => ?_, fun a ha b hb hab => ?_, fun z hz => ?_⟩
  · rw [hθE]
    exact coe_smul_mem _ (zpow_smul_mem 1 (add_comm _ _) (Submodule.sub_mem _ hy (hEs y hy)))
  · have := key.2 ⟨a - b, Submodule.sub_mem _ ha hb⟩ (Subtype.ext (by
      rw [hT, hE, map_sub θ, hab]; simp))
    exact sub_eq_zero.1 (congrArg Subtype.val this)
  · obtain ⟨m, hm⟩ := key.1 ⟨-((r : k⸨X⸩) • vv k ^ (-1 : ℤ) • z),
      Submodule.neg_mem _ (coe_smul_mem _ (zpow_smul_mem _ (by ring) hz))⟩
    refine ⟨m, m.2, ?_⟩
    have h1 : E m - m = -((r : k⸨X⸩) • vv k ^ (-1 : ℤ) • z) := congrArg Subtype.val hm
    rw [hθE, ← neg_sub, h1, neg_neg, smul_smul, smul_smul, smul_smul, map_natCast, zpow_one,
      show (j : k⸨X⸩) * vv k * r * vv k ^ (-1 : ℤ) = 1 by linear_combination (r * j) * hvv + hr, one_smul]

end GlobalTheory.PhiGam.TwistShift
