import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt

noncomputable section

open GlobalTheory.SmGL ValuativeRel

namespace GlobalTheory.CompanionTheory.ExtCharU

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pw_add {n : ℕ} (ξ : Fin n → ℂˣ) (x y : Fin n → ℤ) :
    GlobalTheory.BCT.pw ξ (x + y) = GlobalTheory.BCT.pw ξ x * GlobalTheory.BCT.pw ξ y := by
  simp only [GlobalTheory.BCT.pw, Pi.add_apply, zpow_add, Units.val_mul, Finset.prod_mul_distrib]

theorem pw_ne_zero {n : ℕ} (ξ : Fin n → ℂˣ) (x : Fin n → ℤ) : GlobalTheory.BCT.pw ξ x ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ => Units.ne_zero _

def dg {n : ℕ} (ϖ : kˣ) (e : Fin n → ℤ) : Fin n → kˣ := fun i => ϖ ^ e i

theorem dg_add {n : ℕ} (ϖ : kˣ) (x y : Fin n → ℤ) : dg ϖ (x + y) = dg ϖ x * dg ϖ y := by
  funext i; simp [dg, zpow_add]

theorem ord_zpow (ϖ : kˣ) (m : ℤ) : ord k (ϖ ^ m) = m * ord k ϖ := by
  let o : kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun x => .ofAdd (ord k x)) fun x y => by
    rw [ord_mul, ofAdd_add]
  have h := map_zpow o ϖ m
  have h2 : ord k (ϖ ^ m) = m • ord k ϖ := by
    have := congrArg Multiplicative.toAdd h
    simpa [o] using this
  simpa using h2

def rr (n : ℕ) : Fin n → ℤ := fun i => (n : ℤ) - 1 - (i : ℕ)

theorem rr_anti (n : ℕ) : StrictAnti (rr n) := fun i j h => by
  have : (i : ℕ) < j := h
  simp only [rr]; omega

theorem rr_smul_anti (n : ℕ) {N : ℤ} (hN : 0 < N) : StrictAnti (N • rr n) := fun i j h => by
  have := rr_anti n h
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_lt_mul_of_pos_left this hN

theorem add_anti {n : ℕ} (e : Fin n → ℤ) :
    ∃ N : ℤ, 0 < N ∧ StrictAnti (e + N • rr n) := by
  refine ⟨1 + 2 * ∑ i, |e i|, by positivity, fun i j h => ?_⟩
  have hij : (i : ℕ) < j := h
  have hi : |e i| ≤ ∑ l, |e l| :=
    Finset.single_le_sum (f := fun l => |e l|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hj : |e j| ≤ ∑ l, |e l| :=
    Finset.single_le_sum (f := fun l => |e l|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have h1 := abs_le.1 (le_refl |e i|)
  have h2 := abs_le.1 (le_refl |e j|)
  set S := ∑ l, |e l|
  have hd : (1 : ℤ) ≤ rr n i - rr n j := by simp only [rr]; omega
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  nlinarith

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem const_eq_one (R : Representation ℂ (Fin n → kˣ) M) {z : M} {ϖ : kˣ} {ξ : Fin n → ℂˣ} {c : ℂ}
    (hz : z ≠ 0)
    (hx : ∀ x : Fin n → ℤ, StrictAnti x → R (fun i => ϖ ^ x i) z = (c * GlobalTheory.BCT.pw ξ x) • z) :
    c = 1 := by
  have hr := hx (rr n) (rr_anti n)
  have h2 := hx (rr n + rr n) (by
    simpa [two_smul] using rr_smul_anti n (N := 2) (by norm_num))
  have hd : (fun i => ϖ ^ (rr n + rr n) i) = (fun i => ϖ ^ rr n i) * (fun i => ϖ ^ rr n i) :=
    dg_add ϖ (rr n) (rr n)
  rw [hd, map_mul, Module.End.mul_apply, hr, map_smul, hr, smul_smul, pw_add] at h2
  set p := GlobalTheory.BCT.pw ξ (rr n)
  have hp : p ≠ 0 := pw_ne_zero ξ _
  have h3 : c * p * (c * p) = c * (p * p) := smul_left_injective ℂ hz h2
  have hc : c ≠ 0 := by
    rintro rfl
    apply hz
    have h4 : R (fun i => ϖ ^ rr n i) z = 0 := by simpa using hr
    have h5 := congrArg (R (fun i => ϖ ^ rr n i)⁻¹) h4
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero] at h5
    simpa using h5
  have hpp : p * p ≠ 0 := mul_ne_zero hp hp
  apply mul_left_cancel₀ (mul_ne_zero hc hpp)
  linear_combination h3

theorem eig_all (R : Representation ℂ (Fin n → kˣ) M) {z : M} {ϖ : kˣ} {ξ : Fin n → ℂˣ}
    (hx : ∀ x : Fin n → ℤ, StrictAnti x → R (fun i => ϖ ^ x i) z = GlobalTheory.BCT.pw ξ x • z)
    (e : Fin n → ℤ) : R (dg ϖ e) z = GlobalTheory.BCT.pw ξ e • z := by
  obtain ⟨N, hN, ha⟩ := add_anti e
  have hy := hx _ (rr_smul_anti n hN)
  have hxy := hx _ ha
  have hd : (fun i => ϖ ^ (e + N • rr n) i) = dg ϖ e * (fun i => ϖ ^ (N • rr n) i) :=
    dg_add ϖ e _
  rw [hd, map_mul, Module.End.mul_apply, hy, map_smul, pw_add, mul_comm, mul_smul] at hxy
  exact smul_right_injective M (pw_ne_zero ξ (N • rr n)) hxy

theorem extChar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (R : Representation ℂ (Fin n → kˣ) M) (z : M) (ϖ : kˣ) (ξ : Fin n → ℂˣ) (c : ℂ),
    z ≠ 0 → ord k ϖ = 1 → (∀ t ∈ torusO k (Fin n), R t z = z) →
    (∀ x : Fin n → ℤ, StrictAnti x → R (fun i => ϖ ^ x i) z = (c * GlobalTheory.BCT.pw ξ x) • z) →
    ∀ t : Fin n → kˣ,
      R t z = (((torusChar fun i => unrChar k (ξ i)) t : ℂˣ) : ℂ) • z := by
  intro k _ _ _ _ n M _ _ R z ϖ ξ c hz hϖ hO hx t
  have hc : c = 1 := const_eq_one R hz hx
  subst hc
  simp only [one_mul] at hx
  set e : Fin n → ℤ := fun i => ord k (t i) with he
  have hu : t * (dg ϖ e)⁻¹ ∈ torusO k (Fin n) := by
    intro i
    apply ord_eq_zero_iff.1
    have h1 : ord k (t i * (ϖ ^ e i)⁻¹) = 0 := by
      have h2 := ord_mul k (t i * (ϖ ^ e i)⁻¹) (ϖ ^ e i)
      rw [inv_mul_cancel_right, ord_zpow, hϖ, mul_one] at h2
      have h3 : e i = ord k (t i) := rfl
      omega
    simpa [dg] using h1
  have ht : t = dg ϖ e * (t * (dg ϖ e)⁻¹) := by simp
  have h1 : R t z = R (dg ϖ e) z := by
    conv_lhs => rw [ht]
    rw [map_mul, Module.End.mul_apply, hO _ hu]
  rw [h1, eig_all R hx e, torusChar_apply]
  congr 1
  simp [GlobalTheory.BCT.pw, he, unrChar_apply]

end GlobalTheory.CompanionTheory.ExtCharU
