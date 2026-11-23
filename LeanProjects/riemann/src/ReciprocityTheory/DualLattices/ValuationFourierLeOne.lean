import ReciprocityTheory.DualLattices.ValuationDetEqOfSpanEq

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]

theorem fourier_apply' {X H : Type} [Fintype X] (e : H → X → C) (u : X → C) (h : H) :
    fourier (R := R) e u h = ∑ a, u a * e h a := rfl

def pairInt {X : Type} [Fintype X] (U : X → C) : Submodule R (X → C) where
  carrier := {F | ∃ r : R, algebraMap R C r = ∑ x, U x * F x}
  add_mem' := by
    rintro F G ⟨r, hr⟩ ⟨s, hs⟩
    exact ⟨r + s, by simp [hr, hs, mul_add, Finset.sum_add_distrib]⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro c F ⟨r, hr⟩
    refine ⟨c * r, ?_⟩
    simp only [map_mul, hr, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring

def conv (u w : N → C) : N → C := fun c => ∑ a, u a * w (c - a)

theorem fourier_conv {H : Type} (χ : H → AddChar N C) (u w : N → C) (h : H) :
    fourier (R := R) (fun h a => χ h a) (conv u w) h =
      fourier (R := R) (fun h a => χ h a) u h * fourier (R := R) (fun h a => χ h a) w h := by
  rw [fourier_apply' (R := R), fourier_apply' (R := R), fourier_apply' (R := R),
    Finset.sum_mul_sum]
  simp only [conv, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Fintype.sum_equiv (Equiv.subRight a) _ _ fun c => ?_
  simp only [Equiv.subRight_apply]
  have hc : χ h c = χ h a * χ h (c - a) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    abel
  rw [hc]
  ring

private theorem mem_dualLat_iff_sum_mul_integral {X : Type} [Fintype X] (M : Submodule R (X → C)) (u : X → C) :
    u ∈ dualLat M ↔ ∀ f ∈ M, ∃ r : R, algebraMap R C r = ∑ a, u a * f a := Iff.rfl

private theorem mem_pairInt_iff {X : Type} [Fintype X] (U F : X → C) :
    F ∈ pairInt (R := R) U ↔ ∃ r : R, algebraMap R C r = ∑ x, U x * F x :=
  Iff.rfl

theorem conv_mem_dualLat (AA : HopfOrder (C := C) R N) {u w : N → C}
    (hu : u ∈ dualLat AA.carrier) (hw : w ∈ dualLat AA.carrier) :
    conv u w ∈ dualLat AA.carrier := by
  have key : tensorSpan R AA.carrier ≤
      pairInt (R := R) (fun p : N × N => u p.1 * w p.2) := by
    rw [tensorSpan, Submodule.span_le]
    rintro F ⟨g, hg, k, hk, rfl⟩
    rw [SetLike.mem_coe, mem_pairInt_iff]
    obtain ⟨r, hr⟩ := (mem_dualLat_iff_sum_mul_integral _ _).1 hu g hg
    obtain ⟨s, hs⟩ := (mem_dualLat_iff_sum_mul_integral _ _).1 hw k hk
    refine ⟨r * s, ?_⟩
    rw [map_mul, hr, hs, Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [mem_dualLat_iff_sum_mul_integral]
  intro f hf
  obtain ⟨r, hr⟩ := (mem_pairInt_iff _ _).1 (key (AA.comul f hf))
  refine ⟨r, hr.trans ?_⟩
  rw [Fintype.sum_prod_type]
  simp only [addPull, LinearMap.funLeft_apply, conv, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Fintype.sum_equiv (Equiv.addLeft a) _ _ fun b => ?_
  simp

theorem single_mem_dualLat (AA : HopfOrder (C := C) R N) :
    (Pi.single 0 1 : N → C) ∈ dualLat AA.carrier := by
  rw [mem_dualLat_iff_sum_mul_integral]
  intro f hf
  obtain ⟨r, hr⟩ := AA.le_int hf 0
  refine ⟨r, ?_⟩
  rw [hr]
  simp [Pi.single_apply]

def cpow (u : N → C) : ℕ → N → C
  | 0 => Pi.single 0 1
  | k + 1 => conv (cpow u k) u

theorem cpow_mem (AA : HopfOrder (C := C) R N) {u : N → C} (hu : u ∈ dualLat AA.carrier) :
    ∀ k, cpow u k ∈ dualLat AA.carrier
  | 0 => single_mem_dualLat AA
  | k + 1 => conv_mem_dualLat AA (cpow_mem AA hu k) hu

theorem fourier_single {H : Type} (χ : H → AddChar N C) (h : H) :
    fourier (R := R) (fun h a => χ h a) (Pi.single 0 1) h = 1 := by
  rw [fourier_apply' (R := R)]
  simp [Pi.single_apply]

theorem fourier_cpow {H : Type} (χ : H → AddChar N C) (u : N → C) (h : H) :
    ∀ k, fourier (R := R) (fun h a => χ h a) (cpow u k) h =
      fourier (R := R) (fun h a => χ h a) u h ^ k
  | 0 => by rw [pow_zero]; exact fourier_single χ h
  | k + 1 => by
    simp only [cpow]
    rw [fourier_conv, fourier_cpow χ u h k, pow_succ]

private theorem nnreal_le_one_of_forall_pow_le {x M : NNReal} (h : ∀ k : ℕ, x ^ k ≤ M) : x ≤ 1 := by
  by_contra hx
  rw [not_le] at hx
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt M hx
  exact (not_lt.2 (h k)) hk

private theorem le_sum_sum {ι κ : Type} [Fintype ι] [Fintype κ] (f : ι → κ → NNReal) (i : ι)
    (j : κ) : f i j ≤ ∑ i, ∑ j, f i j :=
  (Finset.single_le_sum (f := fun j => f i j) (fun _ _ => zero_le) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i => ∑ j, f i j) (fun _ _ => zero_le) (Finset.mem_univ i))

private theorem hopfOrder_exists_valuation_apply_le (v : Valuation C NNReal) (hv : v.Integers R)
    (AA : HopfOrder (C := C) R N) :
    ∃ M : NNReal, ∀ u ∈ dualLat AA.carrier, ∀ a, v (u a) ≤ M := by
  obtain ⟨B, hB, hA⟩ := AA.lat
  refine ⟨∑ j, ∑ x, v (B⁻¹ j x), fun u hu a => ?_⟩
  rw [hA, mem_dualLat_spanCols_iff] at hu
  have hu' : u = (u ᵥ* B) ᵥ* B⁻¹ := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hB, Matrix.vecMul_one]
  rw [hu']
  change v (∑ j, (u ᵥ* B) j * B⁻¹ j a) ≤ _
  apply v.map_sum_le
  intro j _
  obtain ⟨r, hr⟩ := hu j
  rw [map_mul, ← hr]
  exact (mul_le_of_le_one_left (zero_le) (hv.map_le_one r)).trans
    (le_sum_sum (fun j x => v (B⁻¹ j x)) j a)

theorem valuation_fourier_le_one (v : Valuation C NNReal) (hv : v.Integers R) {H : Type}
    (χ : H → AddChar N C) (AA : HopfOrder (C := C) R N) {u : N → C}
    (hu : u ∈ dualLat AA.carrier) (h : H) :
    v (fourier (R := R) (fun h a => χ h a) u h) ≤ 1 := by
  obtain ⟨M, hM⟩ := hopfOrder_exists_valuation_apply_le v hv AA
  have hχ : ∀ a, v (χ h a) ≤ 1 := fun a =>
    nnreal_le_one_of_forall_pow_le (M := ∑ b, v (χ h b)) fun k => by
      rw [← map_pow, ← AddChar.map_nsmul_eq_pow]
      exact Finset.single_le_sum (f := fun b => v (χ h b)) (fun _ _ => zero_le)
        (Finset.mem_univ _)
  apply nnreal_le_one_of_forall_pow_le (M := M)
  intro k
  rw [← map_pow, ← fourier_cpow (R := R) χ u h k, fourier_apply' (R := R)]
  apply v.map_sum_le
  intro a _
  rw [map_mul]
  exact (mul_le_of_le_one_right (zero_le) (hχ a)).trans
    (hM _ (cpow_mem AA hu k) a)

end ReciprocityTheory.PGsh.L2
