import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import Development.WeilBound.CoreStatements.HodgeTatePoints.RangeSubtypeEq

noncomputable section

namespace PositivityTheory.HtPt.Rc

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

section Gen

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {F : Type} [Field F]
  [Fintype F] [DecidableEq F]
variable {N X : Type} [AddCommGroup N] [Module F N] [AddCommGroup X] [Module F X]

def projL (χ : MulChar F R) : (N → C) →ₗ[R] (N → C) where
  toFun := GlobalTheory.CompanionTheory.Ar.GR.proj χ
  map_add' g h := by
    funext x
    simp only [GlobalTheory.CompanionTheory.Ar.GR.proj, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r g := by
    funext x
    simp only [GlobalTheory.CompanionTheory.Ar.GR.proj, Pi.smul_apply, Algebra.smul_def, RingHom.id_apply,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring

lemma projL_apply (χ : MulChar F R) (g : N → C) (x : N) :
    projL χ g x = (Fintype.card Fˣ : C)⁻¹ *
      ∑ a : Fˣ, algebraMap R C (χ⁻¹ (a : F)) * g ((a : F) • x) := rfl

lemma exists_inv_card {v : Valuation C NNReal} (hv : v.Integers R) (p : ℕ) [Fact p.Prime]
    (hvp : v (p : C) < 1) [CharP F p] :
    ∃ u : R, algebraMap R C u = (Fintype.card Fˣ : C)⁻¹ := by
  obtain ⟨n, -, hn⟩ := FiniteField.card F p
  have hq : v ((Fintype.card F : ℕ) : C) < 1 := by
    rw [hn, Nat.cast_pow, map_pow]
    exact pow_lt_one₀ zero_le hvp n.ne_zero
  have h1 : v (Fintype.card Fˣ : C) = 1 := by
    rw [Fintype.card_units, Nat.cast_sub Fintype.card_pos, Nat.cast_one, Valuation.map_sub_swap]
    exact v.map_one_sub_of_lt hq
  exact hv.exists_of_le_one (by rw [map_inv₀, h1, inv_one])

lemma projL_mem (hu : ∃ u : R, algebraMap R C u = (Fintype.card Fˣ : C)⁻¹) (χ : MulChar F R)
    (S : Submodule R (N → C)) (hS : FStable F S) {g : N → C} (hg : g ∈ S) : projL χ g ∈ S := by
  obtain ⟨u, hu⟩ := hu
  have : projL χ g = u • ∑ a : Fˣ, χ⁻¹ (a : F) • (fun x => g ((a : F) • x)) := by
    funext x
    rw [projL_apply, Pi.smul_apply, Finset.sum_apply, Algebra.smul_def, hu]
    exact congrArg _ (Finset.sum_congr rfl fun a _ => (Algebra.smul_def _ _).symm)
  rw [this]
  exact S.smul_mem _ (S.sum_mem fun a _ => S.smul_mem _ (hS _ g hg))

omit [Fintype F] [DecidableEq F] in
lemma fstable_sq {M : Submodule R (N → C)} (hM : FStable F M) :
    FStable F (sqIdeal (augIdeal M)) :=
  fun a _ hg => sq_pull (LinearMap.lsmul F N a).toAddMonoidHom M M (hM a) hg

omit [Fintype F] [DecidableEq F] in
lemma mul_inv_unit (χ : MulChar F R) (a : Fˣ) : χ (a : F) * χ⁻¹ (a : F) = 1 := by
  rw [← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply_coe]

omit [Fintype F] [DecidableEq F] in
lemma eig_le_aug (M : Submodule R (N → C)) (χ : MulChar F R) : eig M χ ≤ augIdeal M := by
  intro g hg
  rw [mem_aug]
  refine ⟨hg.1, ?_⟩
  have := hg.2 0 0
  rwa [zero_smul, MulChar.map_zero, map_zero, zero_mul] at this

lemma projL_eig (hu : ∃ u : R, algebraMap R C u = (Fintype.card Fˣ : C)⁻¹) (χ : MulChar F R)
    {M : Submodule R (N → C)} (hM : FStable F M) {g : N → C} (hg : g ∈ augIdeal M) :
    projL χ g ∈ eig M χ := by
  rw [mem_aug] at hg
  refine ⟨projL_mem hu χ M hM hg.1, fun a x => ?_⟩
  by_cases ha : a = 0
  · rw [ha, zero_smul, MulChar.map_zero, map_zero, zero_mul, projL_apply]
    simp only [smul_zero, hg.2, mul_zero, Finset.sum_const_zero]
  · obtain ⟨a, rfl⟩ := (isUnit_iff_ne_zero.2 ha)
    rw [projL_apply, projL_apply, mul_left_comm, Finset.mul_sum Finset.univ _ (algebraMap R C _),
      ← Equiv.sum_comp (Equiv.mulRight a) (fun b : Fˣ => algebraMap R C (χ (a : F)) *
        (algebraMap R C (χ⁻¹ (b : F)) * g ((b : F) • x)))]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Equiv.coe_mulRight, Units.val_mul, mul_smul, ← mul_assoc, ← map_mul, map_mul χ⁻¹,
      mul_left_comm, mul_inv_unit, mul_one]

lemma projL_self [CharZero C] (χ : MulChar F R) {M : Submodule R (N → C)} {g : N → C}
    (hg : g ∈ eig M χ) : projL χ g = g := by
  funext x
  have h : ∀ a : Fˣ, algebraMap R C (χ⁻¹ (a : F)) * g ((a : F) • x) = g x := fun a => by
    rw [hg.2, ← mul_assoc, ← map_mul, mul_comm (χ⁻¹ _), mul_inv_unit, map_one, one_mul]
  rw [projL_apply]
  simp only [h]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero), one_mul]

lemma projL_ne [IsDomain R] {χ χ' : MulChar F R} (hne : χ ≠ χ') {M : Submodule R (N → C)}
    {g : N → C} (hg : g ∈ eig M χ') : projL χ g = 0 := by
  funext x
  have h : ∀ a : Fˣ, algebraMap R C (χ⁻¹ (a : F)) * g ((a : F) • x) =
      algebraMap R C ((χ⁻¹ * χ') (a : F)) * g x := fun a => by
    rw [hg.2, ← mul_assoc, ← map_mul, MulChar.mul_apply]
  have h0 : ∑ a : Fˣ, (χ⁻¹ * χ') (a : F) = 0 := by
    refine sum_hom_units_eq_zero ((χ⁻¹ * χ').toMonoidHom.comp (Units.coeHom F)) fun h1 => hne ?_
    rw [← inv_mul_eq_one]
    refine MulChar.ext fun a => ?_
    rw [MulChar.one_apply_coe]
    exact DFunLike.congr_fun h1 a
  rw [projL_apply]
  simp only [h]
  rw [← Finset.sum_mul, ← map_sum, h0, map_zero, zero_mul, mul_zero, Pi.zero_apply]

lemma sum_projL [CharZero C] [IsDomain R] (σ : MulChar F R)
    (hσ : ∀ a : Fˣ, σ (a : F) = 1 → a = 1) (g : N → C) :
    ∑ i : Fin (Fintype.card Fˣ), projL (σ ^ ((i : ℕ) + 1)) g = g := by
  funext x
  have h : ∀ a : Fˣ, ∑ i : Fin (Fintype.card Fˣ), (σ ^ ((i : ℕ) + 1))⁻¹ (a : F) =
      if a = 1 then (Fintype.card Fˣ : R) else 0 := by
    intro a
    split_ifs with ha
    · simp [ha]
    · have hp : ∀ i : ℕ, (σ ^ (i + 1))⁻¹ (a : F) = σ⁻¹ (a : F) ^ i * σ⁻¹ (a : F) := fun i => by
        rw [← inv_pow, MulChar.pow_apply_coe, pow_succ]
      simp only [hp]
      rw [← Finset.sum_mul, Fin.sum_univ_eq_sum_range (fun i => σ⁻¹ (a : F) ^ i)]
      have h1 := geom_sum_mul (σ⁻¹ (a : F)) (Fintype.card Fˣ)
      rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one,
        sub_self] at h1
      have h2 : σ⁻¹ (a : F) - 1 ≠ 0 := fun h => ha (hσ a (by
        have := mul_inv_unit σ a
        rwa [sub_eq_zero.1 h, mul_one] at this))
      rw [(mul_eq_zero.1 h1).resolve_right h2, zero_mul]
  rw [Finset.sum_apply]
  simp only [projL_apply]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [← Finset.sum_mul, ← map_sum, h]
  rw [Finset.sum_eq_single 1 (fun a _ ha => by simp [ha]) (by simp)]
  rw [if_pos rfl, map_natCast, Units.val_one, one_smul, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero), one_mul]

lemma projL_funLeft (χ : MulChar F R) (φ : X →ₗ[F] N) (g : N → C) :
    projL χ (LinearMap.funLeft R C φ g) = LinearMap.funLeft R C φ (projL χ g) := by
  funext x
  simp only [projL_apply, LinearMap.funLeft_apply, map_smul]

omit [Fintype F] [DecidableEq F] in
lemma eig_pull (χ : MulChar F R) (φ : X →ₗ[F] N) (M : Submodule R (N → C))
    (M' : Submodule R (X → C)) (h : ∀ g ∈ M, LinearMap.funLeft R C φ g ∈ M') {g : N → C}
    (hg : g ∈ eig M χ) : LinearMap.funLeft R C φ g ∈ eig M' χ :=
  ⟨h g hg.1, fun a x => by simp only [LinearMap.funLeft_apply, map_smul, hg.2]⟩

end Gen

end PositivityTheory.HtPt.Rc
