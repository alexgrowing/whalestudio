import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot

noncomputable section

namespace GlobalTheory.DatumSign

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Module
open scoped TensorProduct

section Lin

variable {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

theorem _root_.GlobalTheory.DatumSign.trace_eq :
    ∀ {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] (T : V →ₗ[ℝ] V) (s : ℝ),
      ∀ (hs : (0 : ℝ) < s) (hT : ∀ (x : V), T (T x) = (s * s) • x),
        LinearMap.trace ℝ V T =
          s * ((2 : ℝ) * (Module.finrank ℝ (T - s • LinearMap.id).ker : ℝ) -
            (Module.finrank ℝ V : ℝ)) := by
  intro V _ _ _ T s hs hT
  set P : V →ₗ[ℝ] V := (2 * s)⁻¹ • (T + s • LinearMap.id) with hP
  have hproj : LinearMap.IsProj (T - s • LinearMap.id).ker P := by
    constructor
    · intro x
      simp only [LinearMap.mem_ker, hP, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.add_apply, LinearMap.id_apply, map_smul, map_add, hT]
      rw [smul_sub s (T x), smul_smul, sub_add_sub_cancel, sub_self, smul_zero]
    · intro x hx
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hx
      simp only [hP, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply, hx,
        ← two_smul ℝ (s • x), smul_smul]
      rw [show (2 * s)⁻¹ * (2 * s) = 1 by field_simp, one_smul]
  have htr := hproj.trace
  have hTP : T = (2 * s) • P - s • LinearMap.id := by
    rw [hP, smul_smul, mul_inv_cancel₀ (by positivity), one_smul, add_sub_cancel_right]
  clear_value P
  conv_lhs => rw [hTP]
  rw [map_sub, map_smul, map_smul, htr, LinearMap.trace_id, smul_eq_mul, smul_eq_mul]
  ring

theorem finrank_le (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (A J K : V →ₗ[ℝ] V) (s : ℝ) (hs : 0 < s)
    (hA : ∀ x, A (A x) = -((s * s) • x)) (hJ : ∀ x, J (J x) = -x) (hK : ∀ x, K (K x) = -x)
    (hKA : K ∘ₗ A = A ∘ₗ K) (pJ : ∀ x, x ≠ 0 → 0 < B (J x) x) (pK : ∀ x, x ≠ 0 → 0 < B (K x) x) :
    finrank ℝ (LinearMap.ker (J ∘ₗ A - s • LinearMap.id)) ≤ finrank ℝ (LinearMap.ker (K ∘ₗ A - s • LinearMap.id)) := by
  have c : ∀ x, K (A x) = A (K x) := fun x => LinearMap.congr_fun hKA x
  let W := LinearMap.ker (J ∘ₗ A - s • LinearMap.id)
  let W' := LinearMap.ker (K ∘ₗ A - s • LinearMap.id)
  have hm : ∀ x, x ∈ W' ↔ K (A x) = s • x := fun x => by simp [W', sub_eq_zero]
  let f : W →ₗ[ℝ] W' := LinearMap.codRestrict W' ((K ∘ₗ A + s • LinearMap.id) ∘ₗ W.subtype) (fun x => (hm _).2 (by
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, map_add,
      map_smul, Submodule.subtype_apply]
    rw [c (K (A x)), hK, map_neg, hA]
    module))
  refine LinearMap.finrank_le_finrank_of_injective (f := f) ?_
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  have hx0 : (x : V) ≠ 0 := fun h => h0 (Subtype.ext h)
  have h1 : J (A x) = s • (x : V) := by
    have : J (A x) - s • (x : V) = 0 := LinearMap.mem_ker.1 x.2
    exact sub_eq_zero.1 this
  have h2 : K (A x) = -(s • (x : V)) := by
    have := congrArg Subtype.val hx
    simpa [f, add_eq_zero_iff_eq_neg] using this
  have e1 : A x = -(s • J x) := by
    have := congrArg J h1
    rw [hJ, map_smul] at this
    rw [← this, neg_neg]
  have e2 : A x = s • K x := by
    have := congrArg K h2
    rw [hK, map_neg, map_smul] at this
    exact neg_injective this
  have b := congrArg (fun v => B v x) (e1.symm.trans e2)
  simp only [map_neg, map_smul, LinearMap.neg_apply, LinearMap.smul_apply, smul_eq_mul] at b
  have := mul_pos hs (pJ x hx0)
  have := mul_pos hs (pK x hx0)
  linarith

end Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

end GlobalTheory.DatumSign
