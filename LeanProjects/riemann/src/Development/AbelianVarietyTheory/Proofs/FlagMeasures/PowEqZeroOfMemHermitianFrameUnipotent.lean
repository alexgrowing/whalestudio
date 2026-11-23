import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.FlagUnipotent

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem hf_sub_left (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L H (a - b) y = hf L H a y - hf L H b y := by
  simp [hf, sub_mul, Finset.sum_sub_distrib]

theorem hf_sub_right (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (x a b : Fin n → E) :
    hf L H x (a - b) = hf L H x a - hf L H x b := by
  simp [hf, mul_sub, Finset.sum_sub_distrib]

theorem pow_eq_zero_of_mem_Nof {L : LocE F E} {r k : ℕ} (S : Frames L r k)
    (f : Fin (r + 1) → S.V) (g : S.GLV) (hg : g ∈ S.Nof f) :
    ((g : S.V →ₗ[E] S.V) - 1) ^ (2 * r + 1) = 0 := by
  obtain ⟨⟨hiso, hfl⟩, hmid⟩ := hg
  have hfl' : ∀ j, j < r → g ∈ unipOn (S.spanTo f (j + 1)) (S.spanTo f j) := fun j hj =>
    (Subgroup.mem_iInf.1 hfl) ⟨j, hj⟩
  set A : S.V →ₗ[E] S.V := (g : S.V →ₗ[E] S.V) - 1 with hA
  have hAv : ∀ v, A v = g v - v := fun v => rfl
  have h0 : S.spanTo f 0 = ⊥ := by simp [Frames.spanTo]
  have ha : ∀ j, j ≤ r → ∀ v, (A ^ j) v ∈ perp L S.Hm (S.spanTo f j) := by
    intro j
    induction j with
    | zero =>
      intro _ v y hy
      rw [h0, Submodule.mem_bot] at hy
      simp [hy, hf]
    | succ j ih =>
      intro hj v x hx
      obtain ⟨h1, h2⟩ := hfl' j hj
      have hw := ih (by omega) v
      rw [pow_succ', Module.End.mul_apply, hAv]
      generalize (A ^ j) v = w at hw
      obtain ⟨y, rfl⟩ := g.surjective x
      have h3 : hf L S.Hm w (g y - y) = 0 := hw _ (h2 y ((h1 y).1 hx))
      have h4 : hf L S.Hm (g w) (g y) = hf L S.Hm w y := hiso w y
      rw [hf_sub_right] at h3
      rw [hf_sub_left, h4]
      linear_combination -h3
  have hc : ∀ j, j ≤ r → ∀ v ∈ S.spanTo f j, (A ^ j) v = 0 := by
    intro j
    induction j with
    | zero =>
      intro _ v hv
      rw [h0, Submodule.mem_bot] at hv
      simp [hv]
    | succ j ih =>
      intro hj v hv
      rw [pow_succ, Module.End.mul_apply, hAv]
      exact ih (by omega) _ ((hfl' j hj).2 v hv)
  refine LinearMap.ext fun v => ?_
  have e : 2 * r + 1 = r + (1 + r) := by omega
  rw [e, pow_add, pow_add, pow_one, Module.End.mul_apply, Module.End.mul_apply, hAv]
  exact hc r le_rfl _ (hmid.2 _ (ha r le_rfl v))

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ g ∈ S.N, ((g : S.V →ₗ[E] S.V) - 1) ^ (2 * r + 1) = 0 :=
  fun _ _ _ S g hg => pow_eq_zero_of_mem_Nof S S.f g hg

end GlobalTheory.FlagUnipotent
