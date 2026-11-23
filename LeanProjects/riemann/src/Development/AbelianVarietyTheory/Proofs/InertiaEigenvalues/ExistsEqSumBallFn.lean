import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient

noncomputable section

open ValuativeRel OnePoint

namespace GlobalTheory.LocGL.ProjLine

variable {k : Type} [Field k] [ValuativeRel k]

def Stable (S : Submodule ℂ (OnePoint k → ℂ)) : Prop :=
  (∀ F ∈ S, ∀ a b : k, a ≠ 0 → ∀ F' : OnePoint k → ℂ, F' ∞ = F ∞ →
    (∀ x : k, F' x = F ((a * x + b : k) : OnePoint k)) → F' ∈ S) ∧
  ∀ F ∈ S, ∀ F' : OnePoint k → ℂ, F' ∞ = F ((0 : k) : OnePoint k) → F' ((0 : k) : OnePoint k) = F ∞ →
    (∀ x : k, x ≠ 0 → F' x = F ((x⁻¹ : k) : OnePoint k)) → F' ∈ S

open Classical in

def ballFn (a r : k) : OnePoint k → ℂ := fun x =>
  x.elim 0 fun y => if valuation k (y - a) ≤ valuation k r then 1 else 0

@[simp] theorem ballFn_infty (a r : k) : ballFn a r ∞ = 0 := rfl

open Classical in

theorem ballFn_coe (a r x : k) :
    ballFn a r x = if valuation k (x - a) ≤ valuation k r then 1 else 0 := rfl

theorem Stable.ballFn_mem {S : Submodule ℂ (OnePoint k → ℂ)} (hS : Stable S) {a r : k} (hr : r ≠ 0)
    (h : ballFn a r ∈ S) (b : k) {s : k} (hs : s ≠ 0) : ballFn b s ∈ S := by
  refine hS.1 _ h (r / s) (a - r / s * b) (div_ne_zero hr hs) _ rfl fun x => ?_
  have h1 : r / s * x + (a - r / s * b) - a = r * ((x - b) / s) := by field_simp; ring
  have h2 : valuation k r ≠ 0 := by simpa using hr
  have h3 : 0 < valuation k s := zero_lt_iff.2 (by simpa using hs)
  rw [ballFn_coe, ballFn_coe, h1, map_mul, map_div₀]
  congr 1
  rw [mul_le_iff_le_one_right (zero_lt_iff.2 h2), div_le_one₀ h3]

def vball (r : k) : AddSubgroup k where
  carrier := {x | valuation k x ≤ valuation k r}
  add_mem' {a b} hx hy := show valuation k (a + b) ≤ valuation k r from (valuation k).map_add_le hx hy
  zero_mem' := by simp
  neg_mem' hx := by simpa using hx

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isOpen_vball {r : k} (hr : r ≠ 0) : IsOpen (vball r : Set k) := by
  have ho : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer
  have h3 : 0 < valuation k r := zero_lt_iff.2 (by simpa using hr)
  convert ho.preimage (continuous_id.div_const r) using 1
  ext x
  show valuation k x ≤ valuation k r ↔ valuation k (x / r) ≤ 1
  rw [map_div₀, div_le_one₀ h3]

theorem exists_vball_subset {U : Set k} (hU : U ∈ nhds (0 : k)) :
    ∃ r : k, r ≠ 0 ∧ ∀ x, valuation k x ≤ valuation k r → x ∈ U := by
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff U).1 hU
  obtain ⟨s, hs⟩ := valuation_surjective (γ : ValueGroupWithZero k)
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer k
  have h0 : s ≠ 0 := by rintro rfl; exact γ.ne_zero (by simpa using hs.symm)
  refine ⟨ϖ * s, mul_ne_zero ϖ.ne_zero h0, fun x hx => hγ (hx.trans_lt ?_)⟩
  rw [map_mul, hs, hϖ]
  exact mul_lt_of_lt_one_left γ.zero_lt uniformizer_lt_one

theorem exists_eq_sum_ballFn {r R : k} (hr : r ≠ 0) (hle : valuation k r ≤ valuation k R) :
    ∃ T : Finset k, (∀ a ∈ T, valuation k a ≤ valuation k R) ∧
      (valuation k r < valuation k R → 1 < T.card) ∧
      ∀ F : OnePoint k → ℂ, F ∞ = 0 → (∀ x : k, valuation k R < valuation k x → F x = 0) →
        (∀ x b : k, valuation k b ≤ valuation k r → F ((x + b : k) : OnePoint k) = F x) →
        F = ∑ a ∈ T, F a • ballFn a r := by
  classical
  let A : AddSubgroup k := vball R
  let B : AddSubgroup k := vball r
  have hA : IsCompact (A : Set k) := IsNonarchimedeanLocalField.isCompact_closedBall k (valuation k R)
  have hB : IsOpen (B : Set k) := isOpen_vball hr
  haveI : CompactSpace A := isCompact_iff_compactSpace.1 hA
  haveI := (B.addSubgroupOf A).quotient_finite_of_isOpen (hB.preimage continuous_subtype_val)
  haveI := Fintype.ofFinite (A ⧸ B.addSubgroupOf A)
  let o : A ⧸ B.addSubgroupOf A → k := fun q => q.out
  have ho : Function.Injective o := fun p q h => Quotient.out_injective (Subtype.ext h)
  have key : ∀ (q : A ⧸ B.addSubgroupOf A) (x : A), valuation k (x - o q) ≤ valuation k r ↔ q = x := fun q x => by
    conv_rhs => rw [← q.out_eq']
    rw [QuotientAddGroup.eq, sub_eq_neg_add]
    rfl
  refine ⟨Finset.univ.image o, fun a ha => ?_, fun h => ?_, fun F h0 h1 h2 => funext fun x => ?_⟩
  · obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 ha
    exact q.out.2
  · rw [Finset.card_image_of_injective _ ho, Finset.card_univ, Fintype.one_lt_card_iff]
    refine ⟨(0 : A), (⟨R, show valuation k R ≤ valuation k R from le_rfl⟩ : A), fun e => h.not_ge ?_⟩
    have h5 := QuotientAddGroup.eq.1 e
    have h4 : -(0 : k) + R ∈ B := h5
    rwa [neg_zero, zero_add] at h4
  · rw [Finset.sum_image ho.injOn, Finset.sum_apply]
    induction x using OnePoint.rec with
    | infty => simp [h0]
    | coe x =>
      by_cases hx : valuation k x ≤ valuation k R
      · simp only [Pi.smul_apply, ballFn_coe, key _ ⟨x, hx⟩, smul_eq_mul, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
        exact (congrArg F (by simp)).trans (h2 _ _ ((key _ ⟨x, hx⟩).2 rfl))
      · rw [h1 x (not_le.1 hx), Finset.sum_eq_zero]
        intro q _
        rw [Pi.smul_apply, ballFn_coe, if_neg, smul_zero]
        intro h
        have h3 : x - o q + o q ∈ A := A.add_mem (h.trans hle) q.out.2
        rw [sub_add_cancel] at h3
        exact hx h3

end GlobalTheory.LocGL.ProjLine
