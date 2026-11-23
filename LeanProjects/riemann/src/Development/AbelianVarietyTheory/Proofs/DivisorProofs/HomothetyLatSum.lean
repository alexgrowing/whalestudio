import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DTermOrigin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdNormSq

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

namespace GlobalTheory.HomothetyLatSum

variable {E : Type} [Field E] [NumberField E]

def mulQ (α : E) : Quotient (unitRel (E := E)) → Quotient (unitRel (E := E)) :=
  Quotient.map (fun x => α * x) (by rintro x x' ⟨u, h⟩; exact ⟨u, by rw [h]; ring⟩)

theorem mulQ_mk (α x : E) : mulQ α (Quotient.mk _ x) = Quotient.mk (unitRel (E := E)) (α * x) := rfl

theorem mulQ_mulQ (a b : E) (q : Quotient (unitRel (E := E))) : mulQ a (mulQ b q) = mulQ (a * b) q := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  rw [mulQ_mk, mulQ_mk, mulQ_mk, mul_assoc]

theorem mulQ_one (q : Quotient (unitRel (E := E))) : mulQ 1 q = q := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  rw [mulQ_mk, one_mul]

theorem mulQ_mem {α : E} (hα : α ≠ 0) {L : Set E} {q : Quotient (unitRel (E := E))} (hq : q ∈ modUnits L) :
    mulQ α q ∈ modUnits ((fun x => α * x) '' L) := by
  obtain ⟨x, hx, h0, rfl⟩ := hq
  exact ⟨α * x, ⟨x, hx, rfl⟩, mul_ne_zero hα h0, rfl⟩

theorem mulQ_inv_mem {α : E} (hα : α ≠ 0) {L : Set E} {q : Quotient (unitRel (E := E))}
    (hq : q ∈ modUnits ((fun x => α * x) '' L)) : mulQ α⁻¹ q ∈ modUnits L := by
  obtain ⟨_, ⟨x, hx, rfl⟩, h0, rfl⟩ := hq
  refine ⟨x, hx, fun h => h0 (by simp [h]), ?_⟩
  rw [mulQ_mk, inv_mul_cancel_left₀ hα]

def mulEquiv {α : E} (hα : α ≠ 0) (L : Set E) : modUnits L ≃ modUnits ((fun x => α * x) '' L) where
  toFun q := ⟨mulQ α q.1, mulQ_mem hα q.2⟩
  invFun q := ⟨mulQ α⁻¹ q.1, mulQ_inv_mem hα q.2⟩
  left_inv q := Subtype.ext (by simp only; rw [mulQ_mulQ, inv_mul_cancel₀ hα, mulQ_one])
  right_inv q := Subtype.ext (by simp only; rw [mulQ_mulQ, mul_inv_cancel₀ hα, mulQ_one])

variable {I : Type} [Fintype I]

theorem term_out_mulQ [IsCMField E] {φ : I → E →+* ℂ} (hφ : IsCMType φ) (s : ℕ) (κ : I → ℕ) (σ : ℂ) (α : E)
    (q : Quotient (unitRel (E := E))) :
    term φ (2 * s) κ σ (mulQ α q).out = term φ (2 * s) κ σ α * term φ (2 * s) κ σ q.out := by
  have h1 : mulQ α q = Quotient.mk _ (α * q.out) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  obtain ⟨u, hu⟩ := Quotient.exact ((Quotient.out_eq _).trans h1)
  rw [← term_mul, hu, (TermUnit.term_unit_and_norm E I φ hφ s κ σ _).1 u]

theorem term_eq_lamInf [IsCMField E] {φ : I → E →+* ℂ} (hφ : IsCMType φ) (s : ℕ) (κ : I → ℕ) (σ : ℂ) (α : Eˣ) :
    term φ (2 * s) κ σ α =
      (lamInf φ (2 * s) κ α)⁻¹ * ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-σ) := by
  have key : ∀ i, ((‖φ i α‖ : ℝ) : ℂ) ^ (-2 * σ) = (((‖φ i α‖ ^ 2 : ℝ)) : ℂ) ^ (-σ) := fun i => by
    have hp : 0 < ‖φ i α‖ := by simp
    have : (((‖φ i α‖ ^ 2 : ℝ)) : ℂ) = ((‖φ i α‖ : ℝ) : ℂ) * ((‖φ i α‖ : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.mul_cpow_ofReal_nonneg hp.le hp.le,
      ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 hp.ne')]
    congr 1; ring
  rw [← TermUnit.prod_norm_sq hφ, ← TermUnit.prod_cpow _ _ (fun i => by positivity)]
  unfold term lamInf
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [key]
  have gen : ∀ (a c N : ℂ) (m n : ℕ), a⁻¹ ^ m * c ^ n * N = (a ^ m * c⁻¹ ^ n)⁻¹ * N := by
    intro a c N m n
    rw [mul_inv, inv_pow, inv_pow, inv_inv]
  exact gen _ _ _ _ _

theorem homothety (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I]
    (φ : I → E →+* ℂ) (hφ : IsCMType φ) (s : ℕ) (L : Set E) : Homothety φ (2 * s) L := by
  intro κ α S hS
  have hα : (α : E) ≠ 0 := α.ne_zero
  have hN : ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, abs_ne_zero, Rat.cast_ne_zero, Algebra.norm_ne_zero_iff]; exact hα
  have key : IsLatSum φ (2 * s) κ ((fun x => (α : E) * x) '' L)
      (fun σ => (lamInf φ (2 * s) κ α)⁻¹ * ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-σ) * S σ) := by
    refine ⟨?_, fun σ hσ => ?_⟩
    · exact ((differentiable_neg.const_cpow (Or.inl hN)).const_mul _).mul hS.1
    · have h1 := (hS.2 σ hσ).mul_left
        ((lamInf φ (2 * s) κ α)⁻¹ * ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-σ))
      have hf : ((fun q' : modUnits ((fun x => (α : E) * x) '' L) => term φ (2 * s) κ σ q'.1.out) ∘ mulEquiv hα L) =
          fun q : modUnits L => (lamInf φ (2 * s) κ α)⁻¹ * ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-σ) *
            term φ (2 * s) κ σ q.1.out := funext fun q => by
        show term φ (2 * s) κ σ (mulQ (α : E) q.1).out = _
        rw [term_out_mulQ hφ, term_eq_lamInf hφ]
      rw [← (mulEquiv hα L).hasSum_iff, hf]
      exact h1
  refine ⟨key, fun S' hS' => ?_⟩
  rw [hS'.unique key]
  simp

end GlobalTheory.HomothetyLatSum
