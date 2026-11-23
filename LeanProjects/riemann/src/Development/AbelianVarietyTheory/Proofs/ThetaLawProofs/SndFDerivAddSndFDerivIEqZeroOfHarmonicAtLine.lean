import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsEventuallyNormRiemannThetaTermLe

noncomputable section

open Complex Matrix

namespace GlobalTheory

open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

end General

variable {g : ℕ}

open Complex Matrix in
variable {g : ℕ} in

theorem _root_.GlobalTheory.isSymm_phSym (x : Matrix (Fin g) (Fin g) ℂ) : (_root_.ReciprocityTheory.ChartRestriction.G.Key.phSym x).IsSymm := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym
  ext i j
  simp only [transpose_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

open Complex Matrix in
variable {g : ℕ} in

theorem _root_.GlobalTheory.phSym_eq_self_of_isSymm {x : Matrix (Fin g) (Fin g) ℂ} (hx : x.IsSymm) :
    _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym x = x := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym
  rw [hx.eq, ← two_smul ℂ x, smul_smul]
  norm_num

open Complex Matrix in
variable {g : ℕ} in

theorem _root_.GlobalTheory.differentiable_phSym_coords :
    Differentiable ℂ (fun x : Fin g → Fin g → ℂ =>
      (Matrix.of.symm (_root_.ReciprocityTheory.ChartRestriction.G.Key.phSym (Matrix.of x)) : Fin g → Fin g → ℂ)) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym
  refine differentiable_pi.2 fun i => differentiable_pi.2 fun j => ?_
  simp only [Matrix.of_symm_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
    Matrix.of_apply, smul_eq_mul]
  fun_prop

open Complex Matrix in
variable {g : ℕ} in

theorem _root_.GlobalTheory.isOpen_phDom (g : ℕ) : IsOpen (_root_.ReciprocityTheory.ChartRestriction.G.Key.phDom g) := by
  have hc : Continuous (fun x : Fin g → Fin g → ℂ => _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym (Matrix.of x)) := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym; fun_prop
  rw [isOpen_iff_mem_nhds]
  intro x hx
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.phDom at hx ⊢
  have hx' : _root_.GlobalTheory.IsSiegel (_root_.ReciprocityTheory.ChartRestriction.G.Key.phSym (Matrix.of x)) := _root_.GlobalTheory.isSiegel_iff_mem_siegelH.2 hx
  have h := hc.continuousAt.eventually hx'.eventually_isSiegel
  filter_upwards [h] with y hy
  exact _root_.GlobalTheory.isSiegel_iff_mem_siegelH.1 (hy (_root_.GlobalTheory.isSymm_phSym _))

open Complex Matrix in
variable {g : ℕ} in
private theorem convex_siegelH (g : ℕ) : Convex ℝ (_root_.ReciprocityTheory.PTheta.SiegelH (Fin g)) := by
  intro A hA B hB a b ha hb hab
  rw [← _root_.GlobalTheory.isSiegel_iff_mem_siegelH] at *
  refine ⟨?_, ?_⟩
  · exact (hA.isSymm.smul a).add (hB.isSymm.smul b)
  · have hm : ((a • A + b • B).map Complex.im) = a • A.map Complex.im + b • B.map Complex.im := by
      ext i j; simp
    rw [hm]
    rcases ha.eq_or_lt with rfl | ha'
    · simp at hab; subst hab; simpa using hB.posDef
    · exact (hA.posDef.smul ha').add_posSemidef (hB.posDef.posSemidef.smul hb)

open Complex Matrix in
variable {g : ℕ} in

theorem _root_.GlobalTheory.convex_phDom (g : ℕ) : Convex ℝ (_root_.ReciprocityTheory.ChartRestriction.G.Key.phDom g) := by
  have hl : IsLinearMap ℝ (fun x : Fin g → Fin g → ℂ => _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym (Matrix.of x)) := by
    constructor
    · intro x y; unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym; ext i j; simp; ring
    · intro c x; unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym; ext i j; simp; ring
  have := (convex_siegelH g).is_linear_preimage hl
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.phDom
  exact this

open Complex Matrix in
variable {g : ℕ} in

theorem _root_.GlobalTheory.of_symm_mem_phDom {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g)) :
    (Matrix.of.symm τ : Fin g → Fin g → ℂ) ∈ _root_.ReciprocityTheory.ChartRestriction.G.Key.phDom g := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.phDom
  show _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym (Matrix.of (Matrix.of.symm τ)) ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g)
  rw [Equiv.apply_symm_apply,
    _root_.GlobalTheory.phSym_eq_self_of_isSymm (_root_.GlobalTheory.isSiegel_iff_mem_siegelH.2 hτ).isSymm]
  exact hτ

end GlobalTheory
