import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConjugateTransposeLeibniz.YOperatorLeibnizRule
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.LogDetSt

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.DetLeibniz

open Matrix QnYLeibnizW

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem trace_adjugate_mul_eq_sum_cramer {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    (A.adjugate * B).trace = ∑ j, A.cramer (fun i => B i j) j := by
  simp only [Matrix.trace, Matrix.diag]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [cramer_eq_adjugate_mulVec]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem hasDerivAt_det_Zhat (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g X : Q.Mx k r) :
    HasDerivAt (fun t : ℝ => (Zhat k r z z' (g * NormedSpace.exp ((t : ℂ) • X))).det)
      ((Zhat k r z z' g).adjugate * Zhat k r z z' (g * X)).trace 0 := by
  have h := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det (fun t : ℝ => Zhat k r z z' (g * NormedSpace.exp ((t : ℂ) • X)))
    (Zhat k r z z' (g * X)) 0 (fun i j =>
      (hermL (Hpk k r) (fvec k r z' j) (fvec k r z i)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
        (hasDerivAt_mul_exp_smul_zero g X))
  simp only [curve_zero] at h
  exact h

theorem Zhat_add_smul (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (A B : Q.Mx k r) (c : ℂ) :
    Zhat k r z z' (A + c • B) = Zhat k r z z' A + c • Zhat k r z z' B := by
  ext i j
  simp [Zhat, herm, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
    dotProduct_smul]

theorem Zhat_mul_single (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r)
    (p q : Fin (2 * r + k + 1)) (j : Fin (r + 1)) :
    (fun i => Zhat k r z z' (g * Matrix.single p q 1) i j) =
      fvec k r z' j q • fun i => herm (Hpk k r) (g *ᵥ bvec p) (fvec k r z i) := by
  have hv : Matrix.single p q (1 : ℂ) *ᵥ fvec k r z' j = fvec k r z' j q • bvec p := by
    rw [Matrix.single_mulVec]
    funext l
    by_cases h : l = p
    · subst h; simp [bvec]
    · simp [bvec, h]
  funext i
  simp only [Zhat, Pi.smul_apply, ← Matrix.mulVec_mulVec, hv, herm, Matrix.mulVec_smul, dotProduct_smul]

theorem det_leibniz : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (D : Set (Q.Mx k r)) (a b : Fin (Q.mdim k r 0)) (f : Q.Mx k r → E), Q.SmoothLev k r 0 D f → ∀ g ∈ Q.Glev k r 0 ∩ D, Q.EH k r (Q.posL k r 0 a) (Q.posL k r 0 b) (fun x => (Zhat k r z z' x).det • f x) g = (Zhat k r z z' g).det • Q.EH k r (Q.posL k r 0 a) (Q.posL k r 0 b) f g + (∑ j : Fin (r + 1), fvec k r z' j (Q.posL k r 0 b) * (Zhat k r z z' g).cramer (fun i => herm (Hpk k r) (g.mulVec (bvec (Q.posL k r 0 a))) (fvec k r z i)) j) • f g := by
  intro E _ _ k r z z' D a b f hf g hg
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  have hgG : g ∈ Q.Glev k r 0 := hg.1
  obtain ⟨hX1, hX2⟩ := hpart_mem (k := k) (r := r) (i := 0) a b
  set Z : Q.Mx k r := Matrix.single (Q.posL k r 0 a) (Q.posL k r 0 b) 1 with hZdef
  set X1 := hpart1 (Hpk k r) Z with hX1def
  set X2 := hpart2 (Hpk k r) Z with hX2def
  have hf1 := hasDerivAt_f f F U g X1 hU hgU hgG hF hfF hX1
  have hf2 := hasDerivAt_f f F U g X2 hU hgU hgG hF hfF hX2
  have hEf : Q.EH k r (Q.posL k r 0 a) (Q.posL k r 0 b) f g =
      fderiv ℝ F g (g * X1) + Complex.I • fderiv ℝ F g (g * X2) := by
    show RdV X1 f g + Complex.I • RdV X2 f g = _
    rw [rdV_of_hasDerivAt X1 g f _ hf1, rdV_of_hasDerivAt X2 g f _ hf2]
  have key : ∀ (φ : Q.Mx k r → ℂ) (d1 d2 : ℂ),
      HasDerivAt (fun t : ℝ => φ (g * NormedSpace.exp ((t : ℂ) • X1))) d1 0 →
      HasDerivAt (fun t : ℝ => φ (g * NormedSpace.exp ((t : ℂ) • X2))) d2 0 →
      Q.EH k r (Q.posL k r 0 a) (Q.posL k r 0 b) (fun x => φ x • f x) g =
        φ g • Q.EH k r (Q.posL k r 0 a) (Q.posL k r 0 b) f g + (d1 + Complex.I * d2) • f g := by
    intro φ d1 d2 h1 h2
    rw [hEf]
    show RdV X1 (fun x => φ x • f x) g + Complex.I • RdV X2 (fun x => φ x • f x) g = _
    rw [rdV_smul_of X1 g φ f d1 _ h1 hf1, rdV_smul_of X2 g φ f d2 _ h2 hf2]
    module
  rw [key (fun x => (Zhat k r z z' x).det) _ _ (hasDerivAt_det_Zhat k r z z' g X1)
    (hasDerivAt_det_Zhat k r z z' g X2)]
  have hsum : g * X1 + Complex.I • (g * X2) = g * Z := by
    rw [← Matrix.mul_smul, ← Matrix.mul_add, hX1def, hX2def, hpart_sum]
  have hd : ((Zhat k r z z' g).adjugate * Zhat k r z z' (g * X1)).trace +
      Complex.I * ((Zhat k r z z' g).adjugate * Zhat k r z z' (g * X2)).trace =
      ((Zhat k r z z' g).adjugate * Zhat k r z z' (g * Z)).trace := by
    rw [← hsum, Zhat_add_smul, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  rw [hd, trace_adjugate_mul_eq_sum_cramer]
  congr 2
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hZdef, Zhat_mul_single, map_smul, Pi.smul_apply, smul_eq_mul]

end GlobalTheory.HatNF.DetLeibniz
