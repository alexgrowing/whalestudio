import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.SecondFromFirstStatement

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

namespace UpperTheory.V.Lit.Dr

private theorem hasDerivAt_evaluation_lie {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (Ξ : AlgRep E a)
    (X : Lie E a) (c : ℝ → GL (Fin a) (Cinf E)) (h0 : c 0 = 1) (hX : HasDerivAt (fun t => toL (c t).val) X 0)
    (h : GA E a) (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) :
    HasDerivAt (fun t => Ξ.mat (c t) *ᵥ ev m (h * infGL E a (c t))) (ev (smLie Ξ X m) h) 0 := by
  induction m using TensorProduct.induction_on with
  | zero => simpa using hasDerivAt_const (0 : ℝ) (0 : Fin Ξ.d → ℂ)
  | add x y hx hy =>
    simpa only [map_add, Pi.add_apply, Matrix.mulVec_add] using hx.fun_add hy
  | tmul φ v =>
    have h1 := GlobalTheory.CuspRep.hasDerivAt_curve φ h c X h0 hX
    have h2 : HasDerivAt (fun t => Ξ.mat (c t) *ᵥ v) (Ξ.dmat X *ᵥ v) 0 :=
      hasDerivAt_pi.2 fun j => HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
        (Ξ.hasDerivAt_curve c X h0 hX j i).mul_const (v i)
    have h3 := h1.fun_smul h2
    simp only [h0, map_one, mul_one, Matrix.one_mulVec] at h3
    have h4 : ev (smLie Ξ X (φ ⊗ₜ[ℂ] v)) h = φ.1 h • Ξ.dmat X *ᵥ v + lieD X φ.1 h • v := by
      change ev ((lie E a X φ) ⊗ₜ[ℂ] v + φ ⊗ₜ[ℂ] (Ξ.dmat X *ᵥ v)) h = _
      rw [map_add, Pi.add_apply, ev_tmul, ev_tmul, add_comm]
      rfl
    rw [h4]
    simpa only [ev_tmul, Matrix.mulVec_smul] using h3

theorem evDeriv : EvDeriv := by
  intro E _ _ _ a Ξ m g x c X h0 hX
  have h1 := (mulVecL (Ξ.mat g)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hasDerivAt_evaluation_lie Ξ X c h0 hX (infGL E a g * finGL E a x) m)
  refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  have e : infGL E a (g * c t) * finGL E a x = infGL E a g * finGL E a x * infGL E a (c t) := by
    rw [map_mul, mul_assoc, mul_assoc, infGL_comm]
  simp only [Function.comp, mulVecL_apply, e, map_mul (Ξ.mat), Matrix.mulVec_mulVec]

end UpperTheory.V.Lit.Dr
