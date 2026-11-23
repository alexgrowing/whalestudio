import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.GardFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ClFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.SkewLieActionL2
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.casSym :
    UpperTheory.V.Cj.H.CasSym := by
  intro E _ _ _ a ha μ _ _ n e c
  have hG := gardFacts E a ha μ
  have hC := (clFacts E a μ).1
  have hcomb : ∀ (s t : ℂ), ∀ φ ∈ gard μ, ∀ ψ ∈ gard μ, cl μ (s • φ + t • ψ) = s • cl μ φ + t • cl μ ψ :=
    fun s t φ hφ ψ hψ => (hC φ ψ s t (hG φ hφ).2.1 (hG ψ hψ).2.1).2
  have hL : ∀ X, ∀ φ ∈ gard μ, lie E a X φ ∈ gard μ := fun X φ hφ => (hG φ hφ).2.2.2.1 X
  have hskew : ∀ X, ∀ φ ∈ gard μ, ∀ ψ ∈ gard μ,
      inner ℂ (cl μ (lie E a X φ)) (cl μ ψ) = -inner ℂ (cl μ φ) (cl μ (lie E a X ψ)) := by
    intro X φ hφ ψ hψ
    have h := skew_lie_action_L2 E a μ X φ ψ (hG φ hφ).1 (hG ψ hψ).1 (hG φ hφ).2.1 (hG ψ hψ).2.1
      (hG _ (hL X φ hφ)).2.1 (hG _ (hL X ψ hψ)).2.1
    rw [cl_eq (hG φ hφ).2.1, cl_eq (hG ψ hψ).2.1, cl_eq (hG _ (hL X φ hφ)).2.1, cl_eq (hG _ (hL X ψ hψ)).2.1]
    exact eq_neg_of_add_eq_zero_left h
  let P : Module.End ℂ (Sm E a) → Prop := fun T => (∀ φ ∈ gard μ, T φ ∈ gard μ) ∧
    ∀ φ ∈ gard μ, ∀ ψ ∈ gard μ, inner ℂ (cl μ (T φ)) (cl μ ψ) = inner ℂ (cl μ φ) (cl μ (T ψ))
  have hP1 : P 1 := ⟨fun _ h => h, fun _ _ _ _ => rfl⟩
  have hPc : ∀ (s t : ℝ) (T S : Module.End ℂ (Sm E a)), P T → P S → P ((s : ℂ) • T + (t : ℂ) • S) := by
    intro s t T S hT hS
    refine ⟨fun φ hφ => ?_, fun φ hφ ψ hψ => ?_⟩
    · exact add_mem (Submodule.smul_mem _ _ (hT.1 φ hφ)) (Submodule.smul_mem _ _ (hS.1 φ hφ))
    · change inner ℂ (cl μ ((s : ℂ) • T φ + (t : ℂ) • S φ)) (cl μ ψ) =
        inner ℂ (cl μ φ) (cl μ ((s : ℂ) • T ψ + (t : ℂ) • S ψ))
      rw [hcomb _ _ _ (hT.1 φ hφ) _ (hS.1 φ hφ), hcomb _ _ _ (hT.1 ψ hψ) _ (hS.1 ψ hψ), inner_add_left,
        inner_add_right, inner_smul_left, inner_smul_left, inner_smul_right, inner_smul_right, Complex.conj_ofReal,
        Complex.conj_ofReal, hT.2 φ hφ ψ hψ, hS.2 φ hφ ψ hψ]
  have hP0 : P 0 := by
    have h := hPc 0 0 1 1 hP1 hP1
    simpa using h
  have hPa : ∀ T S, P T → P S → P (T + S) := fun T S hT hS => by
    have h := hPc 1 1 T S hT hS
    simpa using h
  have hPs : ∀ (t : ℝ) T S, P T → P S → P (T - (t : ℂ) • S) := fun t T S hT hS => by
    have h := hPc 1 (-t) T S hT hS
    rwa [Complex.ofReal_one, one_smul, Complex.ofReal_neg, neg_smul, ← sub_eq_add_neg] at h
  have hPsq : ∀ X, P (lie E a X * lie E a X) := fun X =>
    ⟨fun φ hφ => hL X _ (hL X φ hφ), fun φ hφ ψ hψ => by
      change inner ℂ (cl μ (lie E a X (lie E a X φ))) (cl μ ψ) = inner ℂ (cl μ φ) (cl μ (lie E a X (lie E a X ψ)))
      rw [hskew X _ (hL X φ hφ) ψ hψ, hskew X φ hφ _ (hL X ψ hψ), neg_neg]⟩
  have hsh : shift (lie E a) 0 = lie E a := by
    refine LinearMap.ext fun X => ?_
    rw [shift_apply, zero_mul, zero_smul, add_zero]
  have hcas : P (casA 0 c e) := by
    unfold casA
    rw [hsh]
    refine hPs c _ _ ?_ hP1
    unfold cas
    refine Finset.sum_induction _ P hPa hP0 fun j _ => ?_
    have h := hPs 1 _ _ (hPsq (toL (e j).1)) (hPsq (toL (Complex.I • (e j).1)))
    rwa [Complex.ofReal_one, one_smul] at h
  exact hcas.2
