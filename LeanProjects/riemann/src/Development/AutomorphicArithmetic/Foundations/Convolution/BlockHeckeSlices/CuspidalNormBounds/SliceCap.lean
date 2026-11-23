import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.GoodSmul
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.UmgOps
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.SliceCapR
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliLeviFactorizationSum

noncomputable section

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.V.Cm

namespace UpperTheory.ConvolutionTheory.BW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

private theorem ex_capR (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) : ∃ x, uC E (r + s) x = capR r s τ u :=
  CapFactor.qdet_mem (uC E (r + s)).range _ (fun _ _ => ⟨_, uC_genC τ _ _⟩) _

private theorem ex_capS (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) : ∃ x, uC E (r + s) x = capS r s τ u :=
  CapFactor.qdet_mem (uC E (r + s)).range _ (fun _ _ => ⟨_, uC_genC τ _ _⟩) _

private theorem casimir_commute (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) : Commute (j1 E r s) (capS r s τ u) := by
  have h2 : capS r s τ u ∈ Subalgebra.centralizer ℂ {j1 E r s} := by
    refine CapFactor.qdet_mem _ _ (fun k l => ?_) _
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ rfl
    refine Commute.eq ?_
    unfold j1
    refine Commute.smul_left (Commute.sum_left _ _ _ fun σ _ => Commute.sum_left _ _ _ fun i _ => ?_) _
    by_cases h : σ = τ
    · subst h
      exact CapFactor.Eop_commute_blocks r s σ i i k l
    · rw [← uC_genC, ← uC_genC]
      exact (commute_genC h _ _ _ _).map _
  exact (Subalgebra.mem_centralizer_iff ℂ).1 h2 _ rfl

end UpperTheory.ConvolutionTheory.BW

open UpperTheory.ConvolutionTheory.BW in
theorem UpperTheory.ConvolutionTheory.BW.sliceCap :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.SliceCap E := by
  intro E _ _ _ S r s b t φ τ u hφ
  obtain ⟨F, hF, hN, -, hu⟩ := ctOps E r s φ hφ
  obtain ⟨x, hx⟩ := ex_capR r s τ (u - (s : ℂ) / 2)
  obtain ⟨y, hy⟩ := ex_capS r s τ (u + (r : ℂ) / 2)
  have h1 : slice b.f.1 t (cap τ u φ).1 =
      slice b.f.1 t (capR r s τ (u - (s : ℂ) / 2) (capS r s τ (u + (r : ℂ) / 2) φ)).1 := by
    funext m
    unfold slice
    congr 1
    funext z
    congr 1
    have e1 := hu (capC τ u)
    have e2 := hu (y * x)
    rw [uC_capC] at e1
    rw [map_mul, hx, hy] at e2
    have e3 : capR r s τ (u - (s : ℂ) / 2) (capS r s τ (u + (r : ℂ) / 2) φ) =
        (capS r s τ (u + (r : ℂ) / 2) * capR r s τ (u - (s : ℂ) / 2)) φ := by
      rw [← (CapFactor.capR_commute_capS r s τ _ _).eq]; rfl
    rw [← e1, e3, ← e2]
    exact CapFactor.cap_levi E r s τ u F hN _
  have hU : Umg (capS r s τ (u + (r : ℂ) / 2) φ) := by
    rw [← hy]; exact ((umgOps E (r + s)).2 φ hφ).2.2.2.1 y
  rw [h1, sliceCapR E S r s b t _ τ _ hU]
  congr 2
  have hc : Commute (Polynomial.aeval (j1 E r s) (∏ i, (Polynomial.X + Polynomial.C (u - (s : ℂ) / 2 + b.Λ τ i))))
      (capS r s τ (u + (r : ℂ) / 2)) := by
    generalize (∏ i, (Polynomial.X + Polynomial.C (u - (s : ℂ) / 2 + b.Λ τ i))) = p
    rw [Polynomial.aeval_eq_sum_range]
    exact Commute.sum_left _ _ _ fun i _ => ((casimir_commute r s τ _).pow_left i).smul_left _
  exact LinearMap.congr_fun hc.eq φ
