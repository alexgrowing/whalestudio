import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TensorProductVectors

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
open scoped TensorProduct

namespace UpperTheory.TNZ

theorem gEmb (e1 : TensorProductVectors) (e2 : LeviSubgroupRestriction) (e3 : ParabolicInductionKernel) (e4 : InducedDeterminantTwist)
    (e5 : InductionExtension) : GEmb := by
  intro k _ _ _ _ n G V _ _ π hπ
  obtain ⟨X, instA, instM, σ, -, -, hdet, ⟨e⟩⟩ := hπ
  let _ := instA
  let _ := instM
  obtain ⟨v, hv0, hv⟩ := e1 k G.s G.d X σ G.μ hdet
  choose F hF using fun φ : ↥G.V0sp => e5 e2 e3 k n G X σ v hv φ.1 φ.2
  have hadd : ∀ φ ψ, F (φ + ψ) = F φ + F ψ := fun φ ψ =>
    e4 k G.s n G.d G.hd _ (piTensor σ) _ _ fun κ hκ => by
      have h1 := hF (φ + ψ) ⟨κ, hκ⟩
      have h2 := hF φ ⟨κ, hκ⟩
      have h3 := hF ψ ⟨κ, hκ⟩
      change _ = (F φ).1.1 κ + (F ψ).1.1 κ
      rw [h1, h2, h3, ← add_smul]
      rfl
  have hsmul : ∀ (c : ℂ) φ, F (c • φ) = c • F φ := fun c φ =>
    e4 k G.s n G.d G.hd _ (piTensor σ) _ _ fun κ hκ => by
      have h1 := hF (c • φ) ⟨κ, hκ⟩
      have h2 := hF φ ⟨κ, hκ⟩
      change _ = c • (F φ).1.1 κ
      rw [h1, h2, smul_smul]
      rfl
  let f0 : ↥G.V0sp →ₗ[ℂ] IndSp G.e (piTensor σ) :=
    { toFun := F, map_add' := hadd, map_smul' := hsmul }
  refine ⟨e.symm.toLinearEquiv.toLinearMap ∘ₗ f0, fun φ ψ h => ?_, fun κ φ φ' hφ' => ?_⟩
  · have h' : F φ = F ψ := e.symm.toLinearEquiv.injective h
    refine Subtype.ext (funext fun κ => ?_)
    have h2 := congrArg (fun F : IndSp G.e (piTensor σ) => F.1.1 (κ : GL (Fin n) k)) h'
    simp only [hF] at h2
    exact smul_left_injective ℂ hv0 h2
  · have key : F φ' = parInd G.e (piTensor σ) (κ : GL (Fin n) k) (F φ) :=
      e4 k G.s n G.d G.hd _ (piTensor σ) _ _ fun x hx => by
        rw [hF φ' ⟨x, hx⟩, parInd_apply, hF φ ⟨x * κ, mul_mem hx κ.2⟩, hφ']
        rfl
    change e.symm.toLinearEquiv (F φ') = π κ (e.symm.toLinearEquiv (F φ))
    rw [key, Representation.Equiv.toLinearEquiv_apply, Representation.Equiv.toLinearEquiv_apply]
    exact Representation.IntertwiningMap.isIntertwining _ _ e.symm.toIntertwiningMap (κ : GL (Fin n) k) (F φ)

end UpperTheory.TNZ
