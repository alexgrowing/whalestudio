import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIso

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil Module

set_option linter.all false

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem eps_ind_step {E L Ω : Type} [Field E] [NumberField E] [Field L] [NumberField L] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra E L] [IsScalarTower E L Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) {v : HeightOneSpectrum (𝓞 L)}
    (hv : IsPlaceOver A v) (hL : IsLocalExt L h) {ε : EpsFamily A} (hε : IsDeligneEps ε)
    {ψ : AddChar (w.adicCompletion E) Circle} (hc : Continuous ψ) (h1 : ψ ≠ 1)
    {ψL : AddChar (v.adicCompletion L) Circle} (hcL : Continuous ψL)
    (hψL : ∀ z : L, ψL (algebraMap L _ z) = ψ (algebraMap E _ (Algebra.trace E L z)))
    (r : Weil hv →* Weil h) (hr : ∀ (σ : Weil hv) (z : Ω), (r σ : G E Ω) z = (σ : G L Ω) z)
    (hrs : ∀ (M : Type) [Monoid M] (f : Weil h →* M), IsSmooth f → IsSmooth (f.comp r))
    {m : ℕ} (hm : m = Module.finrank E L) (b : WDRep h (Fin m → ℂ)) (v₀ : Fin m → ℂ)
    (hsp : Submodule.span ℂ (Set.range fun σ => b.ρ σ v₀) = ⊤)
    (ξL₀ : Weil hv →* ℂˣ) (hξ : ∀ σ, b.ρ (r σ) v₀ = (ξL₀ σ : ℂ) • v₀)
    (ν₁ ν₂ : Weil h →* ℂˣ) (hν₁ : IsSmooth ν₁) (hν₂ : IsSmooth ν₂) :
    ∃ (hs₁ : IsSmooth (ξL₀ * ν₁.comp r)) (hs₂ : IsSmooth (ξL₀ * ν₂.comp r)),
      ε E w h ψ (WD.mk (b.twist ν₁ hν₁)) * ε L v hv ψL (WD.lpOfChar hv (ξL₀ * ν₂.comp r) hs₂) =
        ε E w h ψ (WD.mk (b.twist ν₂ hν₂)) * ε L v hv ψL (WD.lpOfChar hv (ξL₀ * ν₁.comp r) hs₁) := by
  have key : ∀ (ν : Weil h →* ℂˣ) (hν : IsSmooth ν), ∃ hs : IsSmooth (ξL₀ * ν.comp r),
      Induces (WD.lpOfChar hv (ξL₀ * ν.comp r) hs) (WD.mk (b.twist ν hν)) := by
    intro ν hν
    refine EpsUnique.induces_of_eigenvector E L Ω A w v h hv r hr hrs m (b.twist ν hν) v₀ (ξL₀ * ν.comp r) hm
      (fun σ => ?_) ?_
    · rw [WDRep.twist_ρ, LinearMap.smul_apply, hξ, smul_smul, MonoidHom.mul_apply, Units.val_mul,
        MonoidHom.comp_apply, mul_comm]
    · rw [eq_top_iff, ← hsp]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨σ, rfl⟩
      have e : b.ρ σ v₀ = ((ν σ)⁻¹ : ℂˣ) • ((b.twist ν hν).ρ σ v₀) := by
        rw [WDRep.twist_ρ, LinearMap.smul_apply, Units.smul_def, smul_smul, ← Units.val_mul, inv_mul_cancel,
          Units.val_one, one_smul]
      show b.ρ σ v₀ ∈ Submodule.span ℂ (Set.range fun σ => (b.twist ν hν).ρ σ v₀)
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ, rfl⟩)
  obtain ⟨hs₁, i₁⟩ := key ν₁ hν₁
  obtain ⟨hs₂, i₂⟩ := key ν₂ hν₂
  refine ⟨hs₁, hs₂, ?_⟩
  have d : (WD.lpOfChar hv (ξL₀ * ν₁.comp r) hs₁).lpDim = (WD.lpOfChar hv (ξL₀ * ν₂.comp r) hs₂).lpDim := by
    simp [WD.lpOfChar]
  exact hε.ind E L w v h hv hL ψ ψL hc h1 hcL hψL _ _ _ _ i₁ i₂ d

end DiscreteGroups.sglob.DzType

end
