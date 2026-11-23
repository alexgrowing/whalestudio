import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.MixSeedPAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.DenseRangeUnitsR
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.SphPlain

open NumberField IsDedekindDomain GlobalTheory.LocGL GlobalTheory.SmGL GlobalTheory.CuspRep GlobalTheory.LocLanglands Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open UpperTheory.V UpperTheory.V.Af

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open private expo_intR sys_twist from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.DenseRangeUnitsR

namespace UpperTheory.V.Z.Win.Birth

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem plainTor_tw {x : IrrGL k} (h : GlobalTheory.RoadU.PlainTor x) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    GlobalTheory.RoadU.PlainTor (x.tw χ hχ) := by
  obtain ⟨s, hs, h1, hu⟩ := h
  refine ⟨s.map (·.tw χ hχ), (hs.tw χ hχ).of_equiv (x.twEquiv χ hχ), ?_, ?_⟩
  · intro y hy
    obtain ⟨y', hy', rfl⟩ := Multiset.mem_map.1 hy
    exact h1 y' hy'
  · intro y hy z hz e
    obtain ⟨y', hy', rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨z', hz', rfl⟩ := Multiset.mem_map.1 hz
    rw [IrrGL.tw_nu] at e
    have hinv : IsSmoothChar χ⁻¹ := hχ.inv
    have e2 := congrArg (·.tw χ⁻¹ hinv) e
    simp only [IrrGL.tw_tw, mul_inv_cancel, IrrGL.tw_one] at e2
    exact hu y' hy' z' hz' e2

end Local

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

private theorem plainAtR_twist {π : TR.CuspSub F n} {v : HeightOneSpectrum (𝓞 F)} (h : PlainAtR π v) (χ : HChar F) :
    PlainAtR (π.twist χ) v := by
  intro σ hσ
  have e : (π.twist χ).twist χ⁻¹ = π := by
    rw [← TR.CuspSub.twist_mul, mul_inv_cancel, TR.CuspSub.twist_one]
  have h1 := hσ.twist χ⁻¹
  rw [e] at h1
  have h2 := h _ h1
  have hsm := GlobalTheory.HeckeComp.smooth_loc χ⁻¹ v
  have hsm' := GlobalTheory.HeckeComp.smooth_loc χ v
  have h3 : IrrGL.of (σ.twist (CuspSub.locDet n χ⁻¹ v) (TR.CuspSub.isOpen_ker_locDet χ⁻¹ v)).ρ
      (σ.twist (CuspSub.locDet n χ⁻¹ v) (TR.CuspSub.isOpen_ker_locDet χ⁻¹ v)).smooth
      (σ.twist (CuspSub.locDet n χ⁻¹ v) (TR.CuspSub.isOpen_ker_locDet χ⁻¹ v)).irred =
      (IrrGL.of σ.ρ σ.smooth σ.irred).tw (χ⁻¹.loc v) hsm :=
    (IrrGL.tw_of σ.ρ σ.smooth σ.irred _ hsm).symm
  rw [h3] at h2
  have h4 := plainTor_tw h2 (χ.loc v) hsm'
  rw [IrrGL.tw_tw] at h4
  have e3 : χ⁻¹.loc v * χ.loc v = 1 := MonoidHom.ext fun x => by
    change (χ.loc v x)⁻¹ * χ.loc v x = 1
    simp
  have key : ∀ (c : (v.adicCompletion F)ˣ →* ℂˣ) (hc : IsSmoothChar c), c = 1 →
      (IrrGL.of σ.ρ σ.smooth σ.irred).tw c hc = IrrGL.of σ.ρ σ.smooth σ.irred := by
    rintro _ hc rfl
    exact IrrGL.tw_one _ _
  rwa [key _ _ e3] at h4

end UpperTheory.V.Z.Win.Birth

theorem UpperTheory.V.Z.Win.Birth.prTw :
    UpperTheory.V.Z.Win.Birth.PrTw := by
  rintro F Ω _ _ _ _ _ _ l _ ι r κ ⟨-, art, χ, a, ha, hχ, hL⟩ ⟨π, hr, hA, hP⟩
  refine ⟨π.twist χ, hr.twist (expo_intR hχ), sys_twist hA ha hL fun w B hB hu => hB.twist hu, fun v => ?_⟩
  rcases hP v with h | ⟨B, hB⟩
  · exact Or.inl (plainAtR_twist h χ)
  · by_cases hu : χ.UnrAt v
    · exact Or.inr ⟨_, hB.twist hu⟩
    · exact Or.inl (plainAtR_twist (plainAtR_of_hasSat (by norm_num) π v B hB) χ)
