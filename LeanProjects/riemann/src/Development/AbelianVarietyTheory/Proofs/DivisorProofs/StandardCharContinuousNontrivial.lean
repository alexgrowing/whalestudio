import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzWeylFourier
import GroundTheory.GlobalFields.TateThesis.AdelicCharLocal

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.PsiLocal

variable {F : Type} [Field F] [NumberField F]

theorem exists_not_mem_localInvDifferent (v : Pl F) :
    ∃ x : Fv F v, x ∉ GroundTheory.Global.localInvDifferent v := by
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hy0' : algebraMap (𝓞 F) F y ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
  have ht0' : algebraMap (𝓞 F) F t ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
  refine ⟨((algebraMap (𝓞 F) F y * algebraMap (𝓞 F) F t)⁻¹ : F), fun h => ?_⟩
  have h1 := (GroundTheory.Global.coe_mem_localInvDifferent_iff v _).1 h y hy
  have e : (algebraMap (𝓞 F) F y * algebraMap (𝓞 F) F t)⁻¹ * algebraMap (𝓞 F) F y =
      (algebraMap (𝓞 F) F t)⁻¹ := by
    field_simp
  rw [e, map_inv₀] at h1
  have hlt : v.valuation F (algebraMap (𝓞 F) F t) < 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (v.intValuation_lt_one_iff_mem t).2 ht
  have hne : v.valuation F (algebraMap (𝓞 F) F t) ≠ 0 := by
    rwa [ne_eq, map_eq_zero]
  have := one_lt_inv_iff₀.2 ⟨zero_lt_iff.2 hne, hlt⟩
  exact absurd h1 (not_le.2 this)

theorem psi_loc_main : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ v : Pl F,
    Continuous (psiLoc ψ v) ∧ ∃ x : Fv F v, psiLoc ψ v x ≠ 1 := by
  intro F _ _ ψ hψ v
  have hval : ∀ x, psiLoc ψ v x = (GroundTheory.Global.localAdelicChar F v x : ℂ) := by
    intro x
    show ψ (GroundTheory.Global.finitePlaceIncl v x) = _
    exact GlobalTheory.AdelicSvN.Weyl.isStd_eq hψ _
  refine ⟨?_, ?_⟩
  · exact hψ.1.comp (continuous_const.prodMk (continuous_singleFin v))
  · by_contra hc
    push_neg at hc
    have h1 : ∀ x, GroundTheory.Global.localAdelicChar F v x = 1 := fun x => by
      have := hc x
      rw [hval] at this
      exact Circle.ext (by simpa using this)
    obtain ⟨x, hx⟩ := exists_not_mem_localInvDifferent v
    exact hx ((GroundTheory.Global.forall_localAdelicChar_mul_eq_one_iff v x).1 fun a _ => h1 _)

end GlobalTheory.PsiLocal
