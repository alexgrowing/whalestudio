import Mathlib
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaDistributionHeisenbergInvariant

open NumberField

namespace GlobalTheory.CompanionTheory.AdeleDual

open GroundTheory.Global

variable {F : Type} [Field F] [NumberField F]

theorem exists_eq_adelicChar_mul (χ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hc : Continuous χ)
    (hF : ∀ a : F, χ (algebraMap F (AdeleRing (𝓞 F) F) a) = 1) :
    ∃ ξ : F, ∀ x, χ x = (adelicChar F (algebraMap F (AdeleRing (𝓞 F) F) ξ * x) : ℂ) := by
  have hn := GlobalTheory.CompanionTheory.AdeleAnn.norm_eq_one χ hc hF
  let χ' : AddChar (AdeleRing (𝓞 F) F) Circle :=
    { toFun := fun y => ⟨χ y, mem_sphere_zero_iff_norm.2 (hn y)⟩
      map_zero_eq_one' := Circle.ext (by simp)
      map_add_eq_mul' := fun a b => Circle.ext (χ.map_add_eq_mul a b) }
  have hχ' : Continuous χ' := hc.subtype_mk _
  obtain ⟨ξ, hξ, -⟩ := GroundTheory.Global.existsUnique_eq_adelicChar_mul χ' hχ' fun k => Circle.ext (hF k)
  exact ⟨ξ, fun x => congrArg (fun c : Circle => (c : ℂ)) (hξ x)⟩

end GlobalTheory.CompanionTheory.AdeleDual
