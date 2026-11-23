import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeDefs
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeModules
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangePlaces
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeMackey
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField GroundTheory.Global GroundTheory.Global.SemiLocal

universe u

variable {F L Ω : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω]
  [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] [IsGalois F Ω] [IsGalois L Ω]
  {S : Set (HeightOneSpectrum (𝓞 F))}
  (hL : ∀ x : L, algebraMap L Ω x ∈ maxUnramifiedOutside F Ω S)
  (ιs : ∀ v : S, Ω →ₐ[F] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F))

theorem exists_gsBaseChange_mackeyFamily_eq (p : MackeyIndex (gsOpenSubgroup S hL) (gsFinFamily S ιs))
    (ι' : Ω →ₐ[L] AlgebraicClosure ((gsLocalPlace hL ιs p.1 p.2.out).1.adicCompletion L)) :
    ∃ g : galUnramifiedOutside L Ω (placesOver S),
      ∀ σ : mackeyGroup (gsOpenSubgroup S hL) (gsFinFamily S ιs) p,
        gsBaseChange S hL (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs) p σ) =
          g⁻¹ * decompHomS ((gsLocalPlace hL ιs p.1 p.2.out).1.adicCompletion L) (placesOver S) ι'
            (gsMackeyLocalEquiv hL ιs p.1 p.2.out σ) * g := by
  have h3 : ∃ f : Ω →ₐ[L] AlgebraicClosure ((gsLocalPlace hL ιs p.1 p.2.out).1.adicCompletion L),
      f = gsLocalEmbeddingOver hL ιs p.1 p.2.out := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ := h3
  have h2 := exists_eq_comp_of_normal
    (ι'.comp (maxUnramifiedOutside L Ω (placesOver S)).val)
    (f.comp (maxUnramifiedOutside L Ω (placesOver S)).val)
  obtain ⟨g, hg⟩ := h2
  refine ⟨g, fun σ => ?_⟩
  refine (gsBaseChange_mackeyFamily hL ιs p σ).trans ?_
  subst hf
  exact (congrArg (fun ψ => decompHom ((gsLocalPlace hL ιs p.1 p.2.out).1.adicCompletion L) ψ
    (gsMackeyLocalEquiv hL ιs p.1 p.2.out σ)) hg).trans (decompHom_comp _ g _)

omit [IsGalois L Ω] in

theorem coe_mackeyPlaceEquiv_eq (p : MackeyIndex (gsOpenSubgroup S hL) (gsFinFamily S ιs)) :
    (mackeyPlaceEquiv S hL ιs p : HeightOneSpectrum (𝓞 L)) = (gsLocalPlace hL ιs p.1 p.2.out).1 :=
  rfl

end GroundTheory.ProfCoh
