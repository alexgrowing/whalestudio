import Mathlib
import ReciprocityTheory.Hypotheses.GalCoh
import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import GroundTheory.ProfiniteCohomology.ContinuousCochains
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsDiscreteRepResMuROrep
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.SubsingletonCohomologyOfPrimaryOfFinite
import GroundTheory.ProfiniteCohomology.ClassFormations.IsIsoCohomologyMapAlongResSubgroupOfHom

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global FiniteSubfield ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.CompanionTheory.GSCd GroundTheory.Global.IdeleGroup GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open scoped DirectSum

namespace GlobalTheory.CompanionTheory.GSCd

theorem cdp_le_of_continuousMulEquiv {G H : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (p : ℕ)
    (e : G ≃ₜ* H) : cdp p G ≤ cdp p H := by
  refine cdp_le_iff.2 fun A _ hA q hq => ?_
  let φ : H ≃* G := e.toMulEquiv.symm
  have he : Continuous φ.toMonoidHom := e.continuous_invFun
  have he' : Continuous φ.symm.toMonoidHom := e.continuous_toFun
  let B : Rep.{0} (ULift.{0} ℤ) H := Rep.res φ.toMonoidHom A
  haveI : IsDiscreteRep B := IsDiscreteRep.res he A
  have hB : IsAddTorsion B := hA
  have hH := primaryComponent_cohomology_eq_bot_of_cdp_lt B hB hq
  haveI := isIso_cohomologyMapAlong_of_mulEquiv φ he he' (𝟙 B) Function.bijective_id q
  let F := asIso (cohomologyMapAlong φ.toMonoidHom he (𝟙 B) q)
  rw [primaryComponent_eq_bot_iff] at hH ⊢
  rintro x ⟨k, hk⟩
  have h0 : F.toLinearEquiv x = 0 :=
    hH _ ⟨k, by rw [← map_nsmul, hk, map_zero]⟩
  exact F.toLinearEquiv.injective (h0.trans (map_zero _).symm)

theorem cdp_eq_of_continuousMulEquiv : ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (p : ℕ), (G ≃ₜ* H) → cdp p G = cdp p H := by
  intro G H _ _ _ _ _ _ p e
  exact le_antisymm (cdp_le_of_continuousMulEquiv p e) (cdp_le_of_continuousMulEquiv p e.symm)

end GlobalTheory.CompanionTheory.GSCd
