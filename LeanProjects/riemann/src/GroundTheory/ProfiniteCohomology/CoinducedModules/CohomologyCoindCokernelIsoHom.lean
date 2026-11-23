import Mathlib
import GroundTheory.ProfiniteCohomology.CoinducedModules.Acyclic
import GroundTheory.ProfiniteCohomology.ContinuousCochains.LongExactSequence
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (A : Rep.{u} k G) [IsDiscreteRep A]

instance isDiscreteRep_coindShortComplex_X₁ : IsDiscreteRep (coindShortComplex A).X₁ :=
  (inferInstance : IsDiscreteRep A)

instance isDiscreteRep_coindShortComplex_X₂ : IsDiscreteRep (coindShortComplex A).X₂ :=
  (inferInstance : IsDiscreteRep (discreteCoind k G A))

instance isDiscreteRep_coindShortComplex_X₃ : IsDiscreteRep (coindShortComplex A).X₃ :=
  (inferInstance : IsDiscreteRep (coindCokernel A))

noncomputable def coindδ (n : ℕ) : cohomology (coindCokernel A) n ⟶ cohomology A (n + 1) :=
  δ (coindShortComplex_shortExact A) n (n + 1) rfl

instance epi_coindδ (n : ℕ) : Epi (coindδ A n) :=
  (cohomology_exact₁ (coindShortComplex_shortExact A) n (n + 1) rfl).epi_f
    ((isZero_cohomology_discreteCoind k G A n).eq_of_tgt _ _)

instance mono_coindδ_succ (n : ℕ) : Mono (coindδ A (n + 1)) :=
  (cohomology_exact₃ (coindShortComplex_shortExact A) (n + 1) (n + 2) rfl).mono_g
    ((isZero_cohomology_discreteCoind k G A n).eq_of_src _ _)

instance isIso_coindδ_succ (n : ℕ) : IsIso (coindδ A (n + 1)) :=
  isIso_of_mono_of_epi _

noncomputable def cohomologyCoindCokernelIso (n : ℕ) :
    cohomology (coindCokernel A) (n + 1) ≅ cohomology A (n + 2) :=
  asIso (coindδ A (n + 1))

@[simp]
theorem cohomologyCoindCokernelIso_hom (n : ℕ) :
    (cohomologyCoindCokernelIso A n).hom = coindδ A (n + 1) :=
  rfl

theorem coindδ_zero_exact :
    (ShortComplex.mk (cohomologyMap (coindCokernelπ A) 0) (coindδ A 0)
      (comp_δ (coindShortComplex_shortExact A) 0 1 rfl)).Exact :=
  cohomology_exact₃ (coindShortComplex_shortExact A) 0 1 rfl

noncomputable def cokernelCohomologyMapCoindCokernelπIso :
    cokernel (cohomologyMap (coindCokernelπ A) 0) ≅ cohomology A 1 :=
  IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _) (coindδ_zero_exact A).gIsCokernel

@[reassoc (attr := simp)]
theorem cokernel_π_cokernelCohomologyMapCoindCokernelπIso_hom :
    cokernel.π (cohomologyMap (coindCokernelπ A) 0) ≫
      (cokernelCohomologyMapCoindCokernelπIso A).hom = coindδ A 0 :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel _)
    (coindδ_zero_exact A).gIsCokernel WalkingParallelPair.one

end GroundTheory.ProfCoh
