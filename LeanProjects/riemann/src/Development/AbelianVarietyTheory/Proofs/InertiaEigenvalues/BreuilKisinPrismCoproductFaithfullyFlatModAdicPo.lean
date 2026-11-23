import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismHomMapIdealEqStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicTopologicalBasisBasisModPowStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.EnvFF

theorem adI_map {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] {B B' : Obj l R} (f : Hom B B') (m : ℕ) :
    (adI B ^ m).map f.f = adI B' ^ m := by
  rw [Ideal.map_pow, adI, adI, Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast,
    GlobalTheory.T.prism_hom_map_ideal_eq l R B B' f]

theorem ff_of_basis {R S : Type} [CommRing R] [CommRing S] (g : R →+* S) (ι : Type) [Nonempty ι]
    (h : letI := g.toAlgebra; Nonempty (Module.Basis ι R S)) : g.FaithfullyFlat := by
  letI := g.toAlgebra
  obtain ⟨b⟩ := h
  exact Module.FaithfullyFlat.of_linearEquiv _ _ b.repr

end GlobalTheory.BSP.EnvFF

open GlobalTheory.BSP.EnvFF

theorem GlobalTheory.BSP.envFF : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (t p : B.A)
    (En : Env bk B t p) (m : ℕ), (qmap En.inl m).FaithfullyFlat := by
  intro l _ K bk B t p En m
  have hJ : (adI B ^ m).map En.inl.f = adI En.Q ^ m := adI_map En.inl m
  have e : qmap En.inl m = (Ideal.quotEquivOfEq hJ).toRingHom.comp
      (Ideal.quotientMap ((adI B ^ m).map En.inl.f) En.inl.f Ideal.le_comap_map) := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
    rfl
  have h2 : (Ideal.quotEquivOfEq hJ).toRingHom.FaithfullyFlat :=
    RingHom.FaithfullyFlat.of_bijective (Ideal.quotEquivOfEq hJ).bijective
  have h1 : (Ideal.quotientMap ((adI B ^ m).map En.inl.f) En.inl.f Ideal.le_comap_map).FaithfullyFlat := by
    haveI : Nonempty (Digits l) := ⟨⟨0, fun _ => (Fact.out : l.Prime).pos⟩⟩
    obtain ⟨b, -⟩ := GlobalTheory.T.adicTopologicalBasis_basis_mod_pow B.A En.Q.A En.inl.f (adI B) (Digits l) En.tb m
    exact ff_of_basis _ (Digits l) ⟨b⟩
  rw [e]
  exact RingHom.FaithfullyFlat.stableUnderComposition _ _ h1 h2
