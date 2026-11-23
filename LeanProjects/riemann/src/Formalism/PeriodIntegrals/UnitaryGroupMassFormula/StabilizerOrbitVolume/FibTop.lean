import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.FibDis
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.ExOmTOfSteps
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensFibV

noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Topology
open scoped TensorProduct

def FreeOpen : Prop := InCtx fun F E _ _ _ _ _ _σ M _J a _X0 _hT =>
  IsOpen {X : Fin a → Fin M → Ainf F ⊗[F] E | LinearIndependent (Ainf F ⊗[F] E) X} ∧
  ∀ v : HeightOneSpectrum (𝓞 F),
    IsOpen {X : Fin a → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X}

theorem tensFacts_of_fib {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (a : ℕ) (R : Type) [CommRing R]
    [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R]
    [SecondCountableTopology R] (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j)
    (hfree : IsOpen {X : Fin a → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X}) :
    TensFacts F E σ M J a R := ⟨inferInstance, inferInstance, inferInstance, isClosed_HermR (R := R) σ a,
  continuous_gramR (R := R) σ J, fun X => gramR_mem (R := R) σ hσ J hJ X, hfree⟩

theorem tensAll_of (h : FreeOpen) : TensAll := by
  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a ha haM X0 hT hdet
  have hF := h F E σ hCM M J hJ h1 h2 a ha haM X0 hT hdet
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
    apply τ.injective
    rw [hCM.2.2.2, hCM.2.2.2, star_star]
  exact ⟨tensFacts_of_fib σ M J a (Ainf F) hσ hJ.1 hF.1,
    fun v => by
      haveI : LocallyCompactSpace (Fv F v) := locallyCompact_Fv (F := F) (v := v)
      haveI : SecondCountableTopology (Fv F v) := secondCountable_Fv (F := F) (v := v)
      exact tensFacts_of_fib σ M J a (Fv F v) hσ hJ.1 (hF.2 v)⟩

theorem fibInfEx_of_core (h1 : FreeOpen) (h2 : DensInf) : FibInfEx := fibInfEx_of DiscreteGroups.fibOfDens_holds (tensAll_of h1) h2

theorem fibVEx_of_core (h1 : FreeOpen) (h2 : DensV) : FibVEx := fibVEx_of DiscreteGroups.fibOfDens_holds (tensAll_of h1) h2

theorem exOmT_of_core (h1 : FreeOpen) (h2 : DensInf) (h3 : DensV) (h4 : SdUniq) (h5 : RestrProd) :
    ExOmT := exOmT_of_open (fibInfEx_of_core h1 h2) (fibVEx_of_core h1 h3) h4 h5

end PI.VolStabSW
