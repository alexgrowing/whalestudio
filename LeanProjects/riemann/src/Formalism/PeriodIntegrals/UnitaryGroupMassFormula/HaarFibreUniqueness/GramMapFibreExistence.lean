import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.FibExGram
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.FibTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.FreeOpen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVTop

noncomputable section

namespace PI.OmFibreUniq.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology
open PI.OmFibreUniq PI.VolStabSW PI.VolStabSW.TensAllW PI.VolStabSW.OmFibG
open scoped TensorProduct

theorem densAll_gen {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (hdet : J.det ≠ 0) (v : HeightOneSpectrum (𝓞 F)) (a : ℕ)
    (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a))
    (hμ : μ.IsAddHaarMeasure) (hν : ν.IsAddHaarMeasure) :
    DensAll μ (gramR (Fv F v) σ J) Subtype.val ν
      {X : Fin a → Fin n → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} := by
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have := secondCountable_Fv F v
  have := locallyCompact_Fv F v
  have hfree := isOpen_linIndep (Module.finBasis F E) (Fv F v) (isOpen_units_Fv F v) (lip_field _)
    (a := a) (M := n)
  obtain ⟨t1, t2, t3, t4, t5, _t6, t7⟩ := tensFacts_of_fib σ n J a (Fv F v) hσ hJ hfree
  have := hμ
  have := hν
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Fv F v) σ a) := ⟨rfl⟩
  have : LocallyCompactSpace (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin a → Fv F v ⊗[F] E))
  have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  have : LocallyCompactSpace (HermR (Fv F v) σ a) :=
    t4.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  have hNA : HasCOSub (Fin a → Fin n → Fv F v ⊗[F] E) := by
    obtain ⟨π, h0, hπ⟩ := exists_pow_tendsto_zero_Fv v
    exact hasCOSub_of_lat (latSub (Module.finBasis F E) v a n)
      (PositiveNearLattice.isClopen_latV (Module.finBasis F E) v a n).isOpen
      (PositiveNearLattice.isCompact_latV (Module.finBasis F E) v a n) π h0 hπ
  have hC : DensCosB (scaledB (Fv F v) (latSub (Module.finBasis F E) v a n)) μ
      (gramR (Fv F v) σ J) Subtype.val ν
      {X : Fin a → Fin n → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} := by
    intro x hx
    obtain ⟨N, hN, hd⟩ := gramFilt_all σ hσ n J hJ hdet a v _ (Module.finBasis F E) x hx
    refine ⟨N, hN, fun y hy Λ0 hB _ _ hsub => ?_⟩
    obtain ⟨Λ, H, D, h0, hΛo, hΛc, hΛa, hHo, hHc, hHb, hD, hyp⟩ := hd y hy Λ0 hB hsub
    subst h0
    exact densCos_of_filt henselCount_holds cosDens_holds μ ν (gramR (Fv F v) σ J) Subtype.val
      Subtype.val_injective (gramH (Fv F v) σ hσ J hJ) (Continuous.subtype_mk t5 _)
      (fun _ => rfl) y Λ H hΛo hΛc hΛa hHo hHc hHb D hD hyp
  have hLC := densLC_of_cosB _ _ (isCOBasis_latSub (Module.finBasis F E) v a n) hC
  exact (densAll_iff _ _ _ _ _).2 (densApprox_lc μ _ _ ν _ t7 hNA hLC)

theorem gram_map_fibre_existence : FibEx := by
  intro F E _ _ _ _ _ σ n J v a hCM hJ μ ν hμ hν
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  have := secondCountable_Fv F v
  have := locallyCompact_Fv F v
  have hfree := isOpen_linIndep (Module.finBasis F E) (Fv F v) (isOpen_units_Fv F v) (lip_field _)
    (a := a) (M := n)
  exact fib_of_tens DiscreteGroups.fibOfDens_holds (tensFacts_of_fib σ n J a (Fv F v) hσ hJ.1 hfree) μ ν
    hμ hν (densAll_gen σ hσ J hJ.1 hJ.2 v a μ ν hμ hν)

end PI.OmFibreUniq.W
