import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitarisableOfCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainMulRight
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.UnitaryPointsRankZeroSubsingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BridgeSIsBridge
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThetaCplV
open Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ThetaCplV.UnitaryTrick

theorem exists_isURep_of_core {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] {V : Type} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ K V)
    (hρ : ∀ (φ : V →ₗ[ℂ] ℂ) (v : V), Continuous fun k => φ (ρ k v))
    (c : InnerProductSpace.Core ℂ V) (hc : ∀ k u v, c.inner (ρ k u) (ρ k v) = c.inner u v) :
    ∃ (d : ℕ) (τ : K → (EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)))
      (e : V ≃ₗ[ℂ] EuclideanSpace ℂ (Fin d)), GlobalTheory.Dec.IsURep τ ∧ ∀ k v, e (ρ k v) = τ k (e v) := by
  letI cd : InnerProductSpace.Core ℂ V := c
  letI : NormedAddCommGroup V := @InnerProductSpace.Core.toNormedAddCommGroup ℂ V _ _ _ cd
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore cd.toCore
  let b := stdOrthonormalBasis ℂ V
  let e : V ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) := b.repr.toLinearEquiv
  let τ : K → (EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) →L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V))) :=
    fun g => LinearMap.toContinuousLinearMap (e.toLinearMap ∘ₗ ρ g ∘ₗ e.symm.toLinearMap)
  have hτ : ∀ g x, τ g x = e (ρ g (e.symm x)) := fun _ _ => rfl
  have hn : ∀ g (y : V), ‖ρ g y‖ = ‖y‖ := by
    intro g y
    have h1 : inner ℂ (ρ g y) (ρ g y) = inner ℂ y y := hc g y y
    rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, h1]
  refine ⟨_, τ, e, ⟨?_, fun a c => ?_, fun g x => ?_, fun x => ?_⟩, fun g v => ?_⟩
  · ext1 x; simp [hτ]
  · ext1 x; simp [hτ, map_mul]
  · rw [hτ]
    change ‖b.repr (ρ g (b.repr.symm x))‖ = ‖x‖
    rw [LinearIsometryEquiv.norm_map, hn, ← LinearIsometryEquiv.norm_map b.repr,
      LinearIsometryEquiv.apply_symm_apply]
  · simp only [hτ]
    exact GlobalTheory.UniTrick.continuous_lin ρ hρ e.toLinearMap _
  · rw [hτ, LinearEquiv.symm_apply_apply]

end GlobalTheory.ThetaCplV.UnitaryTrick

namespace GlobalTheory.ThetaCplV

open UnitaryTrick in

theorem exists_isURep_of_stable : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] (j : K →* G), Continuous j → ∀ H : Subgroup G, (∀ k, j k ∈ H) → ∀ T : Submodule ℂ (G → ℂ), FiniteDimensional ℂ T → (∀ t ∈ T, Continuous t) → (∀ h, ∀ t ∈ T, GlobalTheory.ThetaCplV.rt H h t ∈ T) → ∃ (m : ℕ) (τ : K → (EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m))), GlobalTheory.Dec.IsURep τ ∧ ∀ f ∈ GlobalTheory.ThetaCplV.typeSet (GlobalTheory.ThetaCplV.rt H) ⊤ T, ∃ L : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] (G → ℂ), (∀ k w x, L (τ k w) x = L w (x * j k)) ∧ f ∈ LinearMap.range L := by
  intro G _ _ _ K _ _ _ _ j hj H hjH T hT hcont hst
  let ρ : Representation ℂ K T :=
    { toFun := fun k => (rt H ⟨j k, hjH k⟩).restrict (fun t ht => hst _ t ht)
      map_one' := by ext t x; simp
      map_mul' := fun a b => by ext t x; simp [mul_assoc] }
  have hρv : ∀ k (v : T), ((ρ k v : T) : G → ℂ) = fun x => (v : G → ℂ) (x * j k) := fun _ _ => rfl
  have hρc : ∀ v : T, Continuous fun k => ρ k v := by
    intro v
    refine Continuous.subtype_mk ?_ _
    change Continuous fun k => fun x => (v : G → ℂ) (x * j k)
    exact continuous_pi fun x => (hcont v v.2).comp (continuous_const.mul hj)
  have hρφ : ∀ (φ : T →ₗ[ℂ] ℂ) (v : T), Continuous fun k => φ (ρ k v) := fun φ v =>
    (LinearMap.continuous_of_finiteDimensional φ).comp (hρc v)
  obtain ⟨c, hc⟩ := GlobalTheory.exists_invariant_core ρ hρc
  obtain ⟨d, τ, e, hτ, he⟩ := exists_isURep_of_core ρ hρφ c hc
  refine ⟨d, τ, hτ, fun f hf => ?_⟩
  obtain ⟨L₀, -, heq, t, rfl⟩ := hf
  refine ⟨L₀ ∘ₗ e.symm.toLinearMap, fun k w x => ?_, ⟨e t, by simp⟩⟩
  have h1 : e.symm (τ k w) = ρ k (e.symm w) := by
    rw [LinearEquiv.symm_apply_eq, he, LinearEquiv.apply_symm_apply]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h1]
  rw [heq ⟨j k, hjH k⟩ (e.symm w) (ρ k (e.symm w)) rfl, rt_apply]

end GlobalTheory.ThetaCplV
