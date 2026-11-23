import Mathlib
import GroundTheory.GlobalFields.TateThesis.HeckeTheoremConj

open NumberField InfinitePlace IsDedekindDomain MeasureTheory Complex
open scoped NumberField.AdeleRing

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

variable (K) in

theorem normOneClassMeasure_univ_ne_zero : normOneClassMeasure K Set.univ ≠ 0 := by
  rw [normOneClassMeasure_univ]
  exact (isFundamentalDomain_normOneFundamentalDomain K (normOneMeasure K)).measure_ne_zero
    (NeZero.ne _)

variable (K) in

theorem normOneClassMeasure_univ_toReal_ne_zero : (normOneClassMeasure K Set.univ).toReal ≠ 0 :=
  ENNReal.toReal_ne_zero.2 ⟨normOneClassMeasure_univ_ne_zero K, measure_ne_top _ _⟩

namespace HeckeCharacter

variable {χ : HeckeCharacter K} {τ : ℝ}
  (hτ : ∀ x : IdeleGroup K, (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I))
include hτ

theorem conductor_eq_top_of_forall : χ.conductor = ⊤ := by
  have h : ∀ v, IdeleGroup.conductorExponentAt (χ.toIdele.comp IdeleGroup.ofFinite) v = 0 := fun v ↦
    (IdeleGroup.conductorExponentAt_eq_zero_iff Circle.noSmallSubgroups _
      (χ.continuous_toIdele.comp IdeleGroup.continuous_ofFinite) v).2 fun x hx ↦ by
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply,
          ofFinite_finiteUnitsSingle]
        refine Circle.ext ?_
        rw [hτ, ideleModule_finiteEmbedding, norm_eq_one_of_mul_eq_one x.mul_inv
          ((Submonoid.mem_units_iff _ _).1 hx).1 ((Submonoid.mem_units_iff _ _).1 hx).2]
        simp
  rw [conductor, IdeleGroup.conductor]
  simp only [h, pow_zero]
  rw [finprod_one, Ideal.one_eq_top]

theorem infiniteParams_of_forall (w : InfinitePlace K) : χ.infiniteParams w = (0, τ) := by
  refine (χ.infiniteParams_unique w (p := (0, τ)) (fun _ ↦ ⟨le_rfl, by norm_num⟩) fun a ↦ ?_).symm
  dsimp only
  rw [infiniteComponent_apply, hτ, ideleModule_infiniteEmbedding, zpow_zero, one_mul]

theorem infiniteWeight_of_forall (w : InfinitePlace K) : χ.infiniteWeight w = 0 := by
  rw [infiniteWeight, infiniteParams_of_forall hτ]

theorem infiniteTau_of_forall (w : InfinitePlace K) : χ.infiniteTau w = τ := by
  rw [infiniteTau, infiniteParams_of_forall hτ]

theorem infiniteSchwartz_zero_of_forall : χ.infiniteSchwartz 0 = 1 := by
  rw [infiniteSchwartz_apply]
  simp [infinitePoly, infiniteWeight_of_forall hτ]

theorem finiteTestFun_zero_of_forall : χ.finiteTestFun 0 = 1 := by
  have hv : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ χ.conductor := fun v h ↦ by
    rw [conductor_eq_top_of_forall hτ, Ideal.dvd_iff_le, top_le_iff] at h
    exact v.isPrime.ne_top h
  unfold finiteTestFun
  exact (finprod_congr fun v ↦ χ.finiteTest_eq_one (hv v) (by
    rw [show (0 : FiniteAdeleRing (𝓞 K) K) v = 0 from rfl, map_zero]; exact zero_le)).trans finprod_one

theorem testFunction_zero_of_forall : χ.testFunction 0 = 1 := by
  show χ.infiniteSchwartz (homeomorphMixedSpace K 0) * χ.finiteTestFun 0 = 1
  rw [homeomorphMixedSpace_apply, map_zero, infiniteSchwartz_zero_of_forall hτ,
    finiteTestFun_zero_of_forall hτ, one_mul]

end HeckeCharacter

end

end GroundTheory.Global
