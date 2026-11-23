import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open Ad3 Ad3.R
open GroundTheory.Automorphic
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact finAt_mul infAt_mul finAt_one infAt_one)
open GroundTheory.Automorphic.GLnLocal (integralGL)

namespace GlobalTheory.CompanionTheory.RSCompact

abbrev KV (v : Pl) : Type := integralGL (Qv v) 2

instance compactSpace_KV (v : Pl) : CompactSpace (KV v) :=
  isCompact_iff_compactSpace.1 (GLnLocal.isCompact_integralGL (Qv v) 2)

instance compactSpace_KA : CompactSpace KA :=
  isCompact_iff_compactSpace.1 Reduction.isCompact_maxCompact

instance secondCountable_KV (v : Pl) : SecondCountableTopology (KV v) :=
  TopologicalSpace.Subtype.secondCountableTopology _

theorem continuous_finAt (v : Pl) : Continuous (finAt v : G2 → GL (Fin 2) (Qv v)) :=
  (RestrictedProduct.continuous_eval v).comp
    (continuous_snd.comp (AdelicGLn.restrictedProductEquiv ℚ 2).continuous)

def proj (S : Finset Pl) : KA →* ∀ v : S, KV v.1 where
  toFun κ v := ⟨finAt v.1 κ.1, κ.2.2 v.1⟩
  map_one' := by
    funext v
    exact Subtype.ext (finAt_one v.1)
  map_mul' a b := by
    funext v
    exact Subtype.ext (finAt_mul v.1 a.1 b.1)

theorem continuous_proj (S : Finset Pl) : Continuous (proj S) :=
  continuous_pi fun v =>
    Continuous.subtype_mk ((continuous_finAt v.1).comp continuous_subtype_val) _

theorem exists_lift (hL : ∀ (v : Pl) (x : GL (Fin 2) (Qv v)), ∃ h, IsLoc2 v x h)
    (y : ∀ v : Pl, GL (Fin 2) (Qv v)) (T : Finset Pl) :
    ∃ h : G2, (∀ v ∈ T, finAt v h = y v) ∧ (∀ v ∉ T, finAt v h = 1) ∧ ∀ w, infAt w h = 1 := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, by simp, fun v _ => finAt_one v, fun w => infAt_one w⟩
  | insert a T ha ih =>
    obtain ⟨h, h1, h2, h3⟩ := ih
    obtain ⟨l, l1, l2, l3⟩ := hL a (y a)
    refine ⟨h * l, ?_, ?_, ?_⟩
    · intro v hv
      rw [finAt_mul]
      rcases Finset.mem_insert.1 hv with rfl | hvT
      · rw [h2 _ ha, l1, one_mul]
      · rw [h1 v hvT, l2 v (by rintro rfl; exact ha hvT), mul_one]
    · intro v hv
      have hv' : v ≠ a ∧ v ∉ T := by simpa [Finset.mem_insert, not_or] using hv
      rw [finAt_mul, h2 v hv'.2, l2 v hv'.1, mul_one]
    · intro w
      rw [infAt_mul, h3, l3, mul_one]

theorem proj_surjective (hL : ∀ (v : Pl) (x : GL (Fin 2) (Qv v)), ∃ h, IsLoc2 v x h)
    (S : Finset Pl) : Function.Surjective (proj S) := by
  classical
  intro y
  obtain ⟨h, h1, h2, h3⟩ := exists_lift hL
    (fun v => if hv : v ∈ S then (y ⟨v, hv⟩).1 else 1) S
  have hK : h ∈ (maxCompact : Subgroup G2) := by
    refine ⟨fun w => ?_, fun v => ?_⟩
    · rw [h3]
      exact one_mem _
    · by_cases hv : v ∈ S
      · rw [h1 v hv, dif_pos hv]
        exact (y ⟨v, hv⟩).2
      · rw [h2 v hv]
        exact one_mem _
  refine ⟨⟨h, hK⟩, ?_⟩
  funext v
  refine Subtype.ext ?_
  change finAt v.1 h = (y v).1
  rw [h1 v.1 v.2, dif_pos v.2]

theorem integral_prod_finAt : Ad3.R.B0 → Ad3.R.E3 := by
  intro hB mK _ _ m hm S A hA
  have hL : ∀ (v : Pl) (x : GL (Fin 2) (Qv v)), ∃ h, IsLoc2 v x h :=
    fun v => (hB.1 v).2.2.2.2.2.1
  haveI : ∀ v : S, (m v.1).IsHaarMeasure := fun v => (hm v.1).1
  haveI : ∀ v : S, IsProbabilityMeasure (m v.1) := fun v => (hm v.1).2
  have hc := continuous_proj S
  haveI : (Measure.map (proj S) mK).IsHaarMeasure :=
    Measure.isHaarMeasure_map mK (proj S) hc (proj_surjective hL S) (by
      rw [Filter.cocompact_eq_bot]
      exact Filter.tendsto_bot)
  haveI : IsProbabilityMeasure (Measure.map (proj S) mK) :=
    Measure.isProbabilityMeasure_map hc.aemeasurable
  have hmap : Measure.map (proj S) mK = Measure.pi fun v : S => m v.1 :=
    Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _
  have hF : Continuous fun y : (∀ v : S, KV v.1) => ∏ v : S, A v (y v).1 :=
    continuous_finset_prod _ fun v _ =>
      (hA v).continuous.comp (continuous_subtype_val.comp (continuous_apply v))
  calc ∫ κ : KA, ∏ v : S, A v (finAt v.1 κ.1) ∂mK
      = ∫ y, ∏ v : S, A v (y v).1 ∂(Measure.map (proj S) mK) :=
        (integral_map hc.aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ y, ∏ v : S, A v (y v).1 ∂(Measure.pi fun v : S => m v.1) := by rw [hmap]
    _ = ∏ v : S, ∫ κ, A v κ.1 ∂m v.1 :=
        integral_fintype_prod_eq_prod (fun (v : S) (κ : KV v.1) => A v κ.1)

end GlobalTheory.CompanionTheory.RSCompact

end
