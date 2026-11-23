import Mathlib
import GroundTheory.GlobalFields.TateThesis.GlobalZeta
import GroundTheory.GlobalFields.TateThesis.IdeleMeasureQuotient

open NumberField IsDedekindDomain Topology Filter MeasureTheory
open scoped NumberField.AdeleRing ENNReal NNReal

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

def partialZetaSum (w : InfinitePlace K) (f : 𝔸[K] → ℂ) (χ : HeckeCharacter K)
    (t : {r : ℝ // 0 < r}) (u : normOneSubgroup K) : ℂ :=
  ∑' ξ : Kˣ, f ((diagonal K ξ * moduleSection w t * (u : IdeleGroup K) : IdeleGroup K) : 𝔸[K]) *
    (χ.toIdele (moduleSection w t * (u : IdeleGroup K)) : ℂ)

theorem partialZetaSum_mul (w : InfinitePlace K) (f : 𝔸[K] → ℂ) (χ : HeckeCharacter K)
    (t : {r : ℝ // 0 < r}) (u : normOneSubgroup K) {δ : normOneSubgroup K}
    (hδ : δ ∈ diagonalNormOne K) : partialZetaSum w f χ t (u * δ) = partialZetaSum w f χ t u := by
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range] at hδ
  obtain ⟨ξ₀, hξ₀⟩ := hδ
  unfold partialZetaSum
  conv_rhs => rw [← (Equiv.mulRight ξ₀).tsum_eq]
  refine tsum_congr fun ξ ↦ ?_
  have hχ : χ.toIdele (moduleSection w t * ((u * δ : normOneSubgroup K) : IdeleGroup K)) =
      χ.toIdele (moduleSection w t * (u : IdeleGroup K)) := by
    rw [Subgroup.coe_mul, ← hξ₀, ← mul_assoc, map_mul, HeckeCharacter.toIdele_diagonal, mul_one]
  have hf : diagonal K ξ * moduleSection w t * ((u * δ : normOneSubgroup K) : IdeleGroup K) =
      diagonal K ((Equiv.mulRight ξ₀) ξ) * moduleSection w t * (u : IdeleGroup K) := by
    rw [Subgroup.coe_mul, ← hξ₀, Equiv.coe_mulRight, map_mul]
    simp only [mul_comm, mul_left_comm, mul_assoc]
  rw [hχ, hf]

def partialZetaClass (w : InfinitePlace K) (f : 𝔸[K] → ℂ) (χ : HeckeCharacter K)
    (t : {r : ℝ // 0 < r}) : normOneSubgroup K ⧸ diagonalNormOne K → ℂ :=
  Quotient.lift (s := QuotientGroup.leftRel (diagonalNormOne K)) (partialZetaSum w f χ t)
    fun u v h ↦ by
      have h' : u⁻¹ * v ∈ diagonalNormOne K := QuotientGroup.leftRel_apply.1 h
      conv_rhs => rw [← mul_inv_cancel_left u v]
      rw [partialZetaSum_mul w f χ t u h']

def partialZeta (w : InfinitePlace K) (f : 𝔸[K] → ℂ) (χ : HeckeCharacter K)
    (t : {r : ℝ // 0 < r}) : ℂ :=
  ∫ c, partialZetaClass w f χ t c ∂normOneClassMeasure K

theorem measurable_partialZetaSum (w : InfinitePlace K) {f : 𝔸[K] → ℂ} (hf : Continuous f)
    (χ : HeckeCharacter K) (t : {r : ℝ // 0 < r}) : Measurable (partialZetaSum w f χ t) := by
  refine Measurable.tsum fun ξ ↦ Continuous.measurable ?_
  have hu : Continuous fun u : normOneSubgroup K ↦ moduleSection w t * (u : IdeleGroup K) :=
    continuous_const.mul continuous_subtype_val
  have hu' : Continuous fun u : normOneSubgroup K ↦
      diagonal K ξ * moduleSection w t * (u : IdeleGroup K) :=
    continuous_const.mul continuous_subtype_val
  exact (hf.comp (Units.continuous_val.comp hu')).mul
    (continuous_subtype_val.comp (χ.continuous_toIdele.comp hu))

theorem partialZeta_eq_setIntegral (w : InfinitePlace K) {f : 𝔸[K] → ℂ} (hf : Continuous f)
    (χ : HeckeCharacter K) (t : {r : ℝ // 0 < r}) :
    partialZeta w f χ t =
      ∫ u in normOneFundamentalDomain K, partialZetaSum w f χ t u ∂normOneMeasure K := by
  have hm : Measurable (partialZetaClass w f χ t) :=
    QuotientGroup.measurable_from_quotient.2 (measurable_partialZetaSum w hf χ t)
  rw [partialZeta, normOneClassMeasure,
    integral_map QuotientGroup.measurable_coe.aemeasurable hm.aestronglyMeasurable]
  rfl

theorem zetaIntegrand_diagonal_mul (w : InfinitePlace K) (f : 𝔸[K] → ℂ) (χ : HeckeCharacter K)
    (s : ℂ) (ξ : Kˣ) (t : {r : ℝ // 0 < r}) (u : normOneSubgroup K) :
    f ((diagonal K ξ * moduleSection w t * (u : IdeleGroup K) : IdeleGroup K) : 𝔸[K]) *
        (χ.toIdele (diagonal K ξ * moduleSection w t * (u : IdeleGroup K)) : ℂ) *
        ((ideleModule K (diagonal K ξ * moduleSection w t * (u : IdeleGroup K)) : ℝ) : ℂ) ^ s =
      f ((diagonal K ξ * moduleSection w t * (u : IdeleGroup K) : IdeleGroup K) : 𝔸[K]) *
        (χ.toIdele (moduleSection w t * (u : IdeleGroup K)) : ℂ) * ((t : ℝ) : ℂ) ^ s := by
  have hu : ideleModule K (u : IdeleGroup K) = 1 := u.2
  have hmod : ideleModule K (diagonal K ξ * moduleSection w t * (u : IdeleGroup K)) = t := by
    rw [map_mul, map_mul, ideleModule_diagonal, one_mul, ideleModule_moduleSection, hu, mul_one]
  have hχ : χ.toIdele (diagonal K ξ * moduleSection w t * (u : IdeleGroup K)) =
      χ.toIdele (moduleSection w t * (u : IdeleGroup K)) := by
    rw [mul_assoc, map_mul, HeckeCharacter.toIdele_diagonal, one_mul]
  simp only [hmod, hχ]

theorem globalZeta_eq_integral_partialZeta (w : InfinitePlace K) {f : 𝔸[K] → ℂ}
    (hf : f ∈ schwartzBruhat K) (χ : HeckeCharacter K) {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun t ↦ partialZeta w f χ t * ((t : ℝ) : ℂ) ^ s) posRealMeasure ∧
      globalZeta f χ s = ∫ t, partialZeta w f χ t * ((t : ℝ) : ℂ) ^ s ∂posRealMeasure := by
  have hfc := continuous_of_mem_schwartzBruhat hf
  set G : IdeleGroup K → ℂ := fun x ↦ f x * (χ.toIdele x : ℂ) * ((ideleModule K x : ℝ) : ℂ) ^ s
    with hGdef
  have hG : Integrable G (ideleMeasure K) := integrable_globalZetaIntegrand hf χ hs
  have hg : Integrable (fun p : normOneSubgroup K × {r : ℝ // 0 < r} ↦
      G ((p.1 : IdeleGroup K) * moduleSection w p.2))
      ((normOneMeasure K).prod posRealMeasure) := by
    rw [← map_normOneSplitting_eq_prod w]
    refine (integrable_map_equiv (normOneSplitting w).toHomeomorph.toMeasurableEquiv _).2 ?_
    convert hG using 1
    funext x
    exact congrArg G ((normOneSplitting w).symm_apply_apply x)
  have hae : (fun t ↦ ∫ u, G ((u : IdeleGroup K) * moduleSection w t) ∂normOneMeasure K)
      =ᵐ[posRealMeasure] fun t ↦ partialZeta w f χ t * ((t : ℝ) : ℂ) ^ s := by
    filter_upwards [hg.prod_left_ae] with t ht
    rw [integral_normOneMeasure_eq_setIntegral_tsum ht, partialZeta_eq_setIntegral w hfc,
      ← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun u ↦ ?_)
    simp only [partialZetaSum]
    rw [← tsum_mul_right]
    refine tsum_congr fun ξ ↦ ?_
    have hx : ((diagonalToNormOne K ξ * u : normOneSubgroup K) : IdeleGroup K) *
        moduleSection w t = diagonal K ξ * moduleSection w t * (u : IdeleGroup K) := by
      rw [Subgroup.coe_mul, coe_diagonalToNormOne, mul_right_comm]
    rw [hx]
    exact zetaIntegrand_diagonal_mul w f χ s ξ t u
  refine ⟨hg.integral_prod_right.congr hae, ?_⟩
  rw [globalZeta, integral_ideleMeasure_eq_integral_normOne w hG]
  exact integral_congr_ae hae

end

end GroundTheory.Global
