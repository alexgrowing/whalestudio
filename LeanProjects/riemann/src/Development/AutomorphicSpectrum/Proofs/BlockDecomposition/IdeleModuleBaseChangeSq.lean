import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE

set_option maxSynthPendingDepth 1
set_option synthInstance.maxSize 1000

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.MdBase

section

open NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global
  GroundTheory.Global.AdeleBaseChange MeasureTheory.Measure
open scoped ENNReal NNReal NumberField.AdeleRing

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem map_smul_pi (n : ℕ) (a : IdeleGroup K) :
    (Measure.pi fun _ : Fin n ↦ adeleMeasure K).map (fun x i ↦ a • x i) =
      (Real.toNNReal ((IdeleGroup.ideleModule K a : ℝ))⁻¹) ^ n •
        Measure.pi fun _ : Fin n ↦ adeleMeasure K := by
  have hsm : Measurable fun y : 𝔸[K] ↦ a • y := (Homeomorph.smul a).continuous.measurable
  have hmeas : Measurable fun x : Fin n → 𝔸[K] ↦ fun i ↦ a • x i :=
    measurable_pi_lambda _ fun i ↦ hsm.comp (measurable_pi_apply i)
  set c : ℝ≥0 := Real.toNNReal ((IdeleGroup.ideleModule K a : ℝ))⁻¹ with hcdef
  have hmap : (adeleMeasure K).map (fun y ↦ a • y) = c • adeleMeasure K := by
    rw [map_smul_adeleMeasure]
    rfl
  have h1 : (Measure.pi fun _ : Fin n ↦ adeleMeasure K).map (fun x i ↦ a • x i) =
      Measure.pi fun _ : Fin n ↦ c • adeleMeasure K := by
    refine (pi_eq fun s hs ↦ ?_).symm
    rw [map_apply hmeas (MeasurableSet.univ_pi hs)]
    have hpre : (fun x : Fin n → 𝔸[K] ↦ fun i ↦ a • x i) ⁻¹' Set.univ.pi s =
        Set.univ.pi fun i ↦ (fun y ↦ a • y) ⁻¹' s i := by
      ext x
      simp
    rw [hpre, pi_pi]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [← hmap, map_apply hsm (hs i)]
  have h2 : (Measure.pi fun _ : Fin n ↦ c • adeleMeasure K) =
      c ^ n • Measure.pi fun _ : Fin n ↦ adeleMeasure K := by
    refine pi_eq fun s hs ↦ ?_
    rw [Measure.smul_apply, pi_pi, ENNReal.smul_def, smul_eq_mul]
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ENNReal.coe_pow]
  rw [h1, h2]

theorem ideleModule_ideleEmbedding (x : IdeleGroup K) :
    (IdeleGroup.ideleModule L (ideleEmbedding K L x) : ℝ) =
      (IdeleGroup.ideleModule K x : ℝ) ^ Module.finrank K L := by
  have := isModuleTopology_adeleRing (K := K) (L := L)
  set n := Module.finrank K L with hn
  let e : 𝔸[L] ≃ₗ[𝔸[K]] (Fin n → 𝔸[K]) := (adeleBasis (Module.finBasis K L)).equivFun
  have hce : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hcs : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : 𝔸[L] ≃ₜ (Fin n → 𝔸[K]) :=
    { toEquiv := e.toEquiv, continuous_toFun := hce, continuous_invFun := hcs }
  set μ : Measure (Fin n → 𝔸[K]) := Measure.pi fun _ ↦ adeleMeasure K with hμ
  set ν : Measure 𝔸[L] := μ.map e.symm with hν
  have hms : Measurable e.symm := hcs.measurable
  haveI : ν.IsAddHaarMeasure :=
    isAddHaarMeasure_map _ e.symm.toLinearMap.toAddMonoidHom hcs e.symm.surjective
      h.symm.isClosedEmbedding.tendsto_cocompact
  set X := ideleEmbedding K L x with hX
  have hcomp : (fun y : 𝔸[L] ↦ X • y) ∘ e.symm = e.symm ∘ (fun v i ↦ x • v i) := by
    funext v
    have hv : (fun i ↦ x • v i) = (x : 𝔸[K]) • v := by
      funext i
      simp [Units.smul_def]
    simp only [Function.comp_apply]
    rw [hv, map_smul, Units.smul_def]
    change (X : 𝔸[L]) * e.symm v = (x : 𝔸[K]) • e.symm v
    rw [Algebra.smul_def (x : 𝔸[K]), algebraMap_adeleRing]
    rfl
  have hsmL : Measurable fun y : 𝔸[L] ↦ X • y := (Homeomorph.smul X).continuous.measurable
  have hsmK : Measurable fun v : Fin n → 𝔸[K] ↦ fun i ↦ x • v i :=
    measurable_pi_lambda _ fun i ↦
      (Homeomorph.smul x).continuous.measurable.comp (measurable_pi_apply i)
  set c : ℝ≥0 := Real.toNNReal ((IdeleGroup.ideleModule K x : ℝ))⁻¹ with hcdef
  have h1 : ν.map (fun y ↦ X • y) = c ^ n • ν := by
    rw [hν, Measure.map_map hsmL hms, hcomp, ← Measure.map_map hms hsmK, hμ, map_smul_pi,
      Measure.map_smul]
  have hc := isAddLeftInvariant_eq_smul ν (adeleMeasure L)
  set C := ν.addHaarScalarFactor (adeleMeasure L)
  have hC0 : (C : ℝ≥0∞) ≠ 0 := by
    intro h0
    have : ν = 0 := by rw [hc, ENNReal.coe_eq_zero.1 h0, zero_smul]
    exact (NeZero.ne ν) this
  obtain ⟨S, hS, hS0⟩ := exists_compact_mem_nhds (0 : 𝔸[L])
  have hpos : adeleMeasure L S ≠ 0 := (measure_pos_of_mem_nhds _ hS0).ne'
  have htop : adeleMeasure L S ≠ ⊤ := hS.measure_lt_top.ne
  rw [hc, Measure.map_smul, map_smul_adeleMeasure] at h1
  have h2 := congrArg (fun m : Measure 𝔸[L] ↦ m S) h1
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
  rw [mul_left_comm] at h2
  have hne : (C : ℝ≥0∞) * adeleMeasure L S ≠ 0 := mul_ne_zero hC0 hpos
  have hnt : (C : ℝ≥0∞) * adeleMeasure L S ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top htop
  have h3 := (ENNReal.mul_left_inj hne hnt).1 h2
  have hK0 : (0 : ℝ) ≤ (IdeleGroup.ideleModule K x : ℝ)⁻¹ :=
    inv_nonneg.2 (IdeleGroup.ideleModule K x).2.le
  have h4 : ((c ^ n : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (((IdeleGroup.ideleModule K x : ℝ))⁻¹ ^ n) := by
    rw [ENNReal.ofReal_pow hK0, ENNReal.coe_pow]
    rfl
  rw [h4] at h3
  have h5 := (ENNReal.ofReal_eq_ofReal_iff (inv_nonneg.2 (IdeleGroup.ideleModule L X).2.le)
    (pow_nonneg hK0 n)).1 h3
  rw [inv_pow] at h5
  exact inv_inj.1 h5

end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
  PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

theorem ideleModule_ideleEquiv_ofF : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ a : (AF F)ˣ,
    (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (ofF a)) : ℝ) = md a ^ 2 := by
  intro F E _ _ _ _ _ σ hcm a
  have he : GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (ofF a) = ideleEmbedding F E a :=
    Units.ext (GroundTheory.BlockD.ThmBHecke.adeleEquiv_algebraMap (a : AF F))
  rw [he, ideleModule_ideleEmbedding, hcm.2.2.1]
  rfl

end

end GlobalTheory.CompanionTheory.SW.MdBase
