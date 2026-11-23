import Mathlib
import GroundTheory.AutomorphicForms.ReductionMahler
import GroundTheory.PowerSubgroups.CountableNeighbourhoods.GLnPowerSubgroups

open NumberField IsDedekindDomain Topology Filter Set Matrix MeasureTheory
open scoped NumberField.AdeleRing RestrictedProduct ENNReal
open GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace GroundTheory.Automorphic

noncomputable section

namespace Reduction

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def rpowHom (e : ℝ) : {r : ℝ // 0 < r} →* {r : ℝ // 0 < r} where
  toFun s := ⟨s.1 ^ e, Real.rpow_pos_of_pos s.2 e⟩
  map_one' := Subtype.ext (Real.one_rpow e)
  map_mul' s t := Subtype.ext (Real.mul_rpow s.2.le t.2.le)

theorem continuous_rpowHom (e : ℝ) : Continuous (rpowHom e) :=
  (continuous_subtype_val.rpow_const fun s => Or.inl s.2.ne').subtype_mk _

variable (K) in

def posIdeleHom : {r : ℝ // 0 < r} →* IdeleGroup K where
  toFun s := posIdele s.1 s.2
  map_one' := by
    unfold posIdele
    refine Finset.prod_eq_one fun w _ => ?_
    convert map_one (moduleSection (K := K) w)
    exact one_pow _
  map_mul' s t := by
    unfold posIdele
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [← map_mul]
    congr 1
    exact Subtype.ext (by simp only [Positive.val_mul, mul_pow])

theorem posIdeleHom_apply (s : {r : ℝ // 0 < r}) : posIdeleHom K s = posIdele s.1 s.2 := rfl

theorem continuous_posIdeleHom : Continuous (posIdeleHom K) :=
  continuous_posIdele_subtype

variable (K n) in

def scalarUnits : IdeleGroup K →* AdelicGLn.AdelicGL K n :=
  (diagUnits n).comp
    { toFun := fun u _ => u, map_one' := rfl, map_mul' := fun _ _ => rfl }

theorem scalarUnits_apply (u : IdeleGroup K) : scalarUnits K n u = diagUnits n fun _ => u := rfl

theorem continuous_scalarUnits : Continuous (scalarUnits K n) :=
  (continuous_diagUnits n).comp (continuous_pi fun _ => continuous_id)

theorem scalarUnits_mul_comm (u : IdeleGroup K) (g : AdelicGLn.AdelicGL K n) :
    scalarUnits K n u * g = g * scalarUnits K n u := by
  refine Units.ext ?_
  simp only [Units.val_mul, scalarUnits_apply, coe_diagUnits]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

variable (K) in

def centralSection (n : ℕ) : {r : ℝ // 0 < r} →* AdelicGLn.AdelicGL K n :=
  (scalarUnits K n).comp ((posIdeleHom K).comp (rpowHom ((n * Module.finrank ℚ K : ℝ))⁻¹))

theorem continuous_centralSection : Continuous (centralSection K n) :=
  continuous_scalarUnits.comp (continuous_posIdeleHom.comp (continuous_rpowHom _))

theorem centralSection_mul_comm (s : {r : ℝ // 0 < r}) (g : AdelicGLn.AdelicGL K n) :
    centralSection K n s * g = g * centralSection K n s :=
  scalarUnits_mul_comm _ g

variable (K n) in

def detModule : AdelicGLn.AdelicGL K n →* {r : ℝ // 0 < r} :=
  (ideleModule K).comp (AdelicGLn.det K n)

theorem continuous_detModule : Continuous (detModule K n) :=
  continuous_ideleModule.comp (AdelicGLn.continuous_det K n)

theorem mem_normOneGL_iff_detModule {g : AdelicGLn.AdelicGL K n} :
    g ∈ normOneGL K n ↔ detModule K n g = 1 := by
  rw [mem_normOneGL]
  exact ⟨fun h => Subtype.ext (h.trans Positive.val_one.symm),
    fun h => (congrArg Subtype.val h).trans Positive.val_one⟩

theorem detModule_centralSection (hn : 0 < n) (s : {r : ℝ // 0 < r}) :
    detModule K n (centralSection K n s) = s := by
  refine Subtype.ext ?_
  have hd0 : 0 < Module.finrank ℚ K := Module.finrank_pos
  have h1 : (detModule K n (centralSection K n s) : ℝ) =
      ∏ _i : Fin n, (ideleModule K (posIdeleHom K (rpowHom ((n * Module.finrank ℚ K : ℝ))⁻¹ s)) : ℝ) := by
    rw [detModule, MonoidHom.comp_apply, centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply,
      scalarUnits_apply, det_diagUnits, map_prod, coe_finset_prod_pos]
  rw [h1, Finset.prod_const, Finset.card_univ, Fintype.card_fin, posIdeleHom_apply,
    ideleModule_posIdele]
  change ((s.1 ^ ((n * Module.finrank ℚ K : ℝ))⁻¹) ^ Module.finrank ℚ K) ^ n = s.1
  rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul s.2.le]
  have hne : (n * Module.finrank ℚ K : ℝ) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 hn.ne') (Nat.cast_ne_zero.2 hd0.ne')
  rw [show ((n * Module.finrank ℚ K : ℝ))⁻¹ * ((Module.finrank ℚ K * n : ℕ) : ℝ) = 1 by
    push_cast; field_simp, Real.rpow_one]

def glNormOneSplitting (hn : 0 < n) :
    AdelicGLn.AdelicGL K n ≃ₜ* normOneGL K n × {r : ℝ // 0 < r} :=
  GroundTheory.Variant₂.N1.centralSplitting (detModule K n) continuous_detModule (centralSection K n)
    continuous_centralSection (detModule_centralSection hn) centralSection_mul_comm (normOneGL K n)
    (fun _ => mem_normOneGL_iff_detModule)

@[simp] theorem glNormOneSplitting_symm_apply (hn : 0 < n) (p : normOneGL K n × {r : ℝ // 0 < r}) :
    (glNormOneSplitting (K := K) hn).symm p = (p.1 : AdelicGLn.AdelicGL K n) * centralSection K n p.2 := by
  rfl

theorem exists_measure_eq_mul_measure_image (hn : 0 < n)
    [SecondCountableTopology (AdelicGLn.AdelicGL K n)] [MeasurableSpace (AdelicGLn.AdelicGL K n)]
    [BorelSpace (AdelicGLn.AdelicGL K n)]
    (μ₁ : Measure (normOneGL K n)) [μ₁.IsHaarMeasure]
    (μ : Measure (AdelicGLn.AdelicGL K n)) [μ.IsHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ E : Set (normOneGL K n), MeasurableSet E →
      μ₁ E = c * μ ((fun p : normOneGL K n × {r : ℝ // 0 < r} =>
        (p.1 : AdelicGLn.AdelicGL K n) * centralSection K n p.2) '' (E ×ˢ posRealUnitInterval)) := by
  have : SecondCountableTopology (normOneGL K n) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  set Φ : AdelicGLn.AdelicGL K n ≃ₜ* normOneGL K n × {r : ℝ // 0 < r} :=
    GroundTheory.Variant₂.N1.centralSplitting (detModule K n) continuous_detModule (centralSection K n)
      continuous_centralSection (detModule_centralSection hn) centralSection_mul_comm
      (normOneGL K n) (fun _ => mem_normOneGL_iff_detModule) with hΦ
  have hΦs : ∀ p : normOneGL K n × {r : ℝ // 0 < r},
      Φ.symm p = (p.1 : AdelicGLn.AdelicGL K n) * centralSection K n p.2 := fun p => rfl
  have hΦm : Measurable (Φ : AdelicGLn.AdelicGL K n → normOneGL K n × {r : ℝ // 0 < r}) :=
    Φ.continuous.measurable
  set lam : Measure (normOneGL K n × {r : ℝ // 0 < r}) := μ.map Φ with hlam
  have hlamH : lam.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ Φ
  have hν : posRealMeasure posRealUnitInterval = 1 := posRealMeasure_posRealUnitInterval
  set ρ : Measure (normOneGL K n) :=
    Measure.map Prod.fst (lam.restrict (Set.univ ×ˢ posRealUnitInterval)) with hρ
  have hρH : ρ.IsHaarMeasure := isHaarMeasure_map_fst_restrict lam posRealMeasure hν
  have hμ₁ : μ₁ = Measure.haarScalarFactor μ₁ ρ • ρ := Measure.isMulLeftInvariant_eq_smul μ₁ ρ
  refine ⟨(Measure.haarScalarFactor μ₁ ρ : ℝ≥0∞), ENNReal.coe_ne_top, fun E hE => ?_⟩
  have hS : MeasurableSet posRealUnitInterval := measurableSet_posRealUnitInterval
  have hρE : ρ E = μ (Φ ⁻¹' (E ×ˢ posRealUnitInterval)) := by
    rw [hρ, Measure.map_apply measurable_fst hE, Measure.restrict_apply (measurable_fst hE),
      hlam, Measure.map_apply hΦm]
    · congr 1
      ext p
      simp [and_comm]
    · exact (measurable_fst hE).inter (MeasurableSet.univ.prod hS)
  have himg : Φ ⁻¹' (E ×ˢ posRealUnitInterval) =
      (fun p : normOneGL K n × {r : ℝ // 0 < r} =>
        (p.1 : AdelicGLn.AdelicGL K n) * centralSection K n p.2) '' (E ×ˢ posRealUnitInterval) := by
    ext g
    constructor
    · intro hg
      exact ⟨Φ g, hg, (hΦs (Φ g)).symm.trans (Φ.symm_apply_apply g)⟩
    · rintro ⟨p, hp, rfl⟩
      show Φ ((p.1 : AdelicGLn.AdelicGL K n) * centralSection K n p.2) ∈ E ×ˢ posRealUnitInterval
      rw [← hΦs p, ContinuousMulEquiv.apply_symm_apply]
      exact hp
  have h1 : μ₁ E = (Measure.haarScalarFactor μ₁ ρ • ρ) E :=
    congrArg (fun m : Measure (normOneGL K n) => m E) hμ₁
  rw [h1, Measure.smul_apply, hρE, himg, ENNReal.smul_def, smul_eq_mul]

end Reduction

end

end GroundTheory.Automorphic
