import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHaarRightInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftDef
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LiftConst
open GlobalTheory.SiegelSet

noncomputable section

namespace GlobalTheory.SkewUnimod

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem det_ne_zero_of_isSkew {σ : E →ₐ[F] E} {B : Base F E} {n : ℕ} {W : Spc F E n} {r s : ℕ}
    (h : W.IsSkew σ B r s) : W.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace F) := inferInstance
  intro hz
  apply GlobalTheory.UnitaryVol.det_ne_zero_of_isCartan (h.cartan w)
  rw [Matrix.det_smul, show W.J.map (B.emb w).1 = ((B.emb w).1).mapMatrix W.J from rfl, ← RingHom.map_det, hz, map_zero,
    mul_zero]

theorem isHermND_smul_map {σ : E →ₐ[F] E} {B : Base F E} {n : ℕ} {W : Spc F E n} {r s : ℕ}
    (hσ : ∀ x, σ (σ x) = x) (h : W.IsSkew σ B r s) {δ : E} (hδ : δ ≠ 0) (hσδ : σ δ = -δ) :
    IsHermND σ (δ • W.J.map σ) := by
  refine ⟨fun i j => ?_, ?_⟩
  · simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, hσ, hσδ]
    rw [h.skew j i]
    ring
  · rw [Matrix.det_smul, show W.J.map σ = (σ : E →+* E).mapMatrix W.J from rfl, ← RingHom.map_det]
    exact mul_ne_zero (pow_ne_zero _ hδ) ((map_ne_zero _).2 (det_ne_zero_of_isSkew h))

theorem isMulRightInvariant_of_isSkew : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (W : Spc F E n) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ μ : Measure (UA σ W.J), μ.IsHaarMeasure → μ.IsMulRightInvariant := by
  intro F E _ _ _ _ _ σ B n W r s hB hW μ hμ
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hB.cm
  obtain ⟨δ, hδ, hσδ⟩ := GlobalTheory.HermUnimod.exists_anti hB.cm
  have hJ : IsHermND σ (δ • W.J.map σ) := isHermND_smul_map hσ hW hδ hσδ
  have heq : GlobalTheory.WeilM.UG (cA σ) (incM F W.J) = HR (AF F) σ (δ • W.J.map σ) :=
    GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := W.J) hσ hδ
  let e : UA σ W.J ≃* HA (AF F) σ (δ • W.J.map σ) := MulEquiv.subgroupCongr heq
  have he : Continuous e := continuous_subtype_val.subtype_mk _
  have he' : Continuous e.symm := continuous_subtype_val.subtype_mk _
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  haveI : BorelSpace (HA (AF F) σ (δ • W.J.map σ)) := ⟨rfl⟩
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalGroup (HA (AF F) σ (δ • W.J.map σ)) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF F) σ (δ • W.J.map σ)))
  haveI : ContinuousMul (UA σ W.J) := ⟨by
    have h3 : (fun p : UA σ W.J × UA σ W.J => p.1 * p.2) = fun p => e.symm (e p.1 * e p.2) :=
      funext fun p => by rw [← map_mul, MulEquiv.symm_apply_apply]
    rw [h3]
    exact he'.comp ((he.comp continuous_fst).mul (he.comp continuous_snd))⟩
  haveI : (μ.map e).IsHaarMeasure := MulEquiv.isHaarMeasure_map μ e he he'
  have hR : (μ.map e).IsMulRightInvariant :=
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_adelic σ hσ hδ hσδ hJ (μ.map e)
  have hem : Measurable e := he.measurable
  have hem' : Measurable e.symm := he'.measurable
  refine ⟨fun g => ?_⟩
  have hmg : Measurable fun y : HA (AF F) σ (δ • W.J.map σ) => y * e g := (continuous_mul_right (e g)).measurable
  have h1 : (μ.map e).map e.symm = μ := by
    rw [Measure.map_map hem' hem]
    have : (e.symm ∘ e : UA σ W.J → UA σ W.J) = id := funext fun x => e.symm_apply_apply x
    rw [this, Measure.map_id]
  have h2 : ((μ.map e).map (fun y => y * e g)).map e.symm = μ.map (· * g) := by
    rw [Measure.map_map hmg hem, Measure.map_map hem' (hmg.comp hem)]
    congr 1
  rw [← h2, hR.map_mul_right_eq_self (e g), h1]

end GlobalTheory.SkewUnimod
