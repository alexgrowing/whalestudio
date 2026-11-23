import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsLeSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

noncomputable section

open scoped Pointwise

namespace GlobalTheory.ThKOrthVInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isHermND_smul_of_skew {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hsk : ∀ k l, σ (J l k) = -J k l) (hd : J.det ≠ 0) {c : E} (hc : c ≠ 0) (hcs : σ c = -c) :
    IsHermND σ (c • J.map σ) := by
  refine ⟨fun i j => ?_, ?_⟩
  · have h1 : σ (J i j) = -J j i := hsk j i
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, hcs, hσ, h1]
    ring
  · have e : (J.map σ).det = (σ : E →+* E) J.det := by rw [RingHom.map_det]; rfl
    rw [Matrix.det_smul, e]
    exact mul_ne_zero (pow_ne_zero _ hc) ((map_ne_zero _).2 hd)

theorem measure_fundDom_lt_top_smul (hP : GlobalTheory.Published.SiegelSetUnitary) {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {c : E} (hc : c ≠ 0) (hJ : IsHermND σ (c • J.map σ)) {μ : Measure (UA σ J)}
    [μ.IsHaarMeasure] {D : Set (UA σ J)} (hD : IsFundamentalDomain (ratU σ J) D μ) : μ D < ⊤ := by
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hcm
  have heq : UG (cA σ) (incM F J) = HR (AF F) σ (c • J.map σ) := GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := J) hσ hc
  let e : UA σ J ≃* GAd σ (c • J.map σ) := MulEquiv.subgroupCongr heq
  have he : Continuous e := continuous_subtype_val.subtype_mk _
  have he' : Continuous e.symm := continuous_subtype_val.subtype_mk _
  obtain ⟨S, hSc, hcov, -, hfin, -⟩ := GlobalTheory.SiegelSet.exists_cover hP hcm hJ
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  haveI : ContinuousMul (UA σ J) := ⟨by
    have h3 : (fun p : UA σ J × UA σ J => p.1 * p.2) = fun p => e.symm (e p.1 * e p.2) :=
      funext fun p => by rw [← map_mul, MulEquiv.symm_apply_apply]
    rw [h3]
    exact he'.comp ((he.comp continuous_fst).mul (he.comp continuous_snd))⟩
  have hH : (μ.map e).IsHaarMeasure := MulEquiv.isHaarMeasure_map μ e he he'
  have h1 : μ (e ⁻¹' S) < ⊤ := by
    have h2 := hfin _ hH
    rwa [Measure.map_apply he.measurable hSc.measurableSet] at h2
  haveI := GlobalTheory.UnitaryVol.countable_ratU σ J
  haveI : MeasurableMul (UA σ J) :=
    ⟨fun g => (continuous_const.mul continuous_id).measurable, fun g => (continuous_id.mul continuous_const).measurable⟩
  haveI : MeasurableConstSMul (ratU σ J) (UA σ J) :=
    ⟨fun γ => (continuous_const.mul continuous_id : Continuous fun x : UA σ J => γ.1 * x).measurable⟩
  haveI : SMulInvariantMeasure (ratU σ J) (UA σ J) μ := ⟨fun γ A _ => measure_preimage_mul μ γ.1 A⟩
  have hcov' : D ⊆ ⋃ γ : ratU σ J, γ • (e ⁻¹' S) ∩ D := by
    intro x hx
    obtain ⟨γ, hγ, s, hs, hxs⟩ := hcov (e x)
    obtain ⟨u, -, hu⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
    have hr : e.symm γ ∈ ratU σ J := Subgroup.mem_subgroupOf.2 ⟨u, hu⟩
    refine Set.mem_iUnion.2 ⟨⟨e.symm γ, hr⟩, Set.mem_smul_set.2 ⟨e.symm s, show e (e.symm s) ∈ S by rw [MulEquiv.apply_symm_apply]; exact hs, ?_⟩, hx⟩
    change e.symm γ * e.symm s = x
    rw [← map_mul, ← hxs, MulEquiv.symm_apply_apply]
  calc μ D ≤ μ (⋃ γ : ratU σ J, γ • (e ⁻¹' S) ∩ D) := measure_mono hcov'
    _ ≤ ∑' γ : ratU σ J, μ (γ • (e ⁻¹' S) ∩ D) := measure_iUnion_le _
    _ = μ (e ⁻¹' S) := (hD.measure_eq_tsum _).symm
    _ < ⊤ := h1

theorem norm_le_qht_of_le_ht {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g : UA σ J → ℂ}
    (hgi : ∀ γ ∈ ratU σ J, ∀ x, g (γ * x) = g x) {C : ℝ} {k : ℕ} (hC : ∀ h, ‖g h‖ ≤ C * (ht h : ℝ) ^ k) (h : UA σ J) :
    ‖g h‖ ≤ max C 0 * (qht h : ℝ) ^ k := by
  let M : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have e1 : M * qht h ^ k = ⨅ γ : ratU σ J, M * ht (γ.1 * h) ^ k :=
    Monotone.map_ciInf_of_continuousAt (f := fun x : ℝ≥0 => M * x ^ k)
      ((continuous_const.mul (continuous_pow k)).continuousAt)
      (fun x y hxy => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hxy k) (by positivity))
      (OrderBot.bddBelow _)
  have e2 : ‖g h‖₊ ≤ M * qht h ^ k := by
    rw [e1]
    refine le_ciInf fun γ => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, ← hgi γ.1 γ.2 h]
    refine (hC _).trans ?_
    push_cast
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have e3 := NNReal.coe_le_coe.2 e2
  push_cast at e3
  exact e3

end GlobalTheory.ThKOrthVInt
