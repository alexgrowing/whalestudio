import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXLeb
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXECPf

noncomputable section

open MeasureTheory Matrix NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf
  Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates Formalism.L2.SG.RealObj.InfCut

theorem det_LyM {r k : ℕ} {T : ℝ} (hT : 0 < T) : LinearMap.det (LyM (k := k) (r := r) T) = T ^ r := by
  rw [LyM, LinearMap.det_toLin', Matrix.det_diagonal]
  simp only [Fintype.prod_sum_type, dY, Finset.prod_const_one, one_mul, mul_one, Finset.prod_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  rw [show r * 2 = 2 * r by ring, pow_mul, Real.sq_sqrt hT.le]

theorem refN_map_kapL {n r k : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ)
    (w : Fin k → Fin n → ℂ) (z : Fin n → ℂ) {T : ℝ} (hT : 0 < T)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hww : ∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (w a) = 0) (hfw : ∀ c a, hJ ε (f c) (w a) = 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hzw : ∀ a, hJ ε z (w a) = 0) :
    AEMeasurable (kapL ε e f w z) (refNg hn ε e f w (z0v T z)) ∧
      (refNg hn ε e f w (z0v T z)).map (kapL ε e f w z) =
        ENNReal.ofReal ((2 : ℝ) ^ (r ^ 2 + r * k) * (T ^ r)⁻¹) • volume := by
  subst hn
  have hFJ := isFrameJ_of hT hee hff hef hww hew hfw hez hfz hzz hzw
  have emb := embQ hFJ
  have hQz : Qm e f w (z0v T z) *ᵥ zBv k r T = z := Qm_zB hT z
  set Ψ := cM (ε := ε) (Qi ε e f w (z0v T z)) (Qm e f w (z0v T z)) with hΨ
  let Φ : (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ) → Mt k r := fun t => WlocSk.NB.phi0 t.1 t.2
  have hΦc : Continuous Φ := WlocSk.NB.continuous_nilpotent_chart
  let ψ : Mt k r → (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ) := fun x => (WlocSk.NB.psiC x, WlocSk.NB.psiR x)
  have hψc : Continuous ψ := WlocSk.NB.continuous_psiC.prodMk WlocSk.NB.continuous_psiR
  have hleft : Function.LeftInverse ψ Φ := fun t => by
    obtain ⟨h1, h2⟩ := WlocSk.NB.nilpotent_chart_right_inverse t.1 t.2
    show (WlocSk.NB.psiC (WlocSk.NB.phi0 t.1 t.2), WlocSk.NB.psiR (WlocSk.NB.phi0 t.1 t.2)) = t
    rw [h1, h2]
  have hΦe : MeasurableEmbedding Φ := by
    refine MeasurableEmbedding.of_measurable_inverse hΦc.measurable ?_ hψc.measurable hleft
    have hr : Set.range Φ = {x | Φ (ψ x) = x} := by
      ext x
      constructor
      · rintro ⟨t, rfl⟩
        show Φ (ψ (Φ t)) = Φ t
        rw [hleft t]
      · intro hx
        exact ⟨ψ x, hx⟩
    rw [hr]
    exact (isClosed_eq (hΦc.comp hψc) continuous_id).measurableSet
  have hΦN : ∀ t : (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ), WlocSk.NB.phi0 t.1 t.2 ∈ Nset k r := fun t =>
    WlocSk.NB.test_vector_mem_schwartz_bruhat t.1 t.2
  set ν := (volume : Measure ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ))).map Φ with hν
  haveI : SigmaFinite ν := hΦe.sigmaFinite_map
  have hν0 : ν ≠ 0 := by
    intro h0
    rw [hν, Measure.map_eq_zero_iff hΦe.measurable.aemeasurable] at h0
    exact isOpen_univ.measure_ne_zero (volume : Measure ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ))) Set.univ_nonempty
      (by rw [h0, Measure.coe_zero, Pi.zero_apply])
  have hrange : ∀ t, ∃ g : Formalism.REAL.UJ ε, Ψ g = Φ t := fun t => by
    refine ⟨toUJ _ (conjQ_UJ hFJ (hΦN t).1), ?_⟩
    show (Qi ε e f w (z0v T z) * uMat (toUJ _ (conjQ_UJ hFJ (hΦN t).1)) * Qm e f w (z0v T z) :
      Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = WlocSk.NB.phi0 t.1 t.2
    rw [uMat_toUJ, Qi_Qm_conj hFJ]
  set lam0 := Measure.comap Ψ ν with hlam0
  have hmap : lam0.map Ψ = ν := by
    rw [hlam0, emb.map_comap]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff, hν, hΦe.map_apply]
    convert measure_empty (μ := (volume : Measure ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ))))
    ext t
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    obtain ⟨g, hg⟩ := hrange t
    exact ⟨g, hg⟩
  haveI : SigmaFinite lam0 := SigmaFinite.of_map _ emb.measurable.aemeasurable (by rw [hmap]; infer_instance)
  have hNz : NLoc ε e (Qm e f w (z0v T z) *ᵥ zBv k r T) = NLoc ε e z := by rw [hQz]
  have hz0 : ∃ t : ℂ, z0v T z = t • (Qm e f w (z0v T z) *ᵥ zBv k r T) :=
    ⟨(((Real.sqrt T)⁻¹ : ℝ) : ℂ), by rw [hQz]; rfl⟩
  have hHaar : IsHaarLoc (NLoc ε e z) lam0 := by
    refine ⟨inferInstance, fun h0 => hν0 (by rw [← hmap, h0, Measure.map_zero]), ?_, fun s hs => ?_⟩
    · rw [hlam0, emb.comap_apply, hν, hΦe.map_apply]
      convert measure_empty (μ := (volume : Measure ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ))))
      ext t
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false,
        not_exists, not_and]
      intro g hg hgt
      apply hg
      rw [← hNz]
      refine inN_of_conj hFJ (inWb_zB T) ?_
      have : (Qi ε e f w (z0v T z) * uMat g * Qm e f w (z0v T z) :
          Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = WlocSk.NB.phi0 t.1 t.2 := hgt
      rw [this]; exact hΦN t
    · have hs' : InN ε e (Qm e f w (z0v T z) *ᵥ zBv k r T) (uMat s) := by
        have h1 : s ∈ NLoc ε e (Qm e f w (z0v T z) *ᵥ zBv k r T) := by rw [hNz]; exact hs
        exact h1
      have h0 : Qi ε e f w (z0v T z) * uMat s * Qm e f w (z0v T z) ∈ Nset k r :=
        conj_mem_Nset hFJ hz0 (uMat_mem s) hs'
      set m0 := Qi ε e f w (z0v T z) * uMat s * Qm e f w (z0v T z) with hm0
      have hfun : Ψ ∘ (fun x => s * x) = lmulM m0 ∘ Ψ := by
        funext x
        show (Qi ε e f w (z0v T z) * uMat (s * x) * Qm e f w (z0v T z) :
          Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) =
          m0 * (Qi ε e f w (z0v T z) * uMat x * Qm e f w (z0v T z))
        rw [uMat_mul, hm0]
        simp only [← Matrix.mul_assoc]
        rw [Matrix.mul_assoc (Qi ε e f w (z0v T z) * uMat s) (Qm e f w (z0v T z)) (Qi ε e f w (z0v T z)),
          Qm_mul_Qi hFJ, Matrix.mul_one]
      have hsh : lmulM m0 ∘ Φ = Φ ∘ (fun t : (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ) =>
          (t.1 + WlocSk.NB.shG m0 t.1, t.2 + WlocSk.NB.shH m0 t.1)) := by
        funext t
        obtain ⟨h1, h2⟩ := WlocSk.NB.lmul_coord h0 t.1 t.2
        have hmem := WlocSk.UnitaryGroupBasics.mem_n_mul h0 (WlocSk.NB.test_vector_mem_schwartz_bruhat t.1 t.2)
        show m0 * WlocSk.NB.phi0 t.1 t.2 =
          WlocSk.NB.phi0 (t.1 + WlocSk.NB.shG m0 t.1) (t.2 + WlocSk.NB.shH m0 t.1)
        rw [← h1, ← h2]
        exact (WlocSk.NB.nilpotent_chart_left_inverse hmem).symm
      have hmp := WlocSk.NB.shear_mp (d := r) WlocSk.NB.rk (WlocSk.NB.shG m0) (WlocSk.NB.shH m0)
        (fun i => (WlocSk.NB.continuous_shG m0 i).measurable) (fun i x y h => WlocSk.NB.shG_dep m0 i x y h)
        (WlocSk.NB.continuous_shH m0).measurable
      have key : (lam0.map (fun x => s * x)).map Ψ = lam0.map Ψ := by
        rw [Measure.map_map emb.measurable (measurable_const_mul s), hfun,
          ← Measure.map_map (measurable_lmulM m0) emb.measurable, hmap, hν,
          Measure.map_map (measurable_lmulM m0) hΦe.measurable, hsh,
          ← Measure.map_map hΦe.measurable hmp.measurable, hmp.map_eq]
      rw [← emb.comap_map (lam0.map (fun x => s * x)), key, emb.comap_map]
  have hkc : ∀ᵐ g ∂lam0, kapL ε e f w z g = (Kc T ∘ Ψ) g := by
    filter_upwards [(ae_iff.2 hHaar.2.2.1 : ∀ᵐ g ∂lam0, g ∈ NLoc ε e z)] with g hg
    have hg' : InN ε e (Qm e f w (z0v T z) *ᵥ zBv k r T) (uMat g) := by
      have h1 : g ∈ NLoc ε e (Qm e f w (z0v T z) *ᵥ zBv k r T) := by rw [hNz]; exact hg
      exact h1
    exact kapL_eq hFJ hT g (conj_mem_Nset hFJ hz0 (uMat_mem g) hg')
  have hdet := det_LyM_ne (k := k) (r := r) hT
  set c : ℝ≥0∞ := ENNReal.ofReal |(LinearMap.det (LyM (k := k) (r := r) T))⁻¹| with hc
  have hc0 : c ≠ 0 := by rw [hc]; exact (ENNReal.ofReal_pos.2 (abs_pos.2 (inv_ne_zero hdet))).ne'
  have hcT : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmeasK : AEMeasurable (kapL ε e f w z) lam0 :=
    ((Kc_cont T).measurable.comp emb.measurable).aemeasurable.congr (Filter.EventuallyEq.symm hkc)
  have hcomp : Kc T ∘ Φ = LyM (k := k) (r := r) T ∘ Rc := by
    funext t
    funext i
    rw [Function.comp_apply, Function.comp_apply, LyM_apply]
    exact chart_kappa_coordinates T t i
  have hH : Formalism.MainNotions.S.haarLie (Nset k r) 1 = ENNReal.ofReal ((2 : ℝ) ^ (r ^ 2 + r * k)) • ν := by
    rw [hν]
    exact exponential_chart_haar k r
  have hrefN : refNg rfl ε e f w (z0v T z) = ENNReal.ofReal ((2 : ℝ) ^ (r ^ 2 + r * k)) • lam0 := by
    rw [refNg_rfl]
    ext s _
    show (Measure.comap Ψ (Formalism.MainNotions.S.haarLie (Nset k r) 1)) s = _
    rw [emb.comap_apply, hH, Measure.smul_apply, Measure.smul_apply, hlam0, emb.comap_apply]
  have hlamK : lam0.map (kapL ε e f w z) = c • volume := by
    rw [Measure.map_congr hkc, ← Measure.map_map (Kc_cont T).measurable emb.measurable, hmap, hν,
      Measure.map_map (Kc_cont T).measurable hΦe.measurable, hcomp,
      ← Measure.map_map (LyM (k := k) (r := r) T).continuous_of_finiteDimensional.measurable Rc_cont.measurable,
      map_Rc, Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet, ← hc]
  refine ⟨?_, ?_⟩
  · rw [hrefN]
    exact hmeasK.smul_measure _
  · rw [hrefN, Measure.map_smul, hlamK, smul_smul, hc, det_LyM hT, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [abs_of_pos (by positivity)]

end Formalism.L2.SG.Pf.NcReal.JX
