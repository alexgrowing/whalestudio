import Mathlib
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.WeilPolarization.WmSysObjects
import GroundTheory.HeightsAndTheta.Theta.SchroedingerTranslates.ExistsInverseFontaineElementMemFilNegOne
import GroundTheory.HeightsAndTheta.Theta.LocallyCompactField.Countability

noncomputable section

namespace GroundTheory.Heights₂.Theta

namespace WmSysEquiv

open MeasureTheory Measure Topology Filter Set
open scoped NNReal ENNReal Pointwise

set_option linter.unusedSectionVars false

section General

variable {G : Type*} [AddGroup G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
  [IsTopologicalAddGroup G] [LocallyCompactSpace G]

theorem addEquivAddHaarChar_eq_of_preimage (μ : Measure G) [μ.IsAddHaarMeasure] [μ.Regular]
    (φ : G ≃ₜ+ G) {S : Set G} {c : ℝ≥0} (h0 : μ (φ ⁻¹' S) ≠ 0) (htop : μ (φ ⁻¹' S) ≠ ∞)
    (h : (c : ℝ≥0∞) * μ (φ ⁻¹' S) = μ S) : addEquivAddHaarChar φ = c := by
  have h1 := addEquivAddHaarChar_smul_preimage μ (X := S) φ
  rw [ENNReal.smul_def, smul_eq_mul] at h1
  exact ENNReal.coe_injective ((ENNReal.mul_left_inj h0 htop).1 (h1.trans h.symm))

theorem addEquivAddHaarChar_conj {G' : Type*} [AddGroup G'] [TopologicalSpace G']
    [MeasurableSpace G'] [BorelSpace G'] [IsTopologicalAddGroup G'] [LocallyCompactSpace G']
    (b : G ≃ₜ+ G') (H : G ≃ₜ+ G) :
    addEquivAddHaarChar ((b.symm.trans H).trans b) = addEquivAddHaarChar H := by
  let μ : Measure G' := addHaar
  let e : G' ≃ᵐ G := b.symm.toHomeomorph.toMeasurableEquiv
  let ν : Measure G := μ.map e
  have : ν.IsAddHaarMeasure := b.symm.isAddHaarMeasure_map μ
  have : ν.Regular := Regular.map b.symm.toHomeomorph
  have hν : ∀ T : Set G, μ (e ⁻¹' T) = ν T := fun T => (e.map_apply T).symm
  obtain ⟨K, hKc, hK0⟩ : ∃ K : Set G, IsCompact K ∧ K ∈ 𝓝 (0 : G) := exists_compact_mem_nhds 0
  have hpre : ⇑((b.symm.trans H).trans b) ⁻¹' (e ⁻¹' K) = e ⁻¹' (H ⁻¹' K) := by
    ext y
    simp only [Set.mem_preimage]
    change b.symm (b (H (b.symm y))) ∈ K ↔ H (b.symm y) ∈ K
    rw [b.symm_apply_apply]
  have hHK0 : H ⁻¹' K ∈ 𝓝 (0 : G) := by
    have hc : Tendsto (fun x => H x) (𝓝 0) (𝓝 (H 0)) := H.continuous.tendsto 0
    rw [map_zero] at hc
    exact hc hK0
  have hHKc : IsCompact (H ⁻¹' K) := H.toHomeomorph.isCompact_preimage.2 hKc
  refine addEquivAddHaarChar_eq_of_preimage μ _ (S := e ⁻¹' K) ?_ ?_ ?_
  · rw [hpre, hν]
    exact (measure_pos_of_mem_nhds ν hHK0).ne'
  · rw [hpre, hν]
    exact hHKc.measure_lt_top.ne
  · rw [hpre, hν, hν]
    have h1 := addEquivAddHaarChar_smul_preimage ν (X := K) H
    rwa [ENNReal.smul_def, smul_eq_mul] at h1

end General

section Pi

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace F]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def piHomeo (L : (ι → F) ≃ₗ[F] (ι → F)) : (ι → F) ≃ₜ+ (ι → F) :=
  { L.toAddEquiv with
    continuous_toFun := L.toLinearMap.continuous_on_pi
    continuous_invFun := L.symm.toLinearMap.continuous_on_pi }

@[simp] theorem piHomeo_apply (L : (ι → F) ≃ₗ[F] (ι → F)) (x : ι → F) : piHomeo L x = L x := rfl

variable (F ι) in

def glEquiv : GL ι F ≃* ((ι → F) ≃ₗ[F] (ι → F)) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F (ι → F))

theorem glEquiv_apply (g : GL ι F) (x : ι → F) :
    glEquiv F ι g x = (g : Matrix ι ι F).mulVec x := by
  simp [glEquiv, LinearMap.GeneralLinearGroup.generalLinearEquiv, Matrix.GeneralLinearGroup.toLin]

theorem det_glEquiv (g : GL ι F) :
    LinearEquiv.det (glEquiv F ι g) = Matrix.GeneralLinearGroup.det g := by
  ext
  rw [LinearEquiv.coe_det]
  show LinearMap.det (Matrix.toLin' (g : Matrix ι ι F)) = _
  rw [LinearMap.det_toLin']
  rfl

variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [SigmaCompactSpace F]

def piChar (L : (ι → F) ≃ₗ[F] (ι → F)) : ℝ≥0 := addEquivAddHaarChar (piHomeo L)

theorem piChar_mul (L M : (ι → F) ≃ₗ[F] (ι → F)) : piChar (L * M) = piChar L * piChar M := by
  have h : piHomeo (L * M) = (piHomeo M).trans (piHomeo L) := ContinuousAddEquiv.ext fun _ => rfl
  rw [piChar, h, addEquivAddHaarChar_trans, mul_comm]
  rfl

theorem piChar_one : piChar (1 : (ι → F) ≃ₗ[F] (ι → F)) = 1 := by
  have h : piHomeo (1 : (ι → F) ≃ₗ[F] (ι → F)) = ContinuousAddEquiv.refl _ :=
    ContinuousAddEquiv.ext fun _ => rfl
  rw [piChar, h, addEquivAddHaarChar_refl]

def glChar : GL ι F →* ℝ≥0 where
  toFun g := piChar (glEquiv F ι g)
  map_one' := by rw [map_one, piChar_one]
  map_mul' g g' := by rw [map_mul, piChar_mul]

theorem glChar_apply (g : GL ι F) : glChar g = piChar (glEquiv F ι g) := rfl

theorem glChar_diagonal {D : ι → F} (h : (Matrix.diagonal D).det ≠ 0) :
    glChar (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) =
      distribHaarChar F (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h)) := by
  have hD : ∀ i, D i ≠ 0 := fun i => by
    rw [Matrix.det_diagonal] at h
    exact Finset.prod_ne_zero_iff.1 h i (Finset.mem_univ i)
  let u : ι → Fˣ := fun i => Units.mk0 (D i) (hD i)
  have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) =
      ∏ i, u i := by
    ext
    simp [u, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.det_diagonal]
  rw [hdet, map_prod, glChar_apply, piChar]
  let ν : Measure F := addHaar
  let μ : Measure (ι → F) := Measure.pi fun _ => ν
  have : μ.Regular := isAddHaar_regular μ
  obtain ⟨K, hKc, hK0⟩ : ∃ K : Set F, IsCompact K ∧ K ∈ 𝓝 (0 : F) := exists_compact_mem_nhds 0
  have hν0 : ν K ≠ 0 := (measure_pos_of_mem_nhds ν hK0).ne'
  have hνtop : ν K ≠ ∞ := hKc.measure_lt_top.ne
  have hpre : ⇑(piHomeo (glEquiv F ι (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h))) ⁻¹'
      (Set.univ.pi fun _ => K) = Set.univ.pi fun i => (u i)⁻¹ • K := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, piHomeo_apply,
      glEquiv_apply]
    refine forall_congr' fun i => ?_
    change (Matrix.diagonal D).mulVec x i ∈ K ↔ x i ∈ ((u i)⁻¹ : Fˣ) • K
    rw [Matrix.mulVec_diagonal, Set.mem_inv_smul_set_iff, Units.smul_def]
    rfl
  have hP : μ (⇑(piHomeo (glEquiv F ι (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h))) ⁻¹'
      (Set.univ.pi fun _ => K)) = ∏ i, (((distribHaarChar F (u i))⁻¹ : ℝ≥0) : ℝ≥0∞) * ν K := by
    rw [hpre, Measure.pi_pi]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← map_inv, distribHaarChar_mul ν]
  have hpos : ∀ i, (distribHaarChar F (u i) : ℝ≥0) ≠ 0 := fun i => distribHaarChar_pos.ne'
  refine addEquivAddHaarChar_eq_of_preimage μ _ (S := Set.univ.pi fun _ => K) ?_ ?_ ?_
  · rw [hP]
    exact Finset.prod_ne_zero_iff.2 fun i _ =>
      mul_ne_zero (ENNReal.coe_ne_zero.2 (inv_ne_zero (hpos i))) hν0
  · rw [hP]
    exact ENNReal.prod_ne_top fun i _ => ENNReal.mul_ne_top ENNReal.coe_ne_top hνtop
  · rw [hP, Measure.pi_pi, ENNReal.ofNNReal_finsetProd, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← mul_assoc, ← ENNReal.coe_mul, mul_inv_cancel₀ (hpos i), ENNReal.coe_one, one_mul]

theorem glChar_transvection (t : Matrix.TransvectionStruct ι F) (h : t.toMatrix.det ≠ 0) :
    glChar (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) = 1 := by
  obtain ⟨i, j, hij, c⟩ := t
  have h1 : ∀ d : F, (Matrix.transvection i j d).det ≠ 0 := fun d => by
    rw [Matrix.det_transvection_of_ne _ _ hij]
    exact one_ne_zero
  let T : F → GL ι F := fun d => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (h1 d)
  have hT : ∀ d d', T d * T d' = T (d + d') := fun d d' => by
    ext : 1
    simp [T, Matrix.GeneralLinearGroup.mkOfDetNeZero,
      Matrix.transvection_mul_transvection_same (h := hij)]
  have hT0 : T 0 = 1 := by
    ext : 1
    simp [T, Matrix.GeneralLinearGroup.mkOfDetNeZero]

  have hconj : ∀ c : F, c ≠ 0 → glChar (T c) = glChar (T 1) := by
    intro c hc
    let d : ι → F := Function.update 1 i c
    have hd : (Matrix.diagonal d).det ≠ 0 := by
      rw [Matrix.det_diagonal]
      refine Finset.prod_ne_zero_iff.2 fun k _ => ?_
      by_cases hk : k = i
      · subst hk; simpa [d] using hc
      · simp [d, hk]
    let Dg : GL ι F := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd
    have hM : Matrix.transvection i j c * Matrix.diagonal d =
        Matrix.diagonal d * Matrix.transvection i j 1 := by
      ext a b
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, d]
      by_cases hab : a = b
      · subst hab
        by_cases hai : a = i
        · subst hai; simp [Ne.symm hij]
        · simp [hai, Ne.symm hai]
      · by_cases hai : a = i
        · subst hai
          by_cases hbj : b = j
          · subst hbj; simp [hab, Ne.symm hij]
          · simp [hab, Ne.symm hbj]
        · simp [hab, hai, Ne.symm hai]
    have hcomm : T c * Dg = Dg * T 1 := by
      ext : 1
      simpa [T, Dg, Matrix.GeneralLinearGroup.mkOfDetNeZero] using hM
    have key := congrArg glChar hcomm
    rw [map_mul, map_mul, mul_comm (glChar Dg)] at key
    exact (mul_left_inj' (show glChar Dg ≠ 0 from (addEquivAddHaarChar_pos _).ne')).1 key
  have hT1 : glChar (T 1) = 1 := by
    by_cases h2 : (2 : F) = 0
    · have h11 : T 1 * T 1 = 1 := by rw [hT, one_add_one_eq_two, h2, hT0]
      have hsq := congrArg glChar h11
      rw [map_mul, map_one] at hsq
      have hr : (glChar (T 1) : ℝ) * glChar (T 1) = 1 := by exact_mod_cast hsq
      rcases mul_self_eq_one_iff.1 hr with hr1 | hr1
      · exact NNReal.coe_eq_one.1 hr1
      · have := NNReal.coe_nonneg (glChar (T 1))
        linarith
    · have h11 : T 1 * T 1 = T 2 := by rw [hT, one_add_one_eq_two]
      have hsq := congrArg glChar h11
      rw [map_mul, hconj 2 h2] at hsq
      exact (mul_eq_left₀ (show glChar (T 1) ≠ 0 from (addEquivAddHaarChar_pos _).ne')).1 hsq
  change glChar (T c) = 1
  by_cases hc : c = 0
  · rw [hc, hT0, map_one]
  · rw [hconj c hc, hT1]

theorem glChar_eq (g : GL ι F) : glChar g = distribHaarChar F (Matrix.GeneralLinearGroup.det g) := by
  let ψ : GL ι F →* ℝ≥0 := (distribHaarChar F).comp Matrix.GeneralLinearGroup.det
  have key : ∀ (M : Matrix ι ι F) (h : M.det ≠ 0),
      glChar (Matrix.GeneralLinearGroup.mkOfDetNeZero M h) =
        ψ (Matrix.GeneralLinearGroup.mkOfDetNeZero M h) := by
    intro M hM
    refine Matrix.diagonal_transvection_induction_of_det_ne_zero
      (fun M => ∀ h : M.det ≠ 0, glChar (Matrix.GeneralLinearGroup.mkOfDetNeZero M h) =
        ψ (Matrix.GeneralLinearGroup.mkOfDetNeZero M h)) M hM ?_ ?_ ?_ hM
    · intro D _ h
      exact glChar_diagonal h
    · intro t h
      have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) = 1 := by
        ext
        simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]
      change glChar _ = distribHaarChar F _
      rw [glChar_transvection t h, hdet, map_one]
    · intro A B hA hB IHA IHB h
      have : Matrix.GeneralLinearGroup.mkOfDetNeZero (A * B) h =
          Matrix.GeneralLinearGroup.mkOfDetNeZero A hA *
            Matrix.GeneralLinearGroup.mkOfDetNeZero B hB := by
        ext : 1
        rfl
      rw [this, map_mul, map_mul, IHA hA, IHB hB]
  have hg : Matrix.GeneralLinearGroup.mkOfDetNeZero (g : Matrix ι ι F)
      (Matrix.det_ne_zero_of_left_inverse (g.inv_mul)) = g := by
    ext : 1
    rfl
  have := key _ (Matrix.det_ne_zero_of_left_inverse (g.inv_mul))
  rw [hg] at this
  exact this

theorem piChar_eq (L : (ι → F) ≃ₗ[F] (ι → F)) :
    piChar L = IndefiniteRowSideFullHecke.WmSys.absF (LinearMap.det (L : (ι → F) →ₗ[F] (ι → F))) := by
  obtain ⟨g, rfl⟩ := (glEquiv F ι).surjective L
  rw [← glChar_apply, glChar_eq, ← LinearEquiv.coe_det, det_glEquiv, IndefiniteRowSideFullHecke.WmSys.absF,
    dif_neg (Units.ne_zero _), Units.mk0_val]

end Pi

theorem addEquivAddHaarChar_eq_absF_det {F : Type*} [Field F] [TopologicalSpace F]
    [IsTopologicalRing F] [LocallyCompactSpace F] [T2Space F] (hF : ¬ DiscreteTopology F)
    {X : Type*} [AddCommGroup X] [Module F X] [FiniteDimensional F X] [TopologicalSpace X]
    [IsModuleTopology F X] [MeasurableSpace X] [BorelSpace X] [IsTopologicalAddGroup X]
    [LocallyCompactSpace X] (L : X ≃ₗ[F] X) (H : X ≃ₜ+ X) (hH : ∀ x, H x = L x) :
    addEquivAddHaarChar H = IndefiniteRowSideFullHecke.WmSys.absF (LinearMap.det (L : X →ₗ[F] X)) := by
  let : MeasurableSpace F := borel F
  have : BorelSpace F := ⟨rfl⟩
  have := locField_sigmaCompactSpace hF
  have := locField_secondCountable hF
  have := IsModuleTopology.toContinuousAdd F X
  let b₀ : X ≃ₗ[F] (Fin (Module.finrank F X) → F) := (Module.finBasis F X).equivFun
  let b : X ≃ₜ+ (Fin (Module.finrank F X) → F) :=
    { b₀.toAddEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap b₀.toLinearMap
      continuous_invFun := b₀.symm.toLinearMap.continuous_on_pi }
  let L' : (Fin (Module.finrank F X) → F) ≃ₗ[F] (Fin (Module.finrank F X) → F) :=
    b₀.symm.trans (L.trans b₀)
  have hconj : (b.symm.trans H).trans b = piHomeo L' := ContinuousAddEquiv.ext fun y => by
    change b₀ (H (b₀.symm y)) = b₀ (L (b₀.symm y))
    rw [hH]
  have hdet : LinearMap.det (L' : (Fin (Module.finrank F X) → F) →ₗ[F] _) =
      LinearMap.det (L : X →ₗ[F] X) := LinearMap.det_conj (L : X →ₗ[F] X) b₀
  rw [← addEquivAddHaarChar_conj b H, hconj, ← hdet]
  exact piChar_eq L'

end WmSysEquiv

end GroundTheory.Heights₂.Theta
