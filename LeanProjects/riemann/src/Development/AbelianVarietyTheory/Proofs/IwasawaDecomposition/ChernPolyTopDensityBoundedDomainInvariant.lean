import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Formalism.DegreeFormula.Statement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingCompEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopChernDensityInvariantHolomorphicFrameChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityCompHolomorphicNormSqDet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAndFderivMoebI
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMoebZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRestrictScalarsMatrixLeftRightMulAdeleTens
open Formalism.DegreeFormula

open Matrix Formalism.MJ Formalism.UG GlobalTheory.HodgeDomain GlobalTheory.HermFrame GlobalTheory.TrueCx
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.DomDensInv

variable {ι : Type} [Fintype ι] {p q n : ℕ}

theorem unflat_zero : unflat (0 : ι × Fin p × Fin q → ℂ) = 0 := by
  funext i; ext a b; rfl

theorem exists_upqI {z : ι → Matrix (Fin p) (Fin q) ℂ} (hz : z ∈ DomI ι p q) :
    ∃ g ∈ UpqI ι p q, moebI g 0 = z := by
  have : ∀ τ, ∃ g : GL (Fin p ⊕ Fin q) ℂ, g ∈ Upq p q ∧ moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) 0 = z τ := by
    intro τ
    obtain ⟨g, hg, hgz⟩ := GlobalTheory.TrueCx.FrameOnto.exists_moeb_zero (hz τ)
    have hd : g.det ≠ 0 := by
      intro h0
      have h1 := congrArg det hg
      have h2 := congrArg det (Jpq_sq (p := p) (q := q))
      rw [det_mul, h0, mul_zero] at h1
      rw [det_mul, ← h1] at h2
      simp at h2
    exact ⟨GeneralLinearGroup.mkOfDetNeZero _ hd, upq_iff.2 hg, hgz⟩
  choose g hg hgz using this
  exact ⟨g, fun τ _ => hg τ, funext fun τ => hgz τ⟩

theorem normSq_det_jW {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) :
    Complex.normSq (jW g 0).det = ((hQ (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) 0)).det).re := by
  have h := hP_moeb hg (zero_mem_hcDom p q)
  have e0 : hP (0 : Matrix (Fin p) (Fin q) ℂ) = 1 := by simp [hP]
  rw [e0, Matrix.mul_one] at h
  have h2 := congrArg Matrix.det h
  rw [det_mul, det_conjTranspose, hP, det_one_sub_mul_comm] at h2
  rw [hQ, ← h2, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

theorem normSq_det_kapQ_inv {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) :
    Complex.normSq ((kapQ g 0)⁻¹).det = ((hQ (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) 0)).det).re := by
  have h := hQ_moeb hg (zero_mem_hcDom p q)
  have e0 : hQ (0 : Matrix (Fin p) (Fin q) ℂ) = 1 := by simp [hQ]
  rw [e0] at h
  have h2 := congrArg Matrix.det h
  rw [det_mul, det_mul, det_conjTranspose, det_one] at h2
  set d := (kapQ g 0).det
  set H := (hQ (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) 0)).det
  have h3 : H * ((Complex.normSq d : ℝ) : ℂ) = 1 := by
    rw [← Complex.mul_conj, ← h2, Complex.star_def]; ring
  have h4 : H = ((Complex.normSq d : ℝ) : ℂ)⁻¹ := eq_inv_of_mul_eq_one_left h3
  rw [det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀, h4, ← Complex.ofReal_inv, Complex.ofReal_re]

end GlobalTheory.DomDensInv

namespace GlobalTheory.DomDensInv

variable {ι : Type} [Fintype ι] {p q n : ℕ}

theorem det_flat_mul (A : ι → Matrix (Fin p) (Fin p) ℂ) (B : ι → Matrix (Fin q) (Fin q) ℂ)
    (L : (ι × Fin p × Fin q → ℂ) →ₗ[ℂ] (ι × Fin p × Fin q → ℂ))
    (hL : ∀ x, L x = flat (fun τ => A τ * unflat x τ * B τ)) :
    LinearMap.det L = ∏ τ, (A τ).det ^ q * (B τ).det ^ p := by
  let E : (ι × Fin p × Fin q → ℂ) ≃ₗ[ℂ] (ι → Matrix (Fin p) (Fin q) ℂ) :=
    { toFun := unflat, invFun := flat, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have key : (E : (ι × Fin p × Fin q → ℂ) →ₗ[ℂ] (ι → Matrix (Fin p) (Fin q) ℂ)) ∘ₗ L ∘ₗ
      (E.symm : (ι → Matrix (Fin p) (Fin q) ℂ) →ₗ[ℂ] (ι × Fin p × Fin q → ℂ)) =
      LinearMap.pi fun τ => (GlobalTheory.ModuLR.lrLin (A τ) (B τ)).comp (LinearMap.proj τ) := by
    refine LinearMap.ext fun x => funext fun τ => ?_
    change unflat (L (flat x)) τ = A τ * x τ * B τ
    rw [hL]; rfl
  rw [← LinearMap.det_conj L E, key, LinearMap.det_pi]
  simp only [GlobalTheory.ModuLR.det_lrLin, Fintype.card_fin]

theorem model_smooth (h : Fintype.card (ι × Fin p × Fin q) = n) {u : ReciprocityTheory.L2DbarEstimates.V n}
    (hu : GlobalTheory.UnifDens.flatL h u ∈ DomFlat ι p q) (τ : ι) :
    MContDiffAt 2 (fun w : ReciprocityTheory.L2DbarEstimates.V n => ((hP (unflat (GlobalTheory.UnifDens.flatL h w) τ))⁻¹)ᵀ) u ∧
      IsUnit (((hP (unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹)ᵀ).det := by
  have hp := hP_posDef (hu τ)
  have hunit : IsUnit (hP (unflat (GlobalTheory.UnifDens.flatL h u) τ)).det := hp.det_pos.ne'.isUnit
  refine ⟨MContDiffAt.transpose (MContDiffAt.inv ?_ hunit), ?_⟩
  · have hY : MContDiffAt 2 (fun w : ReciprocityTheory.L2DbarEstimates.V n => unflat (GlobalTheory.UnifDens.flatL h w) τ) u := by
      intro a b
      have e : (fun w : ReciprocityTheory.L2DbarEstimates.V n => unflat (GlobalTheory.UnifDens.flatL h w) τ a b) =
          fun w => (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι × Fin p × Fin q => ℂ) (τ, a, b)).comp
            (GlobalTheory.UnifDens.flatL h : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (ι × Fin p × Fin q → ℂ))).restrictScalars ℝ) w := rfl
      rw [e]; exact (ContinuousLinearMap.contDiff _).contDiffAt
    exact (mContDiffAt_const 1).sub (hY.mul hY.conjTranspose)
  · rw [det_transpose]; exact isUnit_nonsing_inv_det _ hunit

theorem gram_transpose_of_congr {J Hg Hy : Matrix (Fin p) (Fin p) ℂ} (hJ : IsUnit J.det) (h : Jᴴ * Hg * J = Hy) :
    Hgᵀ = (J⁻¹)ᵀ * Hyᵀ * ((J⁻¹)ᵀ)ᴴ := by
  have hJ' : IsUnit Jᴴ.det := by rw [det_conjTranspose]; exact hJ.star
  have h1 : Hg = (J⁻¹)ᴴ * Hy * J⁻¹ := by
    rw [← h, conjTranspose_nonsing_inv]
    simp only [← Matrix.mul_assoc, nonsing_inv_mul _ hJ', Matrix.one_mul]
    rw [Matrix.mul_assoc, mul_nonsing_inv _ hJ, Matrix.mul_one]
  rw [h1, transpose_mul, transpose_mul]
  have e : ((J⁻¹)ᴴ)ᵀ = ((J⁻¹)ᵀ)ᴴ := by ext i j; rfl
  rw [e, Matrix.mul_assoc]

theorem chernTop_model_moeb : ∀ (ι : Type) [Fintype ι] (p q n : ℕ) (h : Fintype.card (ι × Fin p × Fin q) = n) (v : ReciprocityTheory.L2DbarEstimates.V n), GlobalTheory.UnifDens.flatL h v ∈ Formalism.DegreeFormula.DomFlat ι p q → GlobalTheory.GoodMetric.chernTop (m := fun _ : ι => p) (∏ τ : ι, (MvPolynomial.C ((-1 : ℝ) ^ p) * MvPolynomial.X (τ, p)) ^ q) (fun u τ => Matrix.transpose (hP (unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) v = GlobalTheory.GoodMetric.chernTop (m := fun _ : ι => p) (∏ τ : ι, (MvPolynomial.C ((-1 : ℝ) ^ p) * MvPolynomial.X (τ, p)) ^ q) (fun u τ => Matrix.transpose (hP (unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) 0 * ∏ i, ((Formalism.DegreeFormula.hQ (Formalism.DegreeFormula.unflat (GlobalTheory.UnifDens.flatL h v) i)).det.re) ^ (-((p + q : ℕ) : ℤ)) := by
  intro ι _ p q n h v hv
  classical
  set e := GlobalTheory.UnifDens.flatL h with he
  set K : ReciprocityTheory.L2DbarEstimates.V n → ι → Matrix (Fin p) (Fin p) ℂ := fun u τ => ((hP (unflat (e u) τ))⁻¹)ᵀ with hK
  set R : MvPolynomial (ι × ℕ) ℝ := ∏ τ : ι, (MvPolynomial.C ((-1 : ℝ) ^ p) * MvPolynomial.X (τ, p)) ^ q with hR
  set z := unflat (e v) with hz
  have hzD : z ∈ DomI ι p q := hv
  obtain ⟨g, hg, hgz⟩ := exists_upqI hzD
  set Φ : (ι × Fin p × Fin q → ℂ) → (ι × Fin p × Fin q → ℂ) := fun w => flat (moebI g (unflat w)) with hΦ
  set φ : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.L2DbarEstimates.V n := fun u => e.symm (Φ (e u)) with hφ
  have h0D : (0 : ι × Fin p × Fin q → ℂ) ∈ DomFlat ι p q := by
    intro τ; rw [unflat_zero]; exact zero_mem_hcDom p q
  have he0 : e 0 = 0 := map_zero e
  have hφ0 : φ 0 = v := by
    show e.symm (flat (moebI g (unflat (e 0)))) = v
    rw [he0, unflat_zero, hgz]
    exact e.symm_apply_apply v
  obtain ⟨ho, H⟩ := GlobalTheory.HodgeDomain.ActionDeriv.isOpen_and_fderiv_moebI ι p q
  obtain ⟨hd, hD⟩ := H g hg
  have hΦan : AnalyticAt ℂ Φ 0 := GlobalTheory.SCV.analyticOnNhd_of_differentiableOn ho hd 0 h0D
  have hΦan' : AnalyticAt ℂ Φ (e 0) := by rw [he0]; exact hΦan
  have hφan : AnalyticAt ℂ φ 0 :=
    (e.symm : (ι × Fin p × Fin q → ℂ) →L[ℂ] ReciprocityTheory.L2DbarEstimates.V n).analyticAt _ |>.comp
      (hΦan'.comp ((e : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (ι × Fin p × Fin q → ℂ)).analyticAt 0))
  have hKv := fun τ => model_smooth h (u := v) hv τ
  have h0S : e 0 ∈ DomFlat ι p q := by rw [he0]; exact h0D
  have hK0 := fun τ => model_smooth h (u := 0) h0S τ

  have hA := GlobalTheory.ChernPull.chernTop_comp R K φ 0 hφan (by rw [hφ0]; exact fun τ => (hKv τ).1)
    (by rw [hφ0]; exact fun τ => (hKv τ).2)
  rw [hφ0] at hA

  set S : Set (ReciprocityTheory.L2DbarEstimates.V n) := e ⁻¹' DomFlat ι p q with hS
  have hSo : IsOpen S := ho.preimage e.continuous
  have h0S' : (0 : ReciprocityTheory.L2DbarEstimates.V n) ∈ S := h0S
  set g' : ReciprocityTheory.L2DbarEstimates.V n → ι → Matrix (Fin p) (Fin p) ℂ :=
    fun w τ => ((jW (g τ) (unflat (e w) τ))⁻¹)ᵀ with hg'
  have hΦcd : ContDiffOn ℂ 1 Φ (DomFlat ι p q) :=
    (GlobalTheory.SCV.analyticOnNhd_of_differentiableOn ho hd).contDiffOn ho.uniqueDiffOn
  have hΨ : ContDiffOn ℂ 1 (fun w => Φ (e w)) S :=
    hΦcd.comp (e : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (ι × Fin p × Fin q → ℂ)).contDiff.contDiffOn fun w hw => hw
  have hg'an : ∀ τ i j, AnalyticAt ℂ (fun w => g' w τ i j) 0 := by
    intro τ i j
    have hent : ∀ a b, ContDiffOn ℂ 1 (fun w => jW (g τ) (unflat (e w) τ) a b) S := by
      intro a b
      have ee : (fun w => jW (g τ) (unflat (e w) τ) a b) = fun w =>
          (g τ).1.toBlocks₁₁ a b - ∑ k, Φ (e w) (τ, a, k) * (g τ).1.toBlocks₂₁ k b := by
        funext w; simp only [jW, Matrix.sub_apply, Matrix.mul_apply]; rfl
      rw [ee]
      exact contDiffOn_const.sub (ContDiffOn.sum fun k _ => ((contDiffOn_pi.1 hΨ) (τ, a, k)).mul contDiffOn_const)
    have hinv := GlobalTheory.HodgeDomain.ActionDeriv.diffOn_inv (s := S) (M := fun w => jW (g τ) (unflat (e w) τ)) hent
      (fun w hw => (jW_isUnit (hg τ (Set.mem_univ _)) (hw τ)).ne_zero) j i
    exact GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hSo (hinv.differentiableOn one_ne_zero) 0 h0S'
  have hg'u : ∀ τ, IsUnit (g' 0 τ).det := by
    intro τ
    rw [hg', det_transpose]
    exact isUnit_nonsing_inv_det _ (jW_isUnit (hg τ (Set.mem_univ _)) (h0S τ))
  have hev : ∀ᶠ w in nhds (0 : ReciprocityTheory.L2DbarEstimates.V n), ∀ τ, K (φ w) τ =
      (((fun _ : ι => (1 : ℝ)) τ : ℝ) : ℂ) • (g' w τ * K w τ * (g' w τ)ᴴ) := by
    filter_upwards [hSo.mem_nhds h0S'] with w hw τ
    have hy : unflat (e w) τ ∈ hcDom p q := hw τ
    have hgt := hg τ (Set.mem_univ _)
    have key := gram_transpose_of_congr (jW_isUnit hgt hy) (hP_inv_moeb hgt hy)
    have e1 : K (φ w) τ = ((hP (moeb ((g τ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (unflat (e w) τ)))⁻¹)ᵀ := by
      show ((hP (unflat (e (e.symm (Φ (e w)))) τ))⁻¹)ᵀ = _
      rw [e.apply_symm_apply]; rfl
    rw [e1, key, Complex.ofReal_one, one_smul]
  have hB := GlobalTheory.PointChern.chernTop_changeFrame R (fun w => K (φ w)) K g' (fun _ => (1 : ℝ)) 0
    (fun _ => one_pos) hg'an hg'u (fun τ => (hK0 τ).1) (fun τ => (hK0 τ).2) hev

  have hΦd : HasFDerivAt Φ (fderiv ℂ Φ 0) (e 0) := by rw [he0]; exact hΦan.differentiableAt.hasFDerivAt
  have hφd : HasFDerivAt φ ((e.symm : (ι × Fin p × Fin q → ℂ) →L[ℂ] ReciprocityTheory.L2DbarEstimates.V n).comp
      ((fderiv ℂ Φ 0).comp (e : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (ι × Fin p × Fin q → ℂ)))) 0 :=
    e.symm.hasFDerivAt.comp 0 (hΦd.comp 0 e.hasFDerivAt)
  have hdetF : LinearMap.det (fderiv ℂ Φ 0 : (ι × Fin p × Fin q → ℂ) →ₗ[ℂ] (ι × Fin p × Fin q → ℂ)) =
      ∏ τ, (jW (g τ) 0).det ^ q * ((kapQ (g τ) 0)⁻¹).det ^ p := by
    refine det_flat_mul _ _ _ fun x => ?_
    have := hD 0 (fun τ => zero_mem_hcDom p q) (unflat x)
    exact this
  have hdet : LinearMap.det (fderiv ℂ φ 0 : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] ReciprocityTheory.L2DbarEstimates.V n) =
      ∏ τ, (jW (g τ) 0).det ^ q * ((kapQ (g τ) 0)⁻¹).det ^ p := by
    rw [hφd.fderiv, ← hdetF, ← LinearMap.det_conj (fderiv ℂ Φ 0 : (ι × Fin p × Fin q → ℂ) →ₗ[ℂ] (ι × Fin p × Fin q → ℂ))
      e.symm.toLinearEquiv]
    rfl
  have hx : ∀ τ, Complex.normSq (jW (g τ) 0).det = ((hQ (z τ)).det).re ∧
      Complex.normSq ((kapQ (g τ) 0)⁻¹).det = ((hQ (z τ)).det).re := by
    intro τ
    have hgt := hg τ (Set.mem_univ _)
    have hzτ : moeb ((g τ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) 0 = z τ := congrFun hgz τ
    rw [← hzτ]
    exact ⟨normSq_det_jW hgt, normSq_det_kapQ_inv hgt⟩
  have hN : Complex.normSq (LinearMap.det (fderiv ℂ φ 0 : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] ReciprocityTheory.L2DbarEstimates.V n)) =
      ∏ τ, ((hQ (z τ)).det).re ^ (p + q) := by
    rw [hdet, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_mul, map_pow, map_pow, (hx τ).1, (hx τ).2, pow_add, mul_comm]
  have hpos : ∀ τ, 0 < ((hQ (z τ)).det).re := fun τ =>
    (Complex.pos_iff.1 (show (hQ (z τ)).PosDef from hzD τ).det_pos).1
  have hNpos : 0 < ∏ τ, ((hQ (z τ)).det).re ^ (p + q) := Finset.prod_pos fun τ _ => pow_pos (hpos τ) _
  rw [hB, hN] at hA
  have e2 : ∏ τ, ((hQ (z τ)).det).re ^ (-((p + q : ℕ) : ℤ)) = (∏ τ, ((hQ (z τ)).det).re ^ (p + q))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [_root_.zpow_neg, zpow_natCast]
  show GlobalTheory.GoodMetric.chernTop R K v = GlobalTheory.GoodMetric.chernTop R K 0 * ∏ τ, ((hQ (z τ)).det).re ^ (-((p + q : ℕ) : ℤ))
  rw [e2, hA]
  field_simp

end GlobalTheory.DomDensInv
