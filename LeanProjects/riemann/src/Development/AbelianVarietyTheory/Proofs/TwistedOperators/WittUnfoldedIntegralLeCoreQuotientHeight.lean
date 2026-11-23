import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedBesselJacobiIntegralAbsLe
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationRationalTranslateSubstitution
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelFormulasWittSourceProof
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumDescendsToWittCoreOfExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OfRealQuotHeightPow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightOrthogonalEmbeddingLePow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapHandedFunctionVanishingPeriodInvariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionInvariantRationalLeviGL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapIntegrableAndBoundedLinearForm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.QuotUnfBound

variable {D : D7}

theorem unitaryAdelicHeight_wittEmbedding_le {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ g : GA D V₀, height V (d.emb0 g) ≤ C * height V₀ g := by
  obtain ⟨C, hC⟩ := GlobalTheory.EmbHeight.exists_heightGL_le D.host.F d.j0 d.p0 (d.jX ⬝ d.pX + d.jY ⬝ d.pY)
  refine ⟨max (C : ℝ) 1, le_max_right _ _, fun g => ?_⟩
  have h := hC (Formalism.L2.Theta.matHom V (d.emb0 g)) (Formalism.L2.Theta.matHom V₀ g) (by
      show Formalism.L2.Theta.mt V (d.emb0 g) = d.j0 ⬝ Formalism.L2.Theta.mt V₀ g ⬝ d.p0 + (d.jX ⬝ d.pX + d.jY ⬝ d.pY)
      rw [GlobalTheory.FlatRInv.unitaryMatrix_wittCoreEmbedding]; abel) (by
      rw [← map_inv, ← map_inv, ← map_inv]
      show Formalism.L2.Theta.mt V (d.emb0 g⁻¹) = d.j0 ⬝ Formalism.L2.Theta.mt V₀ g⁻¹ ⬝ d.p0 + (d.jX ⬝ d.pX + d.jY ⬝ d.pY)
      rw [GlobalTheory.FlatRInv.unitaryMatrix_wittCoreEmbedding]; abel)
  have h' : height V (d.emb0 g) ≤ (C : ℝ) * height V₀ g := by
    unfold GlobalTheory.Grow.height; exact_mod_cast h
  exact h'.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (height_pos V₀ g).le)

theorem covolOne_lintegral_mul_right {m n : ℕ} {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)}
    (hμ : IsCovolOne (ratMx D m n) μ 𝓕) (M M' : Mx D n n) (hM'M : M' ⬝ M = 1) (hMM' : M ⬝ M' = 1)
    (hM : M ∈ ratMx D n n) (hM' : M' ∈ ratMx D n n) (φ : Mx D m n → ℝ≥0∞)
    (hφ : ∀ γ ∈ ratMx D m n, ∀ a, φ (γ + a) = φ a) :
    ∫⁻ a in 𝓕, φ (a ⬝ M) ∂μ = ∫⁻ a in 𝓕, φ a ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI : Countable (ratMx D m n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  let e : Mx D m n ≃+ Mx D m n :=
    { toFun := fun a => a ⬝ M
      invFun := fun a => a ⬝ M'
      left_inv := fun a => by simp only [Matrix.mul_assoc, hMM', Matrix.mul_one]
      right_inv := fun a => by simp only [Matrix.mul_assoc, hM'M, Matrix.mul_one]
      map_add' := fun a b => Matrix.add_mul _ _ _ }
  have he : Continuous e := continuous_id.matrix_mul continuous_const
  have he' : Continuous e.symm := continuous_id.matrix_mul continuous_const
  have hr : ∀ x, e x ∈ ratMx D m n ↔ x ∈ ratMx D m n := fun x =>
    ⟨fun h => by
      have h2 := GlobalTheory.MixModel.ratMx_mul h hM'
      have h3 : e x ⬝ M' = x := e.symm_apply_apply x
      rwa [h3] at h2,
     fun h => GlobalTheory.MixModel.ratMx_mul h hM⟩
  obtain ⟨h1, hemb⟩ := GlobalTheory.Unf.ParCont.isCovolOne_map hμ e he he' hr
  have hmeq : Measure.map e μ = μ := GlobalTheory.MixModel.covolOne_measure_eq hμ h1
  haveI := hμ.1
  have h1' := h1
  rw [hmeq] at h1'
  have hfd : ∫⁻ a in e '' 𝓕, φ a ∂μ = ∫⁻ a in 𝓕, φ a ∂μ :=
    h1'.2.1.setLIntegral_eq hμ.2.1 φ fun γ a => hφ γ γ.2 a
  have hmap : ∫⁻ a in e '' 𝓕, φ a ∂(Measure.map e μ) = ∫⁻ a in 𝓕, φ (e a) ∂μ := by
    rw [hemb.restrict_map, hemb.lintegral_map, Set.preimage_image_eq _ e.injective]
  calc ∫⁻ a in 𝓕, φ (a ⬝ M) ∂μ = ∫⁻ a in 𝓕, φ (e a) ∂μ := rfl
    _ = ∫⁻ a in e '' 𝓕, φ a ∂(Measure.map e μ) := hmap.symm
    _ = ∫⁻ a in e '' 𝓕, φ a ∂μ := by rw [hmeq]
    _ = ∫⁻ a in 𝓕, φ a ∂μ := hfd

theorem enorm_periodic {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V₀ W : HSp D} {ρ : ℕ}
    {F : WO V₀ W → ℂ} (hF : IsThetaFunO ψ V₀ W F) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) :
    ∀ β ∈ ratMx D ρ V₀.rank, ∀ b, ‖F (rat x₀ ⬝ (β + b))‖ₑ = ‖F (rat x₀ ⬝ b)‖ₑ := by
  rintro _ ⟨β, rfl⟩ b
  show ‖F (rat x₀ ⬝ (rat β + b))‖ₑ = ‖F (rat x₀ ⬝ b)‖ₑ
  have e1 : rat x₀ ⬝ (rat β + b) = Formalism.L2.Theta.ratW W V₀ (x₀ ⬝ β) + rat x₀ ⬝ b := by
    rw [Matrix.mul_add]
    congr 1
    show (x₀.map (incA D)) ⬝ (β.map (incA D)) = (x₀ ⬝ β).map (incA D)
    rw [Matrix.map_mul]
  rw [e1, hF.quasi, enorm_mul, GlobalTheory.Unf.FlatForm.enorm_psi hψ, one_mul]

theorem inner_inv {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ)
    {χV χW : (AE D)ˣ →* Circle} {om : Om V W} {om' : Om V₀ W} (hW : IsWeilDatumO ψ V W χV χW om)
    (hW' : IsWeilDatumO ψ V₀ W χV χW om') (vS : VolM D W.rank ρ) (vb : VolM D ρ V₀.rank)
    (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) {Ψ : WO V W → ℂ} (hΨ : IsThetaFunO ψ V W Ψ) {γ : GA D V₀}
    (hγ : γ ∈ GQ V₀) (x : Mx D W.rank ρ) :
    ∫⁻ b in vb.𝓕, ‖d.mixS W ψ vS.μ vS.𝓕 (om (d.emb0 γ, 1) Ψ) x (rat x₀ ⬝ b)‖ₑ ∂vb.μ =
      ∫⁻ b in vb.𝓕, ‖d.mixS W ψ vS.μ vS.𝓕 Ψ x (rat x₀ ⬝ b)‖ₑ ∂vb.μ := by
  set F := d.mixS W ψ vS.μ vS.𝓕 Ψ x with hFdef
  have hF : IsThetaFunO ψ V₀ W F := GlobalTheory.MixValues.mixS_theta D ψ hW.std V V₀ W ρ d vS.μ vS.𝓕 vS.covol Ψ hΨ x
  have hcore := (GlobalTheory.MixSourceFormulas.mixed_source D ψ V V₀ W ρ d χV χW om om' hW hW' vS.μ vS.𝓕 vS.covol Ψ hΨ).core γ x
  have hsub : ∀ w, d.mixS W ψ vS.μ vS.𝓕 (om (d.emb0 γ, 1) Ψ) x w = F (w ⬝ Formalism.L2.Theta.mt V₀ γ) := by
    intro w
    rw [hcore]
    have h := GlobalTheory.Unf.om_rat_mul D ψ V₀ W χV χW om' hW' F hF γ hγ 1 (one_mem _) 1 1 w
    rw [mul_one, mul_one, inv_one, show ((1 : GA D V₀), (1 : GA D W)) = 1 from rfl, map_one] at h
    rw [h]
    simp [Formalism.L2.Theta.mt]
  have hM := (GlobalTheory.MixModel.mem_GQ_iff V₀ γ).1 hγ
  have hM' := (GlobalTheory.MixModel.mem_GQ_iff V₀ γ⁻¹).1 (inv_mem hγ)
  have h1 : Formalism.L2.Theta.mt V₀ γ⁻¹ ⬝ Formalism.L2.Theta.mt V₀ γ = 1 := by
    simp only [Formalism.L2.Theta.mt, map_inv]; exact Units.inv_mul _
  have h2 : Formalism.L2.Theta.mt V₀ γ ⬝ Formalism.L2.Theta.mt V₀ γ⁻¹ = 1 := by
    simp only [Formalism.L2.Theta.mt, map_inv]; exact Units.mul_inv _
  have hmul : ∀ b : Mx D ρ V₀.rank, rat x₀ ⬝ b ⬝ Formalism.L2.Theta.mt V₀ γ = rat x₀ ⬝ (b ⬝ Formalism.L2.Theta.mt V₀ γ) :=
    fun b => Matrix.mul_assoc _ _ _
  simp_rw [hsub, hmul]
  exact covolOne_lintegral_mul_right vb.covol (Formalism.L2.Theta.mt V₀ γ) (Formalism.L2.Theta.mt V₀ γ⁻¹) h1 h2 hM hM'
    (fun b => ‖F (rat x₀ ⬝ b)‖ₑ) (enorm_periodic hW.std hF x₀)

theorem unfolded_rat_inv {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ)
    {χV χW : (AE D)ˣ →* Circle} {om : Om V W} {om' : Om V₀ W} (hW : IsWeilDatumO ψ V W χV χW om)
    (hW' : IsWeilDatumO ψ V₀ W χV χW om') (vS : VolM D W.rank ρ) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ)
    (vW : GlobalTheory.Unf.Vol W) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (G : GA D W → ℂ) {Φ : WO V W → ℂ}
    (hΦ : IsThetaFunO ψ V W Φ) (𝓑 : Set (GA D W)) {γ : GA D V₀} (hγ : γ ∈ GQ V₀) (g : GA D V₀) :
    ∫⁻ h in 𝓑, ‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕,
        ‖d.mixS W ψ vS.μ vS.𝓕 (om (d.emb0 (γ * g), h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ ∂vb.μ ∂vU.ν ∂vW.μ =
      ∫⁻ h in 𝓑, ‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕,
        ‖d.mixS W ψ vS.μ vS.𝓕 (om (d.emb0 g, h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ ∂vb.μ ∂vU.ν ∂vW.μ := by
  refine lintegral_congr fun h => ?_
  congr 1
  refine lintegral_congr fun u => ?_
  have e : om (d.emb0 (γ * g), h) Φ = om (d.emb0 γ, 1) (om (d.emb0 g, h) Φ) := by
    rw [map_mul, show ((d.emb0 γ * d.emb0 g, h) : GA D V × GA D W) = (d.emb0 γ, 1) * (d.emb0 g, h) by
      simp [Prod.mk_mul_mk], map_mul]
    rfl
  rw [e]
  exact inner_inv d hW hW' vS vb x₀ (hW.om_pres _ Φ hΦ) hγ _

end GlobalTheory.QuotUnfBound

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.QuotUnfBound.unfolded_integral_le_quotHeight : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W), IsWeilDatumO ψ V W χV χW om → ∀ (vS : VolM D W.rank ρ) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (vW : GlobalTheory.Unf.Vol W) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), IsBase W x₀ → ∀ (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ 𝓑 : Set (GA D W), IsFundamentalDomain (GQ W ⊓ Rgrp W (rat x₀) : Subgroup (GA D W)) 𝓑 vW.μ → ∃ (C : ℝ) (A : ℕ), ∀ g : GA D V₀, ∫⁻ h in 𝓑, ‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕, ‖d.mixS W ψ vS.μ vS.𝓕 (om (d.emb0 g, h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ ∂vb.μ ∂vU.ν ∂vW.μ ≤ ENNReal.ofReal (C * quotHeight V₀ g ^ A) := by
  intro D ψ V V₀ W ρ d χV χW om hW vS vb vU vW x₀ hx G Φ hG hΦ 𝓑 h𝓑
  obtain ⟨om', hW'⟩ :=
    ((GlobalTheory.Unf.descent_of_weilDatumExists D (GlobalTheory.WeilDatumExistence.weilDatumExists D)) ψ V W χV χW om hW).1 V₀ ρ d
  obtain ⟨C, A, hC⟩ := GlobalTheory.Unf.UnfoldBound.unfolded_integral_le D ψ V V₀ W ρ d χV χW om om' hW hW' vS vb vU vW x₀ hx G Φ hG hΦ 𝓑 h𝓑
  obtain ⟨C₁, hC₁1, hC₁⟩ := GlobalTheory.QuotUnfBound.unitaryAdelicHeight_wittEmbedding_le d
  have hM : (0 : ℝ) < max C 1 := lt_max_of_lt_right one_pos
  have hKpos : (0 : ℝ) < max C 1 * C₁ ^ A := mul_pos hM (pow_pos (one_pos.trans_le hC₁1) A)
  refine ⟨max C 1 * C₁ ^ A, A, fun g => ?_⟩
  have hb : ∀ k : GA D V₀, ∫⁻ h in 𝓑, ‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕,
        ‖d.mixS W ψ vS.μ vS.𝓕 (om (d.emb0 k, h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ ∂vb.μ ∂vU.ν ∂vW.μ ≤
        ENNReal.ofReal (max C 1 * C₁ ^ A) * ENNReal.ofReal (height V₀ k ^ A) := by
    intro k
    rw [← ENNReal.ofReal_mul hKpos.le]
    refine (hC (d.emb0 k)).trans (ENNReal.ofReal_le_ofReal ?_)
    have h0 : 0 ≤ height V (d.emb0 k) := (height_pos V _).le
    have h1 : height V (d.emb0 k) ^ A ≤ (C₁ * height V₀ k) ^ A := pow_le_pow_left₀ h0 (hC₁ k) A
    calc C * height V (d.emb0 k) ^ A ≤ max C 1 * height V (d.emb0 k) ^ A :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg h0 A)
      _ ≤ max C 1 * (C₁ * height V₀ k) ^ A := mul_le_mul_of_nonneg_left h1 hM.le
      _ = max C 1 * C₁ ^ A * height V₀ k ^ A := by rw [mul_pow, mul_assoc]
  have hle : ∀ γ : GQ V₀, ∫⁻ h in 𝓑, ‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕,
        ‖d.mixS W ψ vS.μ vS.𝓕 (om (d.emb0 g, h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ ∂vb.μ ∂vU.ν ∂vW.μ ≤
        ENNReal.ofReal (max C 1 * C₁ ^ A) * ENNReal.ofReal (height V₀ ((γ : GA D V₀) * g) ^ A) := by
    intro γ
    rw [← GlobalTheory.QuotUnfBound.unfolded_rat_inv d hW hW' vS vb vU vW x₀ G hΦ 𝓑 γ.2 g]
    exact hb _
  rw [ENNReal.ofReal_mul hKpos.le, GlobalTheory.MixSumBound.ofReal_quotHeight_pow,
    ENNReal.mul_iInf_of_ne (by simpa using hKpos) ENNReal.ofReal_ne_top]
  exact le_iInf hle

end
