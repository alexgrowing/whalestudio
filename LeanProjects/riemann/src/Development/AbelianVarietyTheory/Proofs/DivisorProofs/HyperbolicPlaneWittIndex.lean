import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConstAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsParDec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BruhatUnipotentLeviDecomp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerRestrictsToOrthocomp
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.ThK.InducedCons.ParDec

open Matrix GlobalTheory.PlaneProj GlobalTheory.IsoPlaneProj GlobalTheory.IwaIsoPlane

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_levi_proj (hσ : IsCMExt F E σ) {n n₁ : ℕ} (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁)
    (hskew : ∀ i j, σ (Y.J j i) = -Y.J i j) (hn : n = n₁ + 2) (hxx : form σ Y.J H.x H.x = 0)
    (hyy : form σ Y.J H.y H.y = 0) (hxy : form σ Y.J H.x H.y = 1)
    (horth : ∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0)
    (hgram : H.ιᵀ * Y.J * H.ι.map σ = Y₁.J) (hd : Y₁.J.det ≠ 0) (p : UA σ Y.J)
    (hp : mat p *ᵥ incV F H.x = incV F H.x) : ∃ h₁ : UA σ Y₁.J,
      ∀ z : Fin n₁ → AE F E, ∃ a : AE F E, mat p *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (mat h₁ *ᵥ z) + a • incV F H.x := by
  have hinv := GlobalTheory.LeviIdeleHom.sigma_sigma hσ
  have hJ₁ : IsUnit Y₁.J.det := isUnit_iff_ne_zero.2 hd
  obtain ⟨π, hfr⟩ := frame_of_gram hinv hskew hn hxx hyy hxy horth hgram hJ₁
  have hsk := GlobalTheory.PlaneFrame.form_skew hσ hskew
  set c : AE F E →+* AE F E := ((cA σ : AE F E →ₐ[AF F] AE F E) : AE F E →+* AE F E) with hc
  have eιx : (H.ιᵀ * Y.J) *ᵥ (⇑σ ∘ H.x) = 0 := by
    funext j
    have h0 := (horth (Pi.single j 1)).1
    rw [form, dotProduct_comm, dotProduct_mulVec, dotProduct_single_one] at h0
    rw [Pi.zero_apply, ← h0, ← mulVec_mulVec, mulVec_transpose]; rfl
  have exι : H.x ᵥ* (Y.J * H.ι.map σ) = 0 := by
    funext j
    have h0 : form σ Y.J H.x (H.ι *ᵥ Pi.single j 1) = 0 := by
      rw [hsk, (horth _).1, map_zero, neg_zero]
    rw [Pi.zero_apply, ← h0, form, ← dotProduct_single_one (H.x ᵥ* _) j, ← dotProduct_mulVec, ← mulVec_mulVec]
    congr 2
    funext i; simp [mulVec, dotProduct, Pi.single_apply]
  have hframe : vecMulVec (incV F H.x) (incM F Y.J *ᵥ (c ∘ incV F H.y)) + incM F H.ι * incM F π -
      vecMulVec (incV F H.y) (incM F Y.J *ᵥ (c ∘ incV F H.x)) = 1 := by
    rw [cA_incV, cA_incV, incM_mulVec', incM_mulVec', incM_vmv, incM_vmv, incM_mul]
    have e1 : incM F (vecMulVec H.x (Y.J *ᵥ (⇑σ ∘ H.y))) + incM F (H.ι * π) - incM F (vecMulVec H.y (Y.J *ᵥ (⇑σ ∘ H.x))) =
        incM F (vecMulVec H.x (Y.J *ᵥ (⇑σ ∘ H.y)) + H.ι * π - vecMulVec H.y (Y.J *ᵥ (⇑σ ∘ H.x))) := by
      ext i j; simp only [incM, Matrix.map_apply, Matrix.add_apply, Matrix.sub_apply, map_add, map_sub]
    rw [e1, hfr]; ext i j; simp [incM, Matrix.one_apply]
  have hgram' : (incM F H.ι)ᵀ * incM F Y.J * (incM F H.ι).map c = incM F Y₁.J := by
    rw [incM_map, incM_transpose, incM_mul, incM_mul, hgram]
  have hιx : ((incM F H.ι)ᵀ * incM F Y.J) *ᵥ (c ∘ incV F H.x) = 0 := by
    rw [cA_incV, incM_transpose, incM_mul, incM_mulVec', eιx, incV_zero]
  have hxι : incV F H.x ᵥ* (incM F Y.J * (incM F H.ι).map c) = 0 := by
    rw [incM_map, incM_mul, incV_vecMul, exι, incV_zero]
  have hxx' : incV F H.x ⬝ᵥ (incM F Y.J *ᵥ (c ∘ incV F H.x)) = 0 := by
    rw [cA_incV, incM_mulVec', incV_dot]
    have : H.x ⬝ᵥ (Y.J *ᵥ (⇑σ ∘ H.x)) = 0 := hxx
    rw [this, map_zero]
  have hJ₁' : IsUnit (incM F Y₁.J).det := by
    rw [show incM F Y₁.J = (inclR (F := F) (AF F)).mapMatrix Y₁.J from rfl, ← RingHom.map_det]
    exact hJ₁.map _
  obtain ⟨hU, hdet, hz⟩ := proj_core c (mat p) (incM F Y.J) (incM F Y₁.J) (incM F H.ι) (incM F π) (incV F H.x) (incV F H.y)
    p.2 hp hframe hgram' hιx hxι hxx' hJ₁'
  exact ⟨⟨Matrix.GeneralLinearGroup.mk'' _ hdet, hU⟩, fun z => ⟨_, hz z⟩⟩

theorem exists_dec (hcm : IsCMExt F E σ) {n n₁ : ℕ} (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁)
    (hsk : ∀ i j, σ (Y.J j i) = -Y.J i j) (hn : n = n₁ + 2) (hxx : form σ Y.J H.x H.x = 0)
    (hyy : form σ Y.J H.y H.y = 0) (hxy : form σ Y.J H.x H.y = 1)
    (horth : ∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0)
    (hgram : H.ιᵀ * Y.J * H.ι.map σ = Y₁.J) (hd : Y₁.J.det ≠ 0) (Msec : UA σ Y₁.J → UA σ Y.J)
    (hMsec : ∀ h₁, IsLevi (W₁ := Y₁) H 1 h₁ (Msec h₁)) (p : UA σ Y.J) (t : (AE F E)ˣ)
    (ht : mat p *ᵥ incV F H.x = t.1 • incV F H.x) :
    ∃ n' ∈ unip σ Y H, ∃ m : UA σ Y.J, IsLevi (W₁ := Y₁) H t 1 m ∧ ∃ h₁ : UA σ Y₁.J, p = n' * m * Msec h₁ := by
  obtain ⟨m, hm⟩ := exists_isLevi_of_hyperbolic_pair hcm Y Y₁ H hsk hxx hyy hxy horth t
  have hmx : mat m⁻¹ *ᵥ incV F H.x = t⁻¹.1 • incV F H.x := by
    have := inv_mulVec_of' m t.1 t.isUnit _ _ hm.1
    simpa using this
  have hp1 : mat (m⁻¹ * p) *ᵥ incV F H.x = incV F H.x := by
    rw [mat_mul'', ← Matrix.mulVec_mulVec, ht, Matrix.mulVec_smul, hmx, smul_smul]; simp
  obtain ⟨h₁, hh₁⟩ := exists_levi_proj hcm Y Y₁ H hsk hn hxx hyy hxy horth hgram hd (m⁻¹ * p) hp1
  have hm₁ := hMsec h₁
  generalize hM : Msec h₁ = m₁ at hm₁
  have hm₁x : mat m₁⁻¹ *ᵥ incV F H.x = incV F H.x := by
    have := inv_mulVec_of' m₁ 1 isUnit_one _ _ (by simpa using hm₁.1)
    simpa using this
  have hmι : mat m * incM F H.ι = incM F H.ι := by rw [hm.2.2, mat_one'', Matrix.mul_one]
  have hmιinv : mat m⁻¹ * incM F H.ι = incM F H.ι := by
    conv_lhs => rw [← hmι, ← Matrix.mul_assoc, mat_inv_mul'', Matrix.one_mul]
  have hm₁ιinv : mat m₁⁻¹ * incM F H.ι = incM F H.ι * mat h₁⁻¹ := by
    calc mat m₁⁻¹ * incM F H.ι = mat m₁⁻¹ * (incM F H.ι * (mat h₁ * mat h₁⁻¹)) := by
          rw [mat_mul_inv'', Matrix.mul_one]
      _ = mat m₁⁻¹ * (mat m₁ * incM F H.ι) * mat h₁⁻¹ := by rw [hm₁.2.2]; simp only [Matrix.mul_assoc]
      _ = incM F H.ι * mat h₁⁻¹ := by rw [← Matrix.mul_assoc, mat_inv_mul'', Matrix.one_mul]
  have e1 : ∀ v, mat p *ᵥ v = mat m *ᵥ (mat (m⁻¹ * p) *ᵥ v) := by
    intro v; rw [Matrix.mulVec_mulVec, mat_mul'', ← Matrix.mul_assoc, mat_mul_inv'', Matrix.one_mul]
  refine ⟨p * m₁⁻¹ * m⁻¹, Subgroup.subset_closure ⟨?_, fun z => ?_⟩, m, hm, h₁, ?_⟩
  · calc mat (p * m₁⁻¹ * m⁻¹) *ᵥ incV F H.x = mat p *ᵥ (mat m₁⁻¹ *ᵥ (mat m⁻¹ *ᵥ incV F H.x)) := by
          simp only [mat_mul'', Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = t⁻¹.1 • (mat p *ᵥ (mat m₁⁻¹ *ᵥ incV F H.x)) := by rw [hmx, Matrix.mulVec_smul, Matrix.mulVec_smul]
      _ = incV F H.x := by rw [hm₁x, ht, smul_smul]; simp
  · obtain ⟨c, hc⟩ := hh₁ (mat h₁⁻¹ *ᵥ z)
    refine ⟨c * t.1, ?_⟩
    calc mat (p * m₁⁻¹ * m⁻¹) *ᵥ (incM F H.ι *ᵥ z) = mat p *ᵥ (mat m₁⁻¹ *ᵥ (mat m⁻¹ *ᵥ (incM F H.ι *ᵥ z))) := by
          simp only [mat_mul'', Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = mat p *ᵥ (incM F H.ι *ᵥ (mat h₁⁻¹ *ᵥ z)) := by
          rw [Matrix.mulVec_mulVec _ (mat m⁻¹), hmιinv, Matrix.mulVec_mulVec _ (mat m₁⁻¹), hm₁ιinv, ← Matrix.mulVec_mulVec]
      _ = mat m *ᵥ (incM F H.ι *ᵥ (mat h₁ *ᵥ (mat h₁⁻¹ *ᵥ z)) + c • incV F H.x) := by rw [e1, hc]
      _ = incM F H.ι *ᵥ z + (c * t.1) • incV F H.x := by
          rw [Matrix.mulVec_mulVec _ (mat h₁), mat_mul_inv'', Matrix.one_mulVec, Matrix.mulVec_add, Matrix.mulVec_mulVec, hmι,
            Matrix.mulVec_smul, hm.1, smul_smul]
  · rw [hM]; group

end GlobalTheory.ThK.InducedCons.ParDec

open GlobalTheory.ThK.SquareIntegrability in

theorem GlobalTheory.ThK.InducedCons.exists_isParDec : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ M : UA σ W₁.J → UA σ W.J, Continuous M → (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) →
      ∀ (r : ℕ) (X' Y' : Matrix (Fin n) (Fin (r + 1)) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) X' Y' →
      (∀ k, X' k 0 = H.x k) →
      ∀ (p : GAd σ (c₀ • W.J.map σ)) (t : (AE F E)ˣ), (matHom (AF F) σ (c₀ • W.J.map σ) p).1 *ᵥ incV F H.x = t.1 • incV F H.x →
      ∃ y : GAd σ (c₀ • W₁.J.map σ), GlobalTheory.ThK.InducedCons.IsParDec hσ W W₁ H hc₀ X' M t y p := by
  intro F E _ _ _ _ _ σ hcm hσ n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram c₀ hc₀ hJ₁ _ M _ hM r X' Y' hW hX p t hp
  have hd : W₁.J.det ≠ 0 := fun h0 => hJ₁.2 (by
    have e : (W₁.J.map σ).det = (σ : E →+* E) W₁.J.det := by rw [RingHom.map_det]; rfl
    rw [Matrix.det_smul, e, h0, map_zero, mul_zero])
  obtain ⟨q, rfl⟩ := (toGAd hσ W.J hc₀).surjective p
  obtain ⟨u, hu, m, hm, h₁, e⟩ := ParDec.exists_dec hcm W W₁ H hsk hn hxx hyy hxy horth hgram hd M hM q t hp
  have hP : GlobalTheory.ThK.GLTwo.IsHypPlane σ H W W₁ := ⟨hn, hxx, hyy, hxy, horth, hgram⟩
  refine ⟨toGAd hσ W₁.J hc₀ h₁, toGAd hσ W.J hc₀ u,
    (hP.mem_unip_iff hσ hsk hd hc₀ hW (Nat.succ_pos r) hX u).1 hu, m, hm, ?_⟩
  rw [e, map_mul, map_mul]
  simp only [GlobalTheory.ThK.CuspTransfer.emb, MulEquiv.symm_apply_apply]

end
