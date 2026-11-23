import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerRestrictsToOrthocomp
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open GlobalTheory.Doubling (absE)
open GlobalTheory.ThK.GLTwo

noncomputable section

namespace GlobalTheory.FlagRadDec

open Matrix GlobalTheory.PlaneProj GlobalTheory.IsoPlaneProj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem x_vecMul (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} {H : Plane E n n₁} {W : Spc F E n} {W₁ : Spc F E n₁}
    (h : IsHypPlane σ H W W₁) (hsk : ∀ i j, σ (W.J j i) = -W.J i j) : H.x ᵥ* (W.J * H.ι.map σ) = 0 := by
  funext j
  have h0 : form σ W.J H.x (H.ι *ᵥ Pi.single j 1) = 0 := by
    rw [GlobalTheory.UnipCocptForm.form_swap σ W.J hsk hσ, (h.2.2.2.2.1 _).1, map_zero, neg_zero]
  rw [Pi.zero_apply, ← h0, form, ← dotProduct_single_one (H.x ᵥ* _) j, ← dotProduct_mulVec, ← mulVec_mulVec]
  congr 2
  funext i; simp [mulVec, dotProduct, Pi.single_apply]

theorem exists_proj (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} {H : Plane E n n₁} {Y : Spc F E n} {Y₁ : Spc F E n₁}
    (hI : IsHypPlane σ H Y Y₁) (hskew : ∀ i j, σ (Y.J j i) = -Y.J i j) (hd : Y₁.J.det ≠ 0) (p : UA σ Y.J)
    (hp : mat p *ᵥ incV F H.x = incV F H.x) : ∃ h₁ : UA σ Y₁.J,
      ∀ z : Fin n₁ → AE F E, ∃ a : AE F E, mat p *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (mat h₁ *ᵥ z) + a • incV F H.x := by
  have exι := x_vecMul hσ hI hskew
  obtain ⟨hn, hxx, hyy, hxy, horth, hgram⟩ := hI
  have hJ₁ : IsUnit Y₁.J.det := isUnit_iff_ne_zero.2 hd
  obtain ⟨π, hfr⟩ := frame_of_gram hσ hskew hn hxx hyy hxy horth hgram hJ₁
  set c : AE F E →+* AE F E := ((cA σ : AE F E →ₐ[AF F] AE F E) : AE F E →+* AE F E) with hc
  have eιx : (H.ιᵀ * Y.J) *ᵥ (⇑σ ∘ H.x) = 0 := by
    funext j
    have h0 := (horth (Pi.single j 1)).1
    rw [form, dotProduct_comm, dotProduct_mulVec, dotProduct_single_one] at h0
    rw [Pi.zero_apply, ← h0, ← mulVec_mulVec, mulVec_transpose]; rfl
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

end GlobalTheory.FlagRadDec

end
