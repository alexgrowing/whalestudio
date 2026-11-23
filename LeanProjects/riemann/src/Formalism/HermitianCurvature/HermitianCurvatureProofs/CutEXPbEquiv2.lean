import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.EmbeddedGroupMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MulVecBvecApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LieBracketMultiplication
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaFiniteOfHaar
import Formalism.FormalDegreeBessel.FinalG

open Matrix MeasureTheory Filter Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutEXPbEquiv

section clm

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E]

theorem integral_clm_leftInv (L M : E →L[ℂ] E) (hML : ∀ v, M (L v) = v) (f : α → E) :
    ∫ x, L (f x) ∂μ = L (∫ x, f x ∂μ) := by
  by_cases hf : Integrable f μ
  · exact L.integral_comp_comm hf
  · have hLf : ¬ Integrable (fun x => L (f x)) μ := by
      intro h
      apply hf
      have := M.integrable_comp h
      simpa [hML] using this
    rw [integral_undef hf, integral_undef hLf, map_zero]

end clm

section ops

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def post (A : Wp →L[ℂ] Wp) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) := ContinuousLinearMap.compL ℂ Wq Wp Wp A

def pre (B' : Wq →L[ℂ] Wq) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) := (ContinuousLinearMap.compL ℂ Wq Wq Wp).flip B'

theorem post_apply (A : Wp →L[ℂ] Wp) (f : Wq →L[ℂ] Wp) : post A f = A.comp f := rfl

theorem pre_apply (B' : Wq →L[ℂ] Wq) (f : Wq →L[ℂ] Wp) : pre B' f = f.comp B' := rfl

end ops

section homeo

variable {k r : ℕ}

def conjHomeo (a : B.Mat k r) (ha : IsUnit a.det) : Mt k r ≃ₜ Mt k r where
  toFun x := a * Matrix.of x * a⁻¹
  invFun x := a⁻¹ * Matrix.of x * a
  left_inv x := by
    show a⁻¹ * (a * Matrix.of x * a⁻¹) * a = x
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ ha, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha,
      Matrix.one_mul]; rfl
  right_inv x := by
    show a * (a⁻¹ * Matrix.of x * a) * a⁻¹ = x
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ ha, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha,
      Matrix.one_mul]; rfl
  continuous_toFun := by
    show Continuous fun x : Mt k r => a * Matrix.of x * a⁻¹
    exact (Continuous.matrix_mul continuous_const continuous_id).matrix_mul continuous_const
  continuous_invFun := by
    show Continuous fun x : Mt k r => a⁻¹ * Matrix.of x * a
    exact (Continuous.matrix_mul continuous_const continuous_id).matrix_mul continuous_const

end homeo

section kr

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [CompleteSpace Wp]

theorem unit_of_uw {z : Fin (2 * r + k + 1) → ℂ} {w : B.Mat k r} (hw : w ∈ UWset k r z) : IsUnit w.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hw.1

theorem kr_right_uw (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (x w : B.Mat k r)
    (hw : w ∈ UWset k r Bs.z') : PBG.Kr Bs F (x * w) = (PBG.Kr Bs F x).comp (Bs.π' w) := by
  have hU := unit_of_uw hw
  have hwi : w⁻¹ ∈ UWset k r Bs.z' := LieBracketMultiplication.uw_inv hw
  have := PBG.sigmaFinite_of_haar Bs.haarN
  have := PBG.sigmaFinite_of_haar Bs.haarW'
  set e1 := (PBG.lmulHomeo w hU).toMeasurableEquiv
  set e2 := (conjHomeo w hU).toMeasurableEquiv
  set Φ : Mt k r × Mt k r ≃ᵐ Mt k r × Mt k r := MeasurableEquiv.prodCongr e1 e2
  have hmp1 : MeasurePreserving e1 Bs.μW' Bs.μW' := by
    refine ⟨e1.measurable, ?_⟩
    have ee : ⇑e1 = lmulM w := by funext x; rfl
    rw [ee]; exact Bs.haarW'.left w hw
  have hmp2 : MeasurePreserving e2 Bs.μN Bs.μN := by
    refine ⟨e2.measurable, ?_⟩
    have ee : ⇑e2 = conjM w := by funext x; rfl
    rw [ee]; exact Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k r Bs.z' Bs.μN Bs.z'_mem Bs.T'_pos Bs.haarN w hw
  have hmp : MeasurePreserving Φ (Bs.μW'.prod Bs.μN) (Bs.μW'.prod Bs.μN) := hmp1.prod hmp2
  set f : Mt k r × Mt k r → (Wq →L[ℂ] Wp) := fun p => star (psi k r Bs.z' cStd (Matrix.of p.2)) •
      (F (x * Matrix.of p.2 * Matrix.of p.1)).comp (Bs.π' (Matrix.of p.1)⁻¹)
  set g : Mt k r × Mt k r → (Wq →L[ℂ] Wp) := fun p => star (psi k r Bs.z' cStd (Matrix.of p.2)) •
      (F (x * w * Matrix.of p.2 * Matrix.of p.1)).comp (Bs.π' (Matrix.of p.1)⁻¹)
  have hK1 : PBG.Kr Bs F x = ∫ p, f (Φ p) ∂(Bs.μW'.prod Bs.μN) := (hmp.integral_comp' f).symm
  have hae : ∀ᵐ p ∂(Bs.μW'.prod Bs.μN), (Matrix.of p.1 : B.Mat k r) ∈ UWset k r Bs.z' :=
    Measure.quasiMeasurePreserving_fst.ae (Formalism.FourierDecayAlt.P.B5.haar_ae Bs.haarW')
  have hK2 : ∫ p, f (Φ p) ∂(Bs.μW'.prod Bs.μN) = ∫ p, pre (Bs.π' w⁻¹) (g p) ∂(Bs.μW'.prod Bs.μN) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with p hp
    have hpsi : psi k r Bs.z' cStd (w * Matrix.of p.2 * w⁻¹) = psi k r Bs.z' cStd (Matrix.of p.2) := by
      have := Formalism.FourierDecayAlt.P.PBM.psi_conj_UW Bs.z' cStd w⁻¹ hwi (Matrix.of p.2)
      rwa [Matrix.nonsing_inv_nonsing_inv _ hU] at this
    have hmat : x * (w * Matrix.of p.2 * w⁻¹) * (w * Matrix.of p.1) = x * w * Matrix.of p.2 * Matrix.of p.1 := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc w⁻¹ w, Matrix.nonsing_inv_mul _ hU, Matrix.one_mul]
    have hpi : Bs.π' (w * Matrix.of p.1)⁻¹ = (Bs.π' (Matrix.of p.1)⁻¹).comp (Bs.π' w⁻¹) := by
      rw [Matrix.mul_inv_rev]
      exact Bs.π'_rep.2 _ (LieBracketMultiplication.uw_inv hp) _ hwi
    show star (psi k r Bs.z' cStd (w * Matrix.of p.2 * w⁻¹)) •
        (F (x * (w * Matrix.of p.2 * w⁻¹) * (w * Matrix.of p.1))).comp (Bs.π' (w * Matrix.of p.1)⁻¹) = _
    rw [hpsi, hmat, hpi, pre_apply, ContinuousLinearMap.smul_comp]
    rfl
  have hML : ∀ v : Wq →L[ℂ] Wp, pre (Bs.π' w) (pre (Bs.π' w⁻¹) v) = v := by
    intro v
    rw [pre_apply, pre_apply, ContinuousLinearMap.comp_assoc, ← Bs.π'_rep.2 _ hwi _ hw,
      Matrix.nonsing_inv_mul _ hU, Bs.π'_rep.1]
    rfl
  have hK3 : PBG.Kr Bs F x = (PBG.Kr Bs F (x * w)).comp (Bs.π' w⁻¹) := by
    rw [hK1, hK2, integral_clm_leftInv _ _ hML]
    rfl
  rw [hK3, ContinuousLinearMap.comp_assoc, ← Bs.π'_rep.2 _ hwi _ hw, Matrix.nonsing_inv_mul _ hU, Bs.π'_rep.1]
  rfl

end kr

section pb

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [CompleteSpace Wp]

theorem pbF_right_uw (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    (H : B.Mat k n → (Wq →L[ℂ] Wp)) (g w : B.Mat k n) (hw : w ∈ UWset k n B0.z') :
    PBQ.pbF Bj B0 e H (g * w) = (PBQ.pbF Bj B0 e H g).comp (B0.π' w) := by
  have hU := unit_of_uw hw
  have hwi : w⁻¹ ∈ UWset k n B0.z' := LieBracketMultiplication.uw_inv hw
  have hML : ∀ v : Wq →L[ℂ] Wp, pre (B0.π' w⁻¹) (pre (B0.π' w) v) = v := by
    intro v
    rw [pre_apply, pre_apply, ContinuousLinearMap.comp_assoc, ← B0.π'_rep.2 _ hw _ hwi,
      Matrix.mul_nonsing_inv _ hU, B0.π'_rep.1]
    rfl
  unfold PBQ.pbF
  rw [← pre_apply, ← integral_clm_leftInv _ _ hML]
  congr 1
  funext x
  unfold PBQ.pbI
  rw [← Matrix.mul_assoc, kr_right_uw B0 H _ w hw, pre_apply, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_assoc]

theorem pbF_left_uw (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    (H : B.Mat k n → (Wq →L[ℂ] Wp)) (h : B.Mat k ρ) (hh : h ∈ UWset k ρ Bj.z) (g : B.Mat k n) :
    PBQ.pbF Bj B0 e H (D.castM e (U.embG k p ρ h) * g) = (Bj.π h).comp (PBQ.pbF Bj B0 e H g) := by
  have hU := unit_of_uw hh
  have hi : h⁻¹ ∈ UWset k ρ Bj.z := LieBracketMultiplication.uw_inv hh
  have hiU := unit_of_uw hi
  have := PBG.sigmaFinite_of_haar Bj.haarN
  have := PBG.sigmaFinite_of_haar Bj.haarW
  haveI : SigmaFinite (U.muRC k p ρ) := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ
  set e1 := (PBG.lmulHomeo h⁻¹ hiU).toMeasurableEquiv
  set e2 := (conjHomeo h⁻¹ hiU).toMeasurableEquiv
  set Φ : PBQ.XP k p ρ ≃ᵐ PBQ.XP k p ρ := MeasurableEquiv.prodCongr (MeasurableEquiv.prodCongr e1 e2)
    (MeasurableEquiv.refl _)
  have hmp1 : MeasurePreserving e1 Bj.μW Bj.μW := by
    refine ⟨e1.measurable, ?_⟩
    have ee : ⇑e1 = lmulM h⁻¹ := by funext x; rfl
    rw [ee]; exact Bj.haarW.left h⁻¹ hi
  have hmp2 : MeasurePreserving e2 Bj.μN Bj.μN := by
    refine ⟨e2.measurable, ?_⟩
    have ee : ⇑e2 = conjM h⁻¹ := by funext x; rfl
    rw [ee]; exact Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k ρ Bj.z Bj.μN Bj.z_mem Bj.T_pos Bj.haarN h⁻¹ hi
  have hmp : MeasurePreserving Φ (PBQ.muXP (p := p) Bj) (PBQ.muXP (p := p) Bj) :=
    (hmp1.prod hmp2).prod (MeasurePreserving.id _)
  have hML : ∀ v : Wq →L[ℂ] Wp, post (Bj.π h⁻¹) (post (Bj.π h) v) = v := by
    intro v
    rw [post_apply, post_apply, ← ContinuousLinearMap.comp_assoc, ← Bj.π_rep.2 _ hi _ hh,
      Matrix.nonsing_inv_mul _ hU, Bj.π_rep.1]
    rfl
  have hF : PBQ.pbF Bj B0 e H g = ∫ x, PBQ.pbI Bj B0 e H g (Φ x) ∂(PBQ.muXP Bj) :=
    (hmp.integral_comp' (PBQ.pbI Bj B0 e H g)).symm
  rw [hF, ← post_apply, ← integral_clm_leftInv _ _ hML]
  unfold PBQ.pbF
  refine integral_congr_ae ?_
  filter_upwards [PBQ.ae_goodP Bj] with x hx
  have hx1 : (Matrix.of x.1.1 : B.Mat k ρ) ∈ UWset k ρ Bj.z := hx.1
  have hx2 : (Matrix.of x.1.2 : B.Mat k ρ) ∈ Nset k ρ := hx.2
  have hΦ : PBQ.GoodP Bj (Φ x) :=
    ⟨LieBracketMultiplication.uw_mul hi hx1, (Formalism.QuantumDeterminants.uWNormal k ρ Bj.z Bj.z_mem h⁻¹ hi _ hx2).1⟩
  have hsP : D.castM e (PBQ.sP Bj x) * (D.castM e (U.embG k p ρ h) * g) = D.castM e (PBQ.sP Bj (Φ x)) * g := by
    rw [← Matrix.mul_assoc, ← PBQ.castM_mul]
    congr 2
    unfold PBQ.sP
    rw [if_pos hx, if_pos hΦ]
    show U.Rn k p ρ (-x.2) * U.embG k p ρ ((Matrix.of x.1.1)⁻¹ * (Matrix.of x.1.2)⁻¹) * U.embG k p ρ h =
      U.Rn k p ρ (-x.2) * U.embG k p ρ ((h⁻¹ * Matrix.of x.1.1)⁻¹ * (h⁻¹ * Matrix.of x.1.2 * h⁻¹⁻¹)⁻¹)
    rw [Matrix.mul_assoc, ← Formalism.FourierDecayAlt.P.Dx2.Split.embG_mul]
    congr 2
    rw [Matrix.nonsing_inv_nonsing_inv h hU]
    simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv h hU, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc h h⁻¹, Matrix.mul_nonsing_inv _ hU, Matrix.one_mul]
  have hcP : PBQ.cP Bj (Φ x) = PBQ.cP Bj x := by
    unfold PBQ.cP
    show psi k ρ Bj.z cStd (h⁻¹ * Matrix.of x.1.2 * h⁻¹⁻¹) * _ = _
    rw [Matrix.nonsing_inv_nonsing_inv h hU, Formalism.FourierDecayAlt.P.PBM.psi_conj_UW Bj.z cStd h hh]
    rfl
  have hπ : Bj.π (Matrix.of x.1.1) = (Bj.π h).comp (Bj.π (h⁻¹ * Matrix.of x.1.1)) := by
    rw [← Bj.π_rep.2 _ hh _ (LieBracketMultiplication.uw_mul hi hx1), ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU, Matrix.one_mul]
  unfold PBQ.pbI
  rw [hsP, ← hcP, hπ, post_apply, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_assoc]
  rfl

end pb

end Formalism.FourierDecayAlt.P.CutEXPbEquiv

namespace Formalism.FourierDecayAlt.P

open CutEXPbEquiv

theorem pullback_equivalence : CutEX.PbEquiv := by
  intro Wp Wq _ _ _ _ _ _ P p G _ Z _ μ _ h hh h' hh'
  haveI : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have hw : D.castM (by omega : P.r + (P.r - P.r) = P.r) (U.embG P.k P.r (P.r - P.r) h') ∈
      UWset P.k P.r p.T.base.z' := by
    have h1 := Formalism.FourierDecayAlt.P.Dx2.Tower.lev_UW (k := P.k) P.r (P.r - P.r) _ h' hh'
    rw [Formalism.FourierDecayAlt.P.Dx2.Tower.lev_eq_embG] at h1
    have h2 := Formalism.FourierDecayAlt.P.Dx2.Tower.castM_UW (by omega : P.r + (P.r - P.r) = P.r) _ _ h1
    rw [p.T.z'_lev P.r le_rfl] at h2
    exact h2
  have hpi : p.T.base.π' (D.castM (by omega : P.r + (P.r - P.r) = P.r) (U.embG P.k P.r (P.r - P.r) h')) =
      (p.T.bs P.r).π' h' := by
    rw [p.T.π'_lev P.r le_rfl, Formalism.FourierDecayAlt.P.Dx2.Tower.lev_eq_embG]
    rfl
  unfold CutEX.pbTop PBQ.pbT CutEX.xT
  rw [LeftFubiniLemmas.embedding_map_embedded_group, PBQ.castM_mul, PBQ.castM_mul, pbF_right_uw _ _ _ _ _ _ hw, pbF_left_uw _ _ _ _ _ hh, hpi,
    ContinuousLinearMap.comp_assoc]

end Formalism.FourierDecayAlt.P
