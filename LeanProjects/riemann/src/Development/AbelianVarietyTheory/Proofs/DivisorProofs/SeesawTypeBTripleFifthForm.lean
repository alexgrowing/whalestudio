import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarOIsAddHaar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModelEigenContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdQ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTypeBTripleHypothesisFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBFlipShifted
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorIsotropicTranslationCharSplit

open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB GlobalTheory.StdPairLoc
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv

noncomputable section

namespace GlobalTheory.ShiftAdapted

open GlobalTheory.PlaneBasis GlobalTheory.ShiftCoords
open GlobalTheory.FlipMatch (coX coY pairM)

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have hA' : A'ᵀ * M * A'.map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]
    ext i j
    simp [A', Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.map_apply]
  have hD : (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)).det ≠ 0 := by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one]
    simp
  intro hM
  apply hD
  rw [← Matrix.det_submatrix_equiv_self e.symm, ← hA', Matrix.det_mul, Matrix.det_mul, hM, mul_zero, zero_mul]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem det_ne_zero_herm {B : Base F E} {n r s : ℕ} {X : Spc F E n} (h : X.IsHerm σ B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  intro h0
  apply det_ne_zero_of_hasSig (h.sig w)
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

theorem det_ne_zero_skew {B : Base F E} {n r s : ℕ} {X : Spc F E n} (h : X.IsSkew σ B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  intro h0
  apply det_ne_zero_of_hasSig (h.sig w)
  rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero]

theorem form_col {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E) (ι : Matrix (Fin n) (Fin n₁) E) (z : Fin n → E)
    (hz : ∀ u, form σ J (ι *ᵥ u) z = 0) (k : Fin n₁) : form σ J (fun r => ι r k) z = 0 := by
  have e : ι *ᵥ Pi.single k 1 = fun r => ι r k := by
    ext r; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [← e, hz]

theorem herm_vec' {B : Base F E} {b : ℕ} {H : Plane E (b + 2) b} {Y : Spc F E (b + 2)} {Y₁ : Spc F E b}
    (hH : H.IsAdapted σ B Y Y₁ 0 (b + 1)) {v : Pl F} (t : E →ₐ[F] Fv F v) :
    ((basV t H)ᵀ * Y.J.map t) *ᵥ (fun s => t (σ (H.y s))) = Pi.single 0 1 := by
  funext i
  rw [← Matrix.mulVec_mulVec]
  change ∑ r, basV t H r i * (Y.J.map t *ᵥ fun s => t (σ (H.y s))) r = _
  by_cases h0 : i.1 = 0
  · have : i = 0 := Fin.ext h0
    simp only [basV, dif_pos h0]
    rw [sum_form, hH.xy, map_one, this, Pi.single_eq_same]
  have : i ≠ 0 := fun e => h0 (by rw [e]; rfl)
  rw [Pi.single_eq_of_ne this]
  by_cases h1 : i.1 = b + 1
  · simp only [basV, dif_neg h0, dif_pos h1]
    rw [sum_form, hH.yy, map_zero]
  · simp only [basV, dif_neg h0, dif_neg h1]
    rw [sum_form σ t Y.J (fun r => H.ι r _), form_col _ _ _ (fun u => (hH.orth u).2), map_zero]

theorem skew_vec' (hcm : IsCMExt F E σ) {B : Base F E} {a b : ℕ} {H' : Plane E (a + (b + 2)) (a + b)}
    {Y : Spc F E (a + (b + 2))} {Y₁ : Spc F E (a + b)} (hY : ∀ i j, σ (Y.J j i) = -Y.J i j)
    (hH : H'.IsAdapted σ B Y Y₁ a (a + b + 1)) {v : Pl F} (t : E →ₐ[F] Fv F v) :
    (fun s => t (σ (H'.x s))) ᵥ* ((Y.J.map t)ᵀ * basW t H') =
      -Pi.single (⟨a + b + 1, by omega⟩ : Fin (a + (b + 2))) 1 := by
  funext i
  rw [← Matrix.vecMul_vecMul, Matrix.vecMul_transpose]
  change ∑ r, (Y.J.map t *ᵥ fun s => t (σ (H'.x s))) r * basW t H' r i = _
  simp only [mul_comm _ (basW t H' _ i)]
  by_cases h0 : i.1 = a
  · have : i ≠ ⟨a + b + 1, by omega⟩ := fun e => by have := congrArg Fin.val e; simp at this; omega
    simp only [basW, dif_pos h0]
    rw [sum_form, hH.xx, map_zero, Pi.neg_apply, Pi.single_eq_of_ne this, neg_zero]
  by_cases h1 : i.1 = a + b + 1
  · have : i = ⟨a + b + 1, by omega⟩ := Fin.ext h1
    simp only [basW, dif_neg h0, dif_pos h1]
    rw [sum_form, form_swap_skew hcm Y.J hY, hH.xy, map_one, map_neg, map_one, Pi.neg_apply, this,
      Pi.single_eq_same]
  · have : i ≠ ⟨a + b + 1, by omega⟩ := fun e => h1 (by rw [e])
    rw [Pi.neg_apply, Pi.single_eq_of_ne this, neg_zero]
    by_cases hlt : i.1 < a
    · simp only [basW, dif_neg h0, dif_neg h1, dif_pos hlt]
      rw [sum_form σ t Y.J (fun r => H'.ι r _), form_col _ _ _ (fun u => (hH.orth u).1), map_zero]
    · simp only [basW, dif_neg h0, dif_neg h1, dif_neg hlt]
      rw [sum_form σ t Y.J (fun r => H'.ι r _), form_col _ _ _ (fun u => (hH.orth u).1), map_zero]

theorem insS_shift {R : Type} [AddZeroClass R] {a b : ℕ} (Y : Matrix (Fin b) (Fin (a + b)) R) (r : Fin (a + (b + 2)) → R)
    (c : Fin b → R) (l : R) : insS Y r c 0 + insS 0 0 0 l = insS Y r c l := by
  funext i j
  simp only [insS, Matrix.add_apply]
  split_ifs <;> simp

theorem shift_acts : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {a b : ℕ}
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ ι, G.M'.IsLinBar B.ψ B.τ₁ 1 1 ι → ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁), ∀ l : (AE F E)ˣ, ∃ (c₀ : ℂ) (s x : Fv F B.v₁),
      ∀ (Y : Matrix (Fin b) (Fin (a + b)) (Fv F B.v₁)) (r : Fin (a + (b + 2)) → Fv F B.v₁) (c : Fin b → Fv F B.v₁),
        ι (schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (GlobalTheory.LatVac.locCo G.M'.co B.v₁ (shiftB σ H H' l)) φ)
            (GlobalTheory.PlaneBasis.crdP B.τ₁ H * insS Y r c 0 * GlobalTheory.PlaneBasis.crdQ B.τ₁ H') =
          c₀ * GlobalTheory.LatVac.psiAt B.ψ B.v₁ (s * r ⟨a, by omega⟩) * ι φ (GlobalTheory.PlaneBasis.crdP B.τ₁ H * insS Y r c x * GlobalTheory.PlaneBasis.crdQ B.τ₁ H') := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ ι hι φ hφ l
  obtain ⟨hP, hQ⟩ := GlobalTheory.T.seesaw_type_b_triple_hypothesis_form B G G₁ H H' hC X om om' om₁ om₁' hT hT₁
  have hcm := hT.base.cm
  have hPT : IsUnit (basV B.τ₁ H)ᵀ.det := by rwa [Matrix.det_transpose]
  have hmap1 : (partFin B.v₁ (shiftB σ H H' l)).map (piW B.τ₁) =
      piW (B.τ₁.comp σ) (l : AE F E) • Matrix.vecMulVec (fun i => B.τ₁ (H.y i)) (fun j => B.τ₁ (H'.x j)) := by
    ext i j
    simp only [partFin, shiftB, Matrix.map_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, incV,
      piW_smul', GlobalTheory.LatVac.evFin_liftV, one_mul, map_mul, piW_cA'', piW_inclR']
  have hmap2 : (partFin B.v₁ (shiftB σ H H' l)).map (piW (B.τ₁.comp σ)) =
      piW B.τ₁ (l : AE F E) • Matrix.vecMulVec (fun i => B.τ₁ (σ (H.y i))) (fun j => B.τ₁ (σ (H'.x j))) := by
    ext i j
    simp only [partFin, shiftB, Matrix.map_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, incV,
      piW_smul', GlobalTheory.LatVac.evFin_liftV, one_mul, map_mul, piW_cA'', piW_inclR', comp_conj_conj hcm, AlgHom.comp_apply]

  have hX : ∀ Z : Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F B.v₁),
      pairM (crdP B.τ₁ H * Z * crdQ B.τ₁ H') (coX B.τ₁ 1 1 (partFin B.v₁ (shiftB σ H H' l))) =
        piW (B.τ₁.comp σ) (l : AE F E) * Z (Fin.last (b + 1)) ⟨a, by omega⟩ := by
    intro Z
    have hb : (crdP B.τ₁ H)ᵀ *ᵥ (fun i => B.τ₁ (H.y i)) = Pi.single (Fin.last (b + 1)) 1 := by
      have e : basV B.τ₁ H *ᵥ Pi.single (Fin.last (b + 1)) 1 = fun i => B.τ₁ (H.y i) := by
        funext r
        rw [Matrix.mulVec_single_one]
        simp [basV]
      rw [← e, Matrix.mulVec_mulVec, crdP, Matrix.transpose_nonsing_inv, Matrix.transpose_transpose,
        Matrix.nonsing_inv_mul _ hP, Matrix.one_mulVec]
    have hc : (fun j => B.τ₁ (H'.x j)) ᵥ* (crdQ B.τ₁ H')ᵀ = Pi.single (⟨a, by omega⟩ : Fin (a + (b + 2))) 1 := by
      have e : basW B.τ₁ H' *ᵥ Pi.single (⟨a, by omega⟩ : Fin (a + (b + 2))) 1 = fun i => B.τ₁ (H'.x i) := by
        funext r
        rw [Matrix.mulVec_single_one]
        simp [basW]
      rw [Matrix.vecMul_transpose, ← e, Matrix.mulVec_mulVec, crdQ, Matrix.nonsing_inv_mul _ hQ, Matrix.one_mulVec]
    rw [GlobalTheory.HeisFlip.pairM_mul, coX, hmap1, inv_one, inv_one, Units.val_one, Units.val_one, Matrix.transpose_one,
      Matrix.one_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec_mul', hb, hc]
    simp [pairM, Matrix.vecMulVec_apply, Pi.single_apply, mul_comm]

  have hY : coY σ G.V' G.W B.τ₁ 1 1 (partFin B.v₁ (shiftB σ H H' l)) =
      crdP B.τ₁ H * insS (a := a) (b := b) 0 0 0 (piW B.τ₁ (l : AE F E)) * crdQ B.τ₁ H' := by
    have e : (basV B.τ₁ H)ᵀ * coY σ G.V' G.W B.τ₁ 1 1 (partFin B.v₁ (shiftB σ H H' l)) * basW B.τ₁ H' =
        insS 0 0 0 (piW B.τ₁ (l : AE F E)) := by
      have e1 : (basV B.τ₁ H)ᵀ * coY σ G.V' G.W B.τ₁ 1 1 (partFin B.v₁ (shiftB σ H H' l)) * basW B.τ₁ H' =
          -(((basV B.τ₁ H)ᵀ * G.V'.J.map B.τ₁) * (partFin B.v₁ (shiftB σ H H' l)).map (piW (B.τ₁.comp σ)) *
            ((G.W.J.map B.τ₁)ᵀ * basW B.τ₁ H')) := by
        simp only [coY, Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg,
          Matrix.neg_mul, Matrix.mul_assoc]
      rw [e1, hmap2, Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec_mul', herm_vec' hC.hH,
        skew_vec' hcm hT.geo.hW.skew hC.hH']
      ext i j
      have hj' : j = (⟨a + b + 1, by omega⟩ : Fin (a + (b + 2))) ↔ j.1 = a + b + 1 := Fin.ext_iff
      have hi' : i = 0 ↔ i.1 = 0 := Fin.ext_iff
      by_cases hi : i.1 = 0 <;> by_cases hj : j.1 = a + b + 1 <;>
        simp [insS, hi, hj, hi', hj', Matrix.vecMulVec_apply, Pi.single_apply]
    rw [← e, crdP, crdQ, Matrix.mul_assoc (basV B.τ₁ H)ᵀ, Matrix.nonsing_inv_mul_cancel_left _ _ hPT,
      Matrix.mul_nonsing_inv_cancel_right _ _ hQ]
  have hp : pairM (coX B.τ₁ 1 1 (partFin B.v₁ (shiftB σ H H' l)))
      (coY σ G.V' G.W B.τ₁ 1 1 (partFin B.v₁ (shiftB σ H H' l))) = 0 := by
    rw [GlobalTheory.HeisFlip.pairM_comm, hY, hX]
    simp [insS]
  obtain ⟨hact, hloc⟩ := locOp_rho G.M'.co hT.base.std.1 B.v₁ (shiftB σ H H' l) hφ
  have key := (GlobalTheory.HeisFlip.heis_trans_char hcm G.V' G.W hT.geo.hV'.herm hT.geo.hW.skew (det_ne_zero_herm hT.geo.hV')
    (det_ne_zero_skew hT.geo.hW) G.M' B.ψ hT.base.std B.τ₁ 1 1 _ (at_partFin _ _) hp φ hφ _ (locOp_mem _ _ _) hact).2 ι hι
  refine ⟨1, -piW (B.τ₁.comp σ) (l : AE F E), piW B.τ₁ (l : AE F E), fun Y r c => ?_⟩
  rw [← hloc, key, hX, hY, ← Matrix.add_mul, ← Matrix.mul_add, insS_shift, one_mul, GlobalTheory.LatVac.psiAt_apply]
  congr 2
  simp [insS]

end GlobalTheory.ShiftAdapted

end
