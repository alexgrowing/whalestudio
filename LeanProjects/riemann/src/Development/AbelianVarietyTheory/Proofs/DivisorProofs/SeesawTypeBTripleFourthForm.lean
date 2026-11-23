import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarOIsAddHaar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModelEigenContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdQ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLocalLiftSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTypeBTripleHypothesisFormStatement
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB GlobalTheory.StdPairLoc
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv

noncomputable section

namespace GlobalTheory.PlaneSmallTransl

open Matrix GlobalTheory.IsoCoord GlobalTheory.PlaneBasis

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}

theorem gram_entry (t : E →ₐ[F] Fv F v) {n m : ℕ} (J : Matrix (Fin n) (Fin n) E) (C : Matrix (Fin n) (Fin n) (Fv F v))
    (I : Matrix (Fin n) (Fin m) E) (i : Fin n) (k : Fin m) (y : Fin n → E) (h : ∀ r, C r i = t (y r)) :
    (Cᵀ * J.map t * I.map (t.comp σ)) i k = t (form σ J y fun r => I r k) := by
  have hD : (Cᵀ * J.map t * I.map (t.comp σ)) i k =
      (fun r => C r i) ⬝ᵥ (J.map t *ᵥ fun r => t (σ (I r k))) := by
    rw [Matrix.mul_assoc]; rfl
  rw [hD, funext h, dot_form]

theorem triple_entry {R : Type} [CommRing R] {n m d e : ℕ} (A : Matrix (Fin n) (Fin m) R) (z : Matrix (Fin m) (Fin e) R)
    (C : Matrix (Fin d) (Fin e) R) (i : Fin n) (j : Fin d) : (A * z * Cᵀ) i j = A i ⬝ᵥ (z *ᵥ C j) := by
  rw [Matrix.mul_assoc]; rfl

theorem co_eq {R : Type} [Field R] {n m d e : ℕ} (P A : Matrix (Fin n) (Fin n) R) (Q C : Matrix (Fin d) (Fin d) R)
    (hP : IsUnit P.det) (hQ : IsUnit Q.det) (I : Matrix (Fin n) (Fin m) R) (I' : Matrix (Fin d) (Fin e) R)
    (z : Matrix (Fin m) (Fin e) R) :
    -(A * (I * z * I'ᵀ) * Cᵀ) = Pᵀ⁻¹ * (-((Pᵀ * A * I) * z * (Qᵀ * C * I')ᵀ)) * Q⁻¹ := by
  have hP' : IsUnit Pᵀ.det := by rwa [det_transpose]
  simp only [transpose_mul, transpose_transpose, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  rw [nonsing_inv_mul_cancel_left _ _ hP', mul_nonsing_inv _ hQ, Matrix.mul_one]

theorem gram_rows {B : Base F E} (hcm : IsCMExt F E σ) {n n₁ : ℕ} {H : Plane E n n₁} {Y : Spc F E n} {Y₁ : Spc F E n₁}
    {i₀ i₁ : ℕ} (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) (ε : E) (hε : ε ≠ 0) (hJ : ∀ i j, σ (Y.J j i) = ε * Y.J i j)
    (t : E →ₐ[F] Fv F v) (C : Matrix (Fin n) (Fin n) (Fv F v)) (i : Fin n) :
    ((∀ r, C r i = t (H.x r)) → (Cᵀ * Y.J.map t * H.ι.map (t.comp σ)) i = 0) ∧
    ((∀ r, C r i = t (H.y r)) → (Cᵀ * Y.J.map t * H.ι.map (t.comp σ)) i = 0) ∧
    ∀ k, (∀ r, C r i = t (H.ι r k)) → (Cᵀ * Y.J.map t * H.ι.map (t.comp σ)) i = Y₁.J.map t k := by
  refine ⟨fun h => funext fun k => ?_, fun h => funext fun k => ?_, fun k h => funext fun l => ?_⟩
  · have := form_swap hcm ε hJ (fun r => H.ι r k) H.x
    rw [(orth_col hH k).1, map_zero] at this
    rw [gram_entry t _ _ _ i k H.x h, (mul_eq_zero.1 this.symm).resolve_left hε, map_zero, Pi.zero_apply]
  · have := form_swap hcm ε hJ (fun r => H.ι r k) H.y
    rw [(orth_col hH k).2, map_zero] at this
    rw [gram_entry t _ _ _ i k H.y h, (mul_eq_zero.1 this.symm).resolve_left hε, map_zero, Pi.zero_apply]
  · rw [gram_entry t _ _ _ i l (fun r => H.ι r k) h, gram_form, hH.gram]
    rfl

variable {B : Base F E} {a b : ℕ} {G : Geo σ a (b + 2)} {G₁ : Geo σ a b} {H : Plane E (b + 2) b}
    {H' : Plane E (a + (b + 2)) (a + b)}

theorem co_embedded (hB : B.IsGood σ) (hG : G.IsGood B) (hC : CfgB B G G₁ H H') (t : E →ₐ[F] Fv F v)
    (hP : IsUnit (basV t H).det) (hQ : IsUnit (basW t H').det) (z : Matrix (Fin b) (Fin (a + b)) (Fv F v)) :
    -(G.V'.J.map t * (H.ι.map (t.comp σ) * z * (H'.ι.map (t.comp σ))ᵀ) * (G.W.J.map t)ᵀ) =
      crdP t H * insS (-(G₁.V'.J.map t * z * (G₁.W.J.map t)ᵀ)) 0 0 0 * crdQ t H' := by
  rw [co_eq _ _ _ _ hP hQ]
  unfold crdP crdQ
  congr 2
  ext i j
  obtain ⟨p0, p1, p2⟩ := gram_rows hB.cm hC.hH 1 one_ne_zero (fun i j => by rw [one_mul]; exact hG.hV'.herm i j) t
    (basV t H) i
  obtain ⟨q0, q1, q2⟩ := gram_rows hB.cm hC.hH' (-1) (neg_ne_zero.2 one_ne_zero)
    (fun i j => by rw [neg_one_mul]; exact hG.hW.skew i j) t (basW t H') j
  rw [Matrix.neg_apply, triple_entry]
  by_cases i0 : i.1 = 0
  · rw [p0 fun r => by simp only [basV, dif_pos i0]]
    simp [insS, i0]
  by_cases i1 : i.1 = b + 1
  · rw [p1 fun r => by simp only [basV, dif_neg i0, dif_pos i1]]
    simp [insS, i1]
  rw [p2 ⟨i.1 - 1, by have := i.2; omega⟩ fun r => by simp only [basV, dif_neg i0, dif_neg i1]]
  by_cases j0 : j.1 = a
  · rw [q0 fun r => by simp only [basW, dif_pos j0]]
    simp [insS, i0, i1, j0]
  by_cases j1 : j.1 = a + b + 1
  · rw [q1 fun r => by simp only [basW, dif_neg j0, dif_pos j1]]
    have e1 : ¬ j.1 < a := by omega
    simp only [insS, dif_neg i0, dif_neg i1, dif_neg e1, dif_neg j0, dif_pos j1]
    simp
  by_cases j2 : j.1 < a
  · rw [q2 ⟨j.1, by omega⟩ fun r => by simp only [basW, dif_neg j0, dif_neg j1, dif_pos j2]]
    simp only [insS, dif_neg i0, dif_neg i1, dif_pos j2]
    rw [Matrix.neg_apply, triple_entry]
  · rw [q2 ⟨j.1 - 1, by have := j.2; omega⟩ fun r => by simp only [basW, dif_neg j0, dif_neg j1, dif_neg j2]]
    simp only [insS, dif_neg i0, dif_neg i1, dif_neg j0, dif_neg j1, dif_neg j2]
    rw [Matrix.neg_apply, triple_entry]

theorem small_transl : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {a b : ℕ}
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (L : ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F B.v₁) → ℂ),
    (∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁), L φ ∈ SB (Fin b × Fin (a + b) → Fv F B.v₁)) →
    (∀ z : Matrix (Fin b) (Fin (a + b)) (AE F E), At (evFin F B.v₁) z → ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁),
      L (schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (GlobalTheory.LatVac.locCo G.M'.co B.v₁ (incM F H.ι * z * (incM F H'.ι)ᵀ)) φ) =
        schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (GlobalTheory.LatVac.locCo G₁.M'.co B.v₁ z) (L φ)) →
    (∀ u ∈ isoB H H', At (evFin F B.v₁) u → ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁),
      L (schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (GlobalTheory.LatVac.locCo G.M'.co B.v₁ u) φ) = L φ) →
    ∀ ι ι₁, G.M'.IsLinBar B.ψ B.τ₁ 1 1 ι → G₁.M'.IsLinBar B.ψ B.τ₁ 1 1 ι₁ →
    ∀ (Y : Matrix (Fin b) (Fin (a + b)) (Fv F B.v₁)), ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁), ∃ φ' ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁), ι₁ (L φ') 0 = ι₁ (L φ) Y ∧
      ∀ Z, ι φ' Z = ι φ (Z + GlobalTheory.PlaneBasis.crdP B.τ₁ H * insS Y 0 0 0 * GlobalTheory.PlaneBasis.crdQ B.τ₁ H') := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ L hLSB hheis _ ι ι₁ hι hι₁ Y φ hφ
  obtain ⟨hP, hQ⟩ := GlobalTheory.T.seesaw_type_b_triple_hypothesis_form B G G₁ H H' hC X om om' om₁ om₁' hT hT₁
  have hN : IsUnit (G₁.V'.J.map B.τ₁).det := isUnit_iff_ne_zero.2 (det_map_ne_zero _
      (GlobalTheory.isUnit_det_of_isHerm F E σ B b G₁.V' _ _ hT₁.geo.hV').ne_zero)
  have hM : IsUnit (G₁.W.J.map B.τ₁)ᵀ.det := by
    rw [det_transpose]
    exact isUnit_iff_ne_zero.2 (det_map_ne_zero _ (det_ne_zero_skew hT₁.geo.hW))
  obtain ⟨z, hz, z0, z1⟩ := GlobalTheory.SplitComps.exists_mat_comps hT.base.cm B.v₁ B.τ₁ 0
    (-((G₁.V'.J.map B.τ₁)⁻¹ * Y * (G₁.W.J.map B.τ₁)ᵀ⁻¹))
  have hY : -(G₁.V'.J.map B.τ₁ * z.map (piW (B.τ₁.comp σ)) * (G₁.W.J.map B.τ₁)ᵀ) = Y := by
    rw [z1]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [mul_nonsing_inv_cancel_left _ _ hN, nonsing_inv_mul _ hM, Matrix.mul_one]
  have hat : At (evFin F B.v₁) (incM F H.ι * z * (incM F H'.ι)ᵀ) := by
    intro r hr
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hz r hr, Matrix.mul_zero, Matrix.zero_mul]
  have hinc : ∀ (t : E →ₐ[F] Fv F B.v₁) {m n : ℕ} (A : Matrix (Fin m) (Fin n) E), (incM F A).map (piW t) = A.map t :=
    fun t _ _ A => Matrix.ext fun i j => piW_incl t (A i j)
  have hm : ∀ t : E →ₐ[F] Fv F B.v₁, (incM F H.ι * z * (incM F H'.ι)ᵀ).map (piW t) =
      H.ι.map t * z.map (piW t) * (H'.ι.map t)ᵀ := by
    intro t
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hinc, hinc]
  have hL := hι
  have hL₁ := hι₁
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLinBar at hL hL₁
  simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at hL hL₁
  have s := GlobalTheory.SchrSB.schr_mem_SB B.ψ hT.base.std.1 B.v₁
    (GlobalTheory.LatVac.locCo G.M'.co B.v₁ (incM F H.ι * z * (incM F H'.ι)ᵀ)) φ hφ
  have s₁ := GlobalTheory.SchrSB.schr_mem_SB B.ψ hT.base.std.1 B.v₁ (GlobalTheory.LatVac.locCo G₁.M'.co B.v₁ z) _ (hLSB φ hφ)
  refine ⟨_, s, ?_, fun Z => ?_⟩
  · rw [hheis z hz φ hφ,
      hL₁.trans z hz z0 _ (hLSB φ hφ) _ s₁ (GlobalTheory.VacBridge.rho_acts_locCo G₁.M'.co B.ψ B.v₁ z hz _)]
    beta_reduce
    rw [hY, zero_add]
  · rw [hL.trans _ hat (by rw [hm, z0, Matrix.mul_zero, Matrix.zero_mul]) _ hφ _ s
      (GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ B.v₁ _ hat _)]
    beta_reduce
    rw [hm, co_embedded hT.base hT.geo hC B.τ₁ hP hQ, hY]

end GlobalTheory.PlaneSmallTransl

end
