import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarOIsAddHaar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModelEigenContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdQ
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB GlobalTheory.StdPairLoc
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv

noncomputable section

namespace GlobalTheory.PlaneBasisInv

theorem det_ne_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]; ext i j; simp [A', Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.map_apply]
  have h2 : (A'ᵀ * M * A'.map star).det ≠ 0 := by
    rw [h1, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    simp [Matrix.det_neg]
  intro h0
  apply h2
  rw [Matrix.det_mul, Matrix.det_mul, h0]; simp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem det_ne_of_sig {n r s : ℕ} (c : ℂ)
    (B : Base F E) (J : Matrix (Fin n) (Fin n) E) (h : ∀ w, HasSig (c • J.map (B.emb w).1) r s) : J.det ≠ 0 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have := det_ne_of_hasSig (h w)
  intro h0; apply this
  have e := RingHom.map_det (B.emb w).1 J
  rw [RingHom.mapMatrix_apply] at e
  rw [Matrix.det_smul, ← e, h0, map_zero, mul_zero]

omit [NumberField F] [NumberField E] in
theorem form_swap {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ε : E)
    (hJ : ∀ i j, σ (J j i) = ε * J i j) (x y : Fin n → E) : σ (form σ J x y) = ε * form σ J y x := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem indep {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) (B : Base F E) {n n₁ : ℕ} (H : Plane E n n₁)
    (Y : Spc F E n) (Y₁ : Spc F E n₁) (i₀ i₁ : ℕ) (h : H.IsAdapted σ B Y Y₁ i₀ i₁) (ε : E)
    (hJ : ∀ i j, σ (Y.J j i) = ε * Y.J i j) (h₁ : Y₁.J.det ≠ 0) (s t : E) (u : Fin n₁ → E)
    (h0 : s • H.x + t • H.y + H.ι *ᵥ u = 0) : s = 0 ∧ t = 0 ∧ u = 0 := by
  have lin : ∀ z, s * form σ Y.J H.x z + t * form σ Y.J H.y z + form σ Y.J (H.ι *ᵥ u) z = 0 := by
    intro z
    have := congrArg (fun w => form σ Y.J w z) h0
    simpa [form, add_dotProduct, smul_dotProduct] using this
  have hs : s = 0 := by
    have := lin H.y
    rw [h.xy, h.yy, (h.orth u).2] at this
    simpa using this
  have hyx : form σ Y.J H.y H.x ≠ 0 := by
    intro h0
    have := form_swap hσ Y.J ε hJ H.x H.y
    rw [h.xy, h0] at this
    simp at this
  have ht : t = 0 := by
    have := lin H.x
    rw [h.xx, (h.orth u).1] at this
    simpa [hyx] using this
  refine ⟨hs, ht, ?_⟩
  have hu : H.ι *ᵥ u = 0 := by simpa [hs, ht] using h0
  apply Matrix.eq_zero_of_vecMul_eq_zero h₁
  rw [← h.gram, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, hu]
  simp

theorem det_ne {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) (B : Base F E) {n n₁ : ℕ} (H : Plane E n n₁)
    (Y : Spc F E n) (Y₁ : Spc F E n₁) (i₀ i₁ : ℕ) (h : H.IsAdapted σ B Y Y₁ i₀ i₁) (ε : E)
    (hJ : ∀ i j, σ (Y.J j i) = ε * Y.J i j) (h₁ : Y₁.J.det ≠ 0) (M : Matrix (Fin n) (Fin n) E)
    (k₀ k₁ : Fin n) (g : Fin n₁ → Fin n) (hg : Function.Injective g) (h01 : k₀ ≠ k₁)
    (hg0 : ∀ j, g j ≠ k₀) (hg1 : ∀ j, g j ≠ k₁) (hall : ∀ i, i = k₀ ∨ i = k₁ ∨ ∃ j, g j = i)
    (hx : ∀ r, M r k₀ = H.x r) (hy : ∀ r, M r k₁ = H.y r) (hι : ∀ r j, M r (g j) = H.ι r j) : M.det ≠ 0 := by
  classical
  intro hd
  obtain ⟨c, hc, hMc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
  have huniv : (Finset.univ : Finset (Fin n)) = insert k₀ (insert k₁ (Finset.univ.image g)) := by
    ext i
    simpa using hall i
  have hsum : ∀ f : Fin n → E, ∑ i, f i = f k₀ + f k₁ + ∑ j, f (g j) := by
    intro f
    rw [huniv, Finset.sum_insert (by simp [h01, hg0]), Finset.sum_insert (by simp [hg1]),
      Finset.sum_image (fun a _ b _ hab => hg hab), add_assoc]
  obtain ⟨e0, e1, e2⟩ := indep hσ B H Y Y₁ i₀ i₁ h ε hJ h₁ (c k₀) (c k₁) (fun j => c (g j)) (by
    ext r
    have := congrFun hMc r
    simp only [Matrix.mulVec, dotProduct] at this
    rw [hsum] at this
    simp only [hx, hy, hι] at this
    simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← this]; ring)
  apply hc
  ext i
  rcases hall i with rfl | rfl | ⟨j, rfl⟩
  · exact e0
  · exact e1
  · exact congrFun e2 j

theorem isUnit_map {v : Pl F} (τ : E →ₐ[F] Fv F v) {n : ℕ} (M : Matrix (Fin n) (Fin n) E) (h : M.det ≠ 0) :
    IsUnit (M.map τ).det := by
  have e := RingHom.map_det τ.toRingHom M
  rw [RingHom.mapMatrix_apply] at e
  change IsUnit (M.map τ.toRingHom).det
  rw [← e]
  exact (Ne.isUnit h).map _

theorem basis_isUnit_det : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {a b : ℕ}
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    IsUnit (GlobalTheory.PlaneBasis.basV B.τ₁ H).det ∧ IsUnit (GlobalTheory.PlaneBasis.basW B.τ₁ H').det := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁
  have hσ : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hT.base.cm.2.2.2, hT.base.cm.2.2.2, star_star]
  constructor
  · let M : Matrix (Fin (b + 2)) (Fin (b + 2)) E := fun r i =>
      if h0 : i.1 = 0 then H.x r else if h : i.1 = b + 1 then H.y r else
        H.ι r ⟨i.1 - 1, by have := i.2; omega⟩
    have hM : GlobalTheory.PlaneBasis.basV B.τ₁ H = M.map B.τ₁ := by
      refine Matrix.ext fun r i => ?_
      rw [Matrix.map_apply]
      simp only [GlobalTheory.PlaneBasis.basV, M]
      split_ifs <;> rfl
    rw [hM]
    apply isUnit_map
    refine det_ne hσ B H _ _ _ _ hC.hH 1 (fun i j => by rw [hT.geo.hV'.herm, one_mul])
      (det_ne_of_sig 1 B _ (fun w => by rw [one_smul]; exact hT₁.geo.hV'.sig w)) M
      ⟨0, by omega⟩ ⟨b + 1, by omega⟩ (fun j => ⟨j.1 + 1, by omega⟩) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro j k hjk
      simp only [Fin.mk.injEq] at hjk
      exact Fin.ext (by omega)
    · simp
    · intro j; simp
    · intro j; have := j.2; simp only [ne_eq, Fin.mk.injEq]; omega
    · intro i
      have := i.2
      by_cases h0 : i.1 = 0
      · exact Or.inl (Fin.ext h0)
      by_cases h1 : i.1 = b + 1
      · exact Or.inr (Or.inl (Fin.ext h1))
      exact Or.inr (Or.inr ⟨⟨i.1 - 1, by omega⟩, Fin.ext (by simp only; omega)⟩)
    · intro r; simp [M]
    · intro r; simp [M]
    · intro r j
      have := j.2
      have h1 : j.1 ≠ b := by omega
      simp [M, h1]
  · let M : Matrix (Fin (a + (b + 2))) (Fin (a + (b + 2))) E := fun r j =>
      if ha : j.1 = a then H'.x r else if hb : j.1 = a + b + 1 then H'.y r else
        if h : j.1 < a then H'.ι r ⟨j.1, by omega⟩ else H'.ι r ⟨j.1 - 1, by have := j.2; omega⟩
    have hM : GlobalTheory.PlaneBasis.basW B.τ₁ H' = M.map B.τ₁ := by
      refine Matrix.ext fun r i => ?_
      rw [Matrix.map_apply]
      simp only [GlobalTheory.PlaneBasis.basW, M]
      split_ifs <;> rfl
    rw [hM]
    apply isUnit_map
    refine det_ne hσ B H' _ _ _ _ hC.hH' (-1) (fun i j => by rw [hT.geo.hW.skew, neg_one_mul])
      (det_ne_of_sig Complex.I B _ hT₁.geo.hW.sig) M
      ⟨a, by omega⟩ ⟨a + b + 1, by omega⟩
      (fun j => ⟨if j.1 < a then j.1 else j.1 + 1, by have := j.2; split_ifs <;> omega⟩) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro j k hjk
      simp only [Fin.mk.injEq] at hjk
      apply Fin.ext
      split_ifs at hjk <;> omega
    · simp only [ne_eq, Fin.mk.injEq]; omega
    · intro j; simp only [ne_eq, Fin.mk.injEq]; split_ifs <;> omega
    · intro j; have := j.2; simp only [ne_eq, Fin.mk.injEq]; split_ifs <;> omega
    · intro i
      have := i.2
      by_cases h0 : i.1 = a
      · exact Or.inl (Fin.ext h0)
      by_cases h1 : i.1 = a + b + 1
      · exact Or.inr (Or.inl (Fin.ext h1))
      by_cases h2 : i.1 < a
      · exact Or.inr (Or.inr ⟨⟨i.1, by omega⟩, Fin.ext (by simp [h2])⟩)
      · exact Or.inr (Or.inr ⟨⟨i.1 - 1, by omega⟩, Fin.ext (by simp only; split_ifs <;> omega)⟩)
    · intro r; simp [M]
    · intro r
      have h1 : a + b + 1 ≠ a := by omega
      simp only [M, dif_neg h1, dif_pos]
    · intro r j
      have := j.2
      by_cases h2 : j.1 < a
      · have h3 : j.1 ≠ a := by omega
        have h4 : j.1 ≠ a + b + 1 := by omega
        simp [M, h2, h3, h4]
      · have h3 : j.1 + 1 ≠ a := by omega
        have h4 : j.1 ≠ a + b := by omega
        have h5 : ¬ j.1 + 1 < a := by omega
        simp [M, h2, h3, h4, h5]

end GlobalTheory.PlaneBasisInv

end
