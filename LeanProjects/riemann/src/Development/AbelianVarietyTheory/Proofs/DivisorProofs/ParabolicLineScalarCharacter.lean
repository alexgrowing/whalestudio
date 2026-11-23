import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLocalTorusFactorization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocOpInfMul
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LineStabLevi

open GlobalTheory.PlaneLeviExt GlobalTheory.PlaneLeviAt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def hypH : Matrix (Fin 2) (Fin 2) E := !![0, 1; 1, 0]

lemma form_swap_herm (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (a b : Fin n → E) : form σ J a b = σ (form σ J b a) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

variable {d d₁ : ℕ}

lemma gram_frame_herm (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) (B : Base F E) {V : Spc F E d} {V₁ : Spc F E d₁}
    {H : Plane E d d₁} {i₀ i₁ r s : ℕ} (hV : V.IsHerm σ B r s) (hA : H.IsAdapted σ B V V₁ i₀ i₁) :
    (frame H)ᵀ * V.J * (frame H).map σ = Matrix.fromBlocks V₁.J 0 0 hypH := by
  have hcol : ∀ k, (fun i => H.ι i k) = H.ι *ᵥ Pi.single k 1 := fun k => by
    ext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have ho : ∀ l, form σ V.J (H.ι.col l) H.x = 0 ∧ form σ V.J (H.ι.col l) H.y = 0 := fun l => by
    have hc : H.ι.col l = H.ι *ᵥ Pi.single l 1 := hcol l
    rw [hc]; exact hA.orth _
  have hyx : form σ V.J H.y H.x = 1 := by
    rw [form_swap_herm σ hσ V.J hV.herm, hA.xy, map_one]
  ext a b
  rw [entry]
  change form σ V.J _ _ = _
  rcases a with k | k <;> rcases b with l | l
  · rw [← hA.gram, Matrix.fromBlocks_apply₁₁, entry]; rfl
  · fin_cases l
    · simp only [frame, twoCols, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, Matrix.of_apply]; exact (ho k).1
    · simp only [frame, twoCols, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, Matrix.of_apply]; exact (ho k).2
  · fin_cases k
    · simp [frame, twoCols, hcol]
      rw [form_swap_herm σ hσ V.J hV.herm]; simp [(ho l).1]
    · simp [frame, twoCols, hcol]
      rw [form_swap_herm σ hσ V.J hV.herm]; simp [(ho l).2]
  · fin_cases k <;> fin_cases l
    · simpa [frame, twoCols, hypH] using hA.xx
    · simpa [frame, twoCols, hypH] using hA.xy
    · simpa [frame, twoCols, hypH] using hyx
    · simpa [frame, twoCols, hypH] using hA.yy

lemma frame_mulVec_eq_zero_herm (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) (B : Base F E) {V : Spc F E d}
    {V₁ : Spc F E d₁} {H : Plane E d d₁} {i₀ i₁ r s r₁ s₁ : ℕ} (hV : V.IsHerm σ B r s)
    (hV₁ : V₁.IsHerm σ B r₁ s₁) (hA : H.IsAdapted σ B V V₁ i₀ i₁) (v : Fin d₁ ⊕ Fin 2 → E)
    (hv : frame H *ᵥ v = 0) : v = 0 := by
  have hg := gram_frame_herm σ hσ B hV hA
  have h0 : v ᵥ* Matrix.fromBlocks V₁.J 0 0 hypH = 0 := by
    rw [← hg, Matrix.mul_assoc, ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, hv, Matrix.zero_vecMul]
  have h1 : v (Sum.inr 0) = 0 ∧ v (Sum.inr 1) = 0 := by
    have a := congrFun h0 (Sum.inr 0)
    have b := congrFun h0 (Sum.inr 1)
    simp [Matrix.vecMul_fromBlocks, hypH, Matrix.vecMul, dotProduct, Fin.sum_univ_two] at a b
    exact ⟨b, a⟩
  have h2 : (fun k : Fin 2 => v (Sum.inr k)) = 0 := by
    ext k; fin_cases k
    · exact h1.1
    · exact h1.2
  have hu : H.ι *ᵥ (fun k => v (Sum.inl k)) = 0 := by
    have : frame H *ᵥ v = H.ι *ᵥ (fun k => v (Sum.inl k)) + twoCols H *ᵥ (fun k => v (Sum.inr k)) := by
      rw [frame, Matrix.fromCols_mulVec]; rfl
    rw [this, h2, Matrix.mulVec_zero, add_zero] at hv
    exact hv
  have hu0 := not_line V₁.L hV₁.lat (fun k => v (Sum.inl k)) fun a =>
    (hA.low _).mpr (by rw [Matrix.mulVec_smul, hu, smul_zero]; exact zero_mem _)
  ext (k | k)
  · exact congrFun hu0 k
  · exact congrFun h2 k

lemma isUnit_sq_herm (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) (B : Base F E) {V : Spc F E d}
    {V₁ : Spc F E d₁} {H : Plane E d d₁} {i₀ i₁ r s r₁ s₁ : ℕ} (hV : V.IsHerm σ B r s)
    (hV₁ : V₁.IsHerm σ B r₁ s₁) (hA : H.IsAdapted σ B V V₁ i₀ i₁) : IsUnit (PlaneLeviExt.sq hA.rank H) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro a b hab
  have h0 : PlaneLeviExt.sq hA.rank H *ᵥ (a - b) = 0 := by rw [Matrix.mulVec_sub, hab, sub_self]
  rw [PlaneLeviExt.sq, Matrix.submatrix_mulVec_equiv] at h0
  have h1 := frame_mulVec_eq_zero_herm σ hσ B hV hV₁ hA _ (by simpa using h0)
  have h2 : a - b = 0 := by
    ext i
    have := congrFun h1 ((num hA.rank).symm i)
    simpa using this
  exact sub_eq_zero.mp h2

lemma dg_unitary_herm (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) (t : (AE F E)ˣ) :
    (dg σ t)ᵀ * incM F (hypH (E := E)) * (dg σ t).map (cA σ) = incM F (hypH (E := E)) := by
  have hc := GlobalTheory.AdelicPlaneLevi.cA_cA σ hσ
  have e1 : t.1 * (t⁻¹).1 = 1 := t.mul_inv
  have e2 : cA σ (t⁻¹).1 * cA σ t.1 = 1 := by rw [← map_mul, t.inv_mul, map_one]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [dg, hypH, incM, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, hc, e1, e2]

end GlobalTheory.LineStabLevi

namespace GlobalTheory.LineStabLevi

open GlobalTheory.PlaneLeviExt GlobalTheory.PlaneLeviAt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {d d₁ : ℕ} {hd : d = d₁ + 2} {H : Plane E d d₁}

lemma map_mul_cA (σ : E →ₐ[F] E) {a b c : Type} [Fintype b] (X : Matrix a b (AE F E)) (Y : Matrix b c (AE F E)) :
    (X * Y).map (cA σ) = X.map (cA σ) * Y.map (cA σ) := Matrix.map_mul (f := (cA σ).toRingHom)

lemma gram_incM (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) (B : Base F E) {V : Spc F E d} {V₁ : Spc F E d₁}
    {i₀ i₁ r s : ℕ} (hV : V.IsHerm σ B r s) (hA : H.IsAdapted σ B V V₁ i₀ i₁) :
    (incM F (frame H))ᵀ * incM F V.J * (incM F (frame H)).map (cA σ) =
      incM F (Matrix.fromBlocks V₁.J 0 0 hypH) := by
  rw [← gram_frame_herm σ hσ B hV hA, incM_mul, incM_mul, incM_transpose, cA_incM]

lemma J_eq (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) (B : Base F E) {V : Spc F E d} {V₁ : Spc F E d₁}
    {i₀ i₁ r s : ℕ} (hV : V.IsHerm σ B r s) (hA : H.IsAdapted σ B V V₁ i₀ i₁) (hu : IsUnit (PlaneLeviExt.sq hd H)) :
    incM F V.J = (incM F (coframe hd H))ᵀ * incM F (Matrix.fromBlocks V₁.J 0 0 hypH) *
      (incM F (coframe hd H)).map (cA σ) := by
  have h1 : (incM F (frame H) * incM F (coframe hd H))ᵀ * incM F V.J *
      (incM F (frame H) * incM F (coframe hd H)).map (cA σ) = incM F V.J := by
    rw [S_T hu, Matrix.transpose_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, Matrix.mul_one]
  calc incM F V.J = (incM F (frame H) * incM F (coframe hd H))ᵀ * incM F V.J *
        (incM F (frame H) * incM F (coframe hd H)).map (cA σ) := h1.symm
    _ = (incM F (coframe hd H))ᵀ * ((incM F (frame H))ᵀ * incM F V.J * (incM F (frame H)).map (cA σ)) *
        (incM F (coframe hd H)).map (cA σ) := by
      rw [Matrix.transpose_mul, map_mul_cA]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [gram_incM σ hσ B hV hA]

lemma leviT_unitary_herm (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) (B : Base F E) {V : Spc F E d}
    {V₁ : Spc F E d₁} {i₀ i₁ r s : ℕ} (hV : V.IsHerm σ B r s) (hA : H.IsAdapted σ B V V₁ i₀ i₁)
    (hu : IsUnit (PlaneLeviExt.sq hd H)) (t : (AE F E)ˣ) (g : Matrix (Fin d₁) (Fin d₁) (AE F E))
    (hg : gᵀ * incM F V₁.J * g.map (cA σ) = incM F V₁.J) :
    (leviT σ hd H t g)ᵀ * incM F V.J * (leviT σ hd H t g).map (cA σ) = incM F V.J := by
  have hG := gram_incM σ hσ B hV hA
  have hJ := J_eq σ hσ B hV hA hu
  have hB : (blkT σ t g)ᵀ * incM F (Matrix.fromBlocks V₁.J 0 0 hypH) * (blkT σ t g).map (cA σ) =
      incM F (Matrix.fromBlocks V₁.J 0 0 hypH) := by
    have e1 : incM F (Matrix.fromBlocks V₁.J 0 0 (hypH (E := E))) =
        Matrix.fromBlocks (incM F V₁.J) 0 0 (incM F hypH) := by
      simp [incM, Matrix.fromBlocks_map]
    have e2 : (blkT σ t g).map (cA σ) = Matrix.fromBlocks (g.map (cA σ)) 0 0 ((dg σ t).map (cA σ)) := by
      rw [blkT, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _)]
    rw [e1, e2, blkT, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [hg, dg_unitary_herm σ hσ t]
  calc (leviT σ hd H t g)ᵀ * incM F V.J * (leviT σ hd H t g).map (cA σ)
      = (incM F (coframe hd H))ᵀ * ((blkT σ t g)ᵀ * ((incM F (frame H))ᵀ * incM F V.J *
          (incM F (frame H)).map (cA σ)) * (blkT σ t g).map (cA σ)) * (incM F (coframe hd H)).map (cA σ) := by
        simp only [leviT, Matrix.transpose_mul, map_mul_cA, Matrix.mul_assoc]
    _ = incM F V.J := by rw [hG, hB, ← hJ]

def frQ (hd : d = d₁ + 2) (H : Plane E d d₁) (P : Matrix (Fin d) (Fin d) (AE F E)) :
    Matrix (Fin d₁ ⊕ Fin 2) (Fin d₁ ⊕ Fin 2) (AE F E) :=
  incM F (coframe hd H) * P * incM F (frame H)

lemma frQ_unitary (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) (B : Base F E) {V : Spc F E d}
    {V₁ : Spc F E d₁} {i₀ i₁ r s : ℕ} (hV : V.IsHerm σ B r s) (hA : H.IsAdapted σ B V V₁ i₀ i₁)
    (hu : IsUnit (PlaneLeviExt.sq hd H)) (P : Matrix (Fin d) (Fin d) (AE F E))
    (hP : Pᵀ * incM F V.J * P.map (cA σ) = incM F V.J) :
    (frQ hd H P)ᵀ * incM F (Matrix.fromBlocks V₁.J 0 0 hypH) * (frQ hd H P).map (cA σ) =
      incM F (Matrix.fromBlocks V₁.J 0 0 hypH) := by
  have hG := gram_incM σ hσ B hV hA
  have hJ := J_eq σ hσ B hV hA hu
  calc _ = (incM F (frame H))ᵀ * (Pᵀ * ((incM F (coframe hd H))ᵀ * incM F (Matrix.fromBlocks V₁.J 0 0 hypH) *
        (incM F (coframe hd H)).map (cA σ)) * P.map (cA σ)) * (incM F (frame H)).map (cA σ) := by
        simp only [frQ, Matrix.transpose_mul, map_mul_cA, Matrix.mul_assoc]
    _ = _ := by rw [← hJ, Matrix.mul_assoc Pᵀ, ← Matrix.mul_assoc Pᵀ, hP, hG]

lemma frame_mulVec_single_eq_x : incM F (frame H) *ᵥ Pi.single (Sum.inr 0) 1 = incV F H.x := by
  ext i; simp [Matrix.mulVec_single, incM, frame, twoCols, incV]

lemma frQ_col (hu : IsUnit (PlaneLeviExt.sq hd H)) (P : Matrix (Fin d) (Fin d) (AE F E)) (c : AE F E)
    (hP : P *ᵥ incV F H.x = c • incV F H.x) :
    frQ hd H P *ᵥ Pi.single (Sum.inr 0) 1 = c • Pi.single (Sum.inr 0) 1 := by
  calc frQ hd H P *ᵥ Pi.single (Sum.inr 0) 1
      = incM F (coframe hd H) *ᵥ (P *ᵥ (incM F (frame H) *ᵥ Pi.single (Sum.inr 0) 1)) := by
        simp only [frQ, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = c • (incM F (coframe hd H) *ᵥ (incM F (frame H) *ᵥ Pi.single (Sum.inr 0) 1)) := by
        rw [frame_mulVec_single_eq_x, hP, Matrix.mulVec_smul]
    _ = c • Pi.single (Sum.inr 0) 1 := by rw [Matrix.mulVec_mulVec, T_S hu, Matrix.one_mulVec]

lemma row_of_col (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) (J₁ : Matrix (Fin d₁) (Fin d₁) E)
    (Q : Matrix (Fin d₁ ⊕ Fin 2) (Fin d₁ ⊕ Fin 2) (AE F E))
    (hQ : Qᵀ * incM F (Matrix.fromBlocks J₁ 0 0 hypH) * Q.map (cA σ) = incM F (Matrix.fromBlocks J₁ 0 0 hypH))
    (c : (AE F E)ˣ) (hc : Q *ᵥ Pi.single (Sum.inr 0) 1 = c.1 • Pi.single (Sum.inr 0) 1) (j : Fin d₁ ⊕ Fin 2) :
    Q (Sum.inr 1) j = cA σ (c⁻¹).1 * (Pi.single (Sum.inr 1) 1 : Fin d₁ ⊕ Fin 2 → AE F E) j := by
  have hcc := GlobalTheory.AdelicPlaneLevi.cA_cA σ hσ
  have h1 : (Pi.single (Sum.inr 0) 1 : Fin d₁ ⊕ Fin 2 → AE F E) ᵥ* (Qᵀ * incM F (Matrix.fromBlocks J₁ 0 0 hypH) * Q.map (cA σ)) =
      (Pi.single (Sum.inr 0) 1 : Fin d₁ ⊕ Fin 2 → AE F E) ᵥ* incM F (Matrix.fromBlocks J₁ 0 0 hypH) := by rw [hQ]
  rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, hc, Matrix.smul_vecMul,
    Matrix.smul_vecMul] at h1
  have he : (Pi.single (Sum.inr 0) 1 : Fin d₁ ⊕ Fin 2 → AE F E) ᵥ* incM F (Matrix.fromBlocks J₁ 0 0 hypH) =
      Pi.single (Sum.inr 1) 1 := by
    ext (k | k)
    · simp [Matrix.vecMul, dotProduct, Pi.single_apply, incM]
    · fin_cases k <;> simp [Matrix.vecMul, dotProduct, Pi.single_apply, incM, hypH]
  rw [he] at h1
  have h2 := congrFun h1 j
  have h3 : ((Pi.single (Sum.inr 1) 1 : Fin d₁ ⊕ Fin 2 → AE F E) ᵥ* Q.map (cA σ)) j = cA σ (Q (Sum.inr 1) j) := by
    simp [Matrix.vecMul, dotProduct, Pi.single_apply]
  rw [Pi.smul_apply, h3, smul_eq_mul] at h2
  have h4 : cA σ (Q (Sum.inr 1) j) = (c⁻¹).1 * (Pi.single (Sum.inr 1) 1 : Fin d₁ ⊕ Fin 2 → AE F E) j := by
    rw [← h2, ← mul_assoc, c.inv_mul, one_mul]
  have h5 := congrArg (cA σ) h4
  rw [hcc, map_mul] at h5
  rw [h5]
  congr 1
  by_cases hj : j = Sum.inr 1
  · subst hj; simp
  · simp [Pi.single_apply, hj]

end GlobalTheory.LineStabLevi

namespace GlobalTheory.LineStabLevi

open GlobalTheory.PlaneLeviExt GlobalTheory.PlaneLeviAt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {d d₁ : ℕ} {hd : d = d₁ + 2} {H : Plane E d d₁}

lemma frame_mulVec_split (v : Fin d₁ ⊕ Fin 2 → AE F E) :
    incM F (frame H) *ᵥ v = incM F H.ι *ᵥ (fun i => v (Sum.inl i)) + (v (Sum.inr 0) • incV F H.x + v (Sum.inr 1) • incV F H.y) := by
  rw [incM_frame, Matrix.fromCols_mulVec]
  congr 1
  ext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, incM, twoCols, incV]
  ring

lemma blk_mul_eq_one (Q Q' : Matrix (Fin d₁ ⊕ Fin 2) (Fin d₁ ⊕ Fin 2) (AE F E)) (h : Q * Q' = 1)
    (h0 : ∀ i, Q (Sum.inl i) (Sum.inr 0) = 0) (h1 : ∀ j, Q' (Sum.inr 1) (Sum.inl j) = 0) :
    Q.toBlocks₁₁ * Q'.toBlocks₁₁ = 1 := by
  ext i j
  have := congrFun (congrFun h (Sum.inl i)) (Sum.inl j)
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, h0, h1, zero_mul, mul_zero, add_zero,
    Matrix.one_apply, Sum.inl.injEq] at this
  simpa [Matrix.toBlocks₁₁, Matrix.mul_apply, Matrix.one_apply] using this

lemma blk_unitary (σ : E →ₐ[F] E) (J₁ : Matrix (Fin d₁) (Fin d₁) E)
    (Q : Matrix (Fin d₁ ⊕ Fin 2) (Fin d₁ ⊕ Fin 2) (AE F E))
    (hQ : Qᵀ * incM F (Matrix.fromBlocks J₁ 0 0 hypH) * Q.map (cA σ) = incM F (Matrix.fromBlocks J₁ 0 0 hypH))
    (h1 : ∀ j, Q (Sum.inr 1) (Sum.inl j) = 0) :
    (Q.toBlocks₁₁)ᵀ * incM F J₁ * (Q.toBlocks₁₁).map (cA σ) = incM F J₁ := by
  ext i j
  have := congrFun (congrFun hQ (Sum.inl i)) (Sum.inl j)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
    incM, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, map_zero, h1, mul_zero, zero_mul, add_zero, zero_add] at this
  simp only [hypH, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, map_zero, mul_zero, zero_mul, add_zero, zero_add] at this
  simpa [Matrix.toBlocks₁₁, Matrix.mul_apply, incM] using this

end GlobalTheory.LineStabLevi

namespace GlobalTheory.LineStabLevi

open GlobalTheory.PlaneLeviExt GlobalTheory.PlaneLeviAt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {d d₁ : ℕ} {hd : d = d₁ + 2} {H : Plane E d d₁}

lemma mat_mul_inv {σ : E →ₐ[F] E} {J : Matrix (Fin d) (Fin d) E} (h : UA σ J) : mat h * mat h⁻¹ = 1 := by
  show ((h.1 * (h⁻¹).1 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) = 1
  rw [← Subgroup.coe_mul, mul_inv_cancel]; rfl

lemma mat_inv_mul {σ : E →ₐ[F] E} {J : Matrix (Fin d) (Fin d) E} (h : UA σ J) : mat h⁻¹ * mat h = 1 := by
  show (((h⁻¹).1 * h.1 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) = 1
  rw [← Subgroup.coe_mul, inv_mul_cancel]; rfl

lemma mat_mul' {σ : E →ₐ[F] E} {J : Matrix (Fin d) (Fin d) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

lemma frQ_mul (hu : IsUnit (PlaneLeviExt.sq hd H)) (P P' : Matrix (Fin d) (Fin d) (AE F E)) :
    frQ hd H P * frQ hd H P' = frQ hd H (P * P') := by
  simp only [frQ, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (incM F (frame H)) (incM F (coframe hd H)), S_T hu, Matrix.one_mul]

lemma frQ_one (hu : IsUnit (PlaneLeviExt.sq hd H)) : frQ hd H (1 : Matrix (Fin d) (Fin d) (AE F E)) = 1 := by
  rw [frQ, Matrix.mul_one, T_S hu]

lemma frame_frQ (hu : IsUnit (PlaneLeviExt.sq hd H)) (P : Matrix (Fin d) (Fin d) (AE F E)) :
    incM F (frame H) * frQ hd H P = P * incM F (frame H) := by
  simp only [frQ, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (incM F (frame H)) (incM F (coframe hd H)), S_T hu, Matrix.one_mul]

lemma at_frQ {R : Type} [Zero R] (ev : AF F → R) (hu : IsUnit (PlaneLeviExt.sq hd H))
    (P : Matrix (Fin d) (Fin d) (AE F E)) (hP : At ev (P - 1)) : At ev (frQ hd H P - 1) := by
  have e : frQ hd H P - 1 = incM F (coframe hd H) * (P - 1) * incM F (frame H) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, T_S hu]; rfl
  rw [e]
  exact at_mul _ _ _ _ hP

lemma col_entry (Q : Matrix (Fin d₁ ⊕ Fin 2) (Fin d₁ ⊕ Fin 2) (AE F E)) (c : AE F E)
    (hc : Q *ᵥ Pi.single (Sum.inr 0) 1 = c • Pi.single (Sum.inr 0) 1) :
    (∀ i, Q (Sum.inl i) (Sum.inr 0) = 0) ∧ Q (Sum.inr 0) (Sum.inr 0) = c := by
  refine ⟨fun i => ?_, ?_⟩
  · have := congrFun hc (Sum.inl i)
    simpa [Matrix.mulVec_single] using this
  · have := congrFun hc (Sum.inr 0)
    simpa [Matrix.mulVec_single] using this

lemma mulVec_iota (hu : IsUnit (PlaneLeviExt.sq hd H)) (P : Matrix (Fin d) (Fin d) (AE F E))
    (h1 : ∀ j, frQ hd H P (Sum.inr 1) (Sum.inl j) = 0) (w : Fin d₁ → AE F E) :
    ∃ a : AE F E, P *ᵥ (incM F H.ι *ᵥ w) = incM F H.ι *ᵥ ((frQ hd H P).toBlocks₁₁ *ᵥ w) + a • incV F H.x := by
  have e0 : incM F (frame H) *ᵥ Sum.elim w 0 = incM F H.ι *ᵥ w := by
    rw [frame_mulVec_split]; simp
  refine ⟨(frQ hd H P *ᵥ Sum.elim w 0) (Sum.inr 0), ?_⟩
  rw [← e0, Matrix.mulVec_mulVec, ← frame_frQ hu, ← Matrix.mulVec_mulVec, frame_mulVec_split]
  have e1 : (frQ hd H P *ᵥ Sum.elim w 0) (Sum.inr 1) = 0 := by
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, h1]
  have e2 : (fun i => (frQ hd H P *ᵥ Sum.elim w 0) (Sum.inl i)) = (frQ hd H P).toBlocks₁₁ *ᵥ w := by
    funext i
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₁₁]
  rw [e1, e2, zero_smul, add_zero]

theorem levi_decomp {R : Type} [Zero R] (ev : AF F → R) (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) (B : Base F E)
    {V : Spc F E d} {V₁ : Spc F E d₁} {i₀ i₁ r s r₁ s₁ : ℕ} (hV : V.IsHerm σ B r s) (hV₁ : V₁.IsHerm σ B r₁ s₁)
    (hA : H.IsAdapted σ B V V₁ i₀ i₁) (p : UA σ V.J) (hp : p ∈ UAt σ V ev) (t : (AE F E)ˣ)
    (hx : mat p *ᵥ incV F H.x = t.1 • incV F H.x) :
    t ∈ idelesAt E ev ∧ ∃ (n m : UA σ V.J) (g₀ : UA σ V₁.J), n ∈ unip σ V H ∧ n ∈ UAt σ V ev ∧
      IsLevi (W₁ := V₁) H t g₀ m ∧ m ∈ UAt σ V ev ∧ g₀ ∈ UAt σ V₁ ev ∧ p = n * m := by
  have hu := isUnit_sq_herm σ hσ B hV hV₁ hA
  have hx' : mat p⁻¹ *ᵥ incV F H.x = (t⁻¹).1 • incV F H.x := by
    have h := congrArg (fun v => (t⁻¹).1 • (mat p⁻¹ *ᵥ v)) hx
    simp only [Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec, Matrix.mulVec_smul, smul_smul, t.inv_mul,
      one_smul] at h
    exact h.symm
  set Q := frQ hA.rank H (mat p) with hQd
  set Q' := frQ hA.rank H (mat p⁻¹) with hQd'
  have hQu := frQ_unitary σ hσ B hV hA hu (mat p) p.2
  have hQu' := frQ_unitary σ hσ B hV hA hu (mat p⁻¹) (p⁻¹).2
  have hc := frQ_col hu (mat p) _ hx
  have hc' := frQ_col hu (mat p⁻¹) _ hx'
  have hr : ∀ j, Q (Sum.inr 1) (Sum.inl j) = 0 := fun j => by
    rw [hQd, row_of_col σ hσ V₁.J _ hQu t hc]; simp
  have hr' : ∀ j, Q' (Sum.inr 1) (Sum.inl j) = 0 := fun j => by
    rw [hQd', row_of_col σ hσ V₁.J _ hQu' t⁻¹ hc']; simp
  have hQQ : Q * Q' = 1 := by rw [hQd, hQd', frQ_mul hu, mat_mul_inv, frQ_one hu]
  have hQQ' : Q' * Q = 1 := by rw [hQd, hQd', frQ_mul hu, mat_inv_mul, frQ_one hu]
  have hAA := blk_mul_eq_one Q Q' hQQ (col_entry _ _ hc).1 hr'
  have hAA' := blk_mul_eq_one Q' Q hQQ' (col_entry _ _ hc').1 hr
  have hAu := blk_unitary σ V₁.J Q hQu hr
  have hatQ : At ev (Q - 1) := at_frQ ev hu _ hp
  have hatt : At ev (t.1 - 1) := fun u hu0 => by
    have := congrFun (congrFun (hatQ u hu0) (Sum.inr 0)) (Sum.inr 0)
    rw [Matrix.smul_apply, Matrix.sub_apply, hQd, (col_entry _ _ hc).2, Matrix.one_apply_eq] at this
    exact this
  have hatA : At ev (Q.toBlocks₁₁ - 1) := fun u hu0 => by
    ext i j
    have := congrFun (congrFun (hatQ u hu0) (Sum.inl i)) (Sum.inl j)
    simpa [Matrix.toBlocks₁₁, Matrix.one_apply] using this
  let gU : GL (Fin d₁) (AE F E) := ⟨Q.toBlocks₁₁, Q'.toBlocks₁₁, hAA, hAA'⟩
  have hgmem : gU ∈ UG (cA σ) (incM F V₁.J) := hAu
  let mU : GL (Fin d) (AE F E) := ⟨leviT σ hA.rank H t Q.toBlocks₁₁, leviT σ hA.rank H t⁻¹ Q'.toBlocks₁₁,
    by rw [leviT_mul σ hu, hAA, mul_inv_cancel, leviT_one σ hu],
    by rw [leviT_mul σ hu, hAA', inv_mul_cancel, leviT_one σ hu]⟩
  have hmem : mU ∈ UG (cA σ) (incM F V.J) := leviT_unitary_herm σ hσ B hV hA hu t _ hAu
  let m : UA σ V.J := ⟨mU, hmem⟩
  have hm : mat m = leviT σ hA.rank H t Q.toBlocks₁₁ := rfl
  have hm' : mat m⁻¹ = leviT σ hA.rank H t⁻¹ Q'.toBlocks₁₁ := rfl
  have hatm : At ev (mat m - 1) := by
    have e : leviT σ hA.rank H t Q.toBlocks₁₁ - 1 =
        incM F (frame H) * (blkT σ t Q.toBlocks₁₁ - 1) * incM F (coframe hA.rank H) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, S_T hu]; rfl
    rw [hm, e]
    exact at_mul _ _ _ _ (at_blkT _ σ t _ hatt hatA)
  obtain ⟨k1, -, k3⟩ := leviT_cols σ _ t⁻¹ Q'.toBlocks₁₁ (leviT_frame σ hu t⁻¹ Q'.toBlocks₁₁)
  refine ⟨hatt, p * m⁻¹, m, ⟨gU, hgmem⟩, Subgroup.subset_closure ⟨?_, fun z => ?_⟩, ?_,
    leviT_cols σ _ t _ (leviT_frame σ hu t _), hatm, hatA, (inv_mul_cancel_right p m).symm⟩
  · rw [mat_mul', ← Matrix.mulVec_mulVec, hm', k1, Matrix.mulVec_smul, hx, smul_smul, t.inv_mul, one_smul]
  · obtain ⟨a, ha⟩ := mulVec_iota hu (mat p) hr (Q'.toBlocks₁₁ *ᵥ z)
    refine ⟨a, ?_⟩
    rw [mat_mul', ← Matrix.mulVec_mulVec, hm', Matrix.mulVec_mulVec z, k3, ← Matrix.mulVec_mulVec, ha,
      Matrix.mulVec_mulVec z, hAA, Matrix.one_mulVec]
  · intro u hu0
    have e : mat (p * m⁻¹) - 1 = (mat p - 1) * mat m⁻¹ - (mat m - 1) * mat m⁻¹ := by
      rw [mat_mul', Matrix.sub_mul, Matrix.sub_mul, mat_mul_inv, Matrix.one_mul]; abel
    rw [e, smul_sub, ← Matrix.smul_mul, ← Matrix.smul_mul, hp u hu0, hatm u hu0, sub_self]

theorem stab_line_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ p ∈ UAt σ G.V' (evI F), ∀ t : (AE F E)ˣ, mat p *ᵥ incV F H.x = t.1 • incV F H.x →
      t ∈ idelesAt E (evI F) ∧ ∃ (n m : UA σ G.V'.J) (g₀ : UA σ G₁.V'.J), n ∈ unip σ G.V' H ∧ n ∈ UAt σ G.V' (evI F) ∧
        IsLevi (W₁ := G₁.V') H t g₀ m ∧ m ∈ UAt σ G.V' (evI F) ∧ g₀ ∈ UAt σ G₁.V' (evI F) ∧ p = n * m := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ p hp t hx
  exact levi_decomp (evI F) σ (GlobalTheory.AdelicPlaneLevi.sigma_invol hT.base.cm) B hT.geo.hV' hT₁.geo.hV' hC.hH p hp t hx

end GlobalTheory.LineStabLevi
