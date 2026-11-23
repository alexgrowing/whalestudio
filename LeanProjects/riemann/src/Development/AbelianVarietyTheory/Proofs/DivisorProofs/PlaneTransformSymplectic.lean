import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacGlueIndicator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzNe
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneCo

noncomputable section
namespace GlobalTheory.ThK.PlaneForm
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem trace_bE_bE' (i j : Fin (Module.finrank F E)) :
    Algebra.trace F E (bE F E i * bE' F E j) = if i = j then 1 else 0 := by
  have h := LinearMap.BilinForm.apply_dualBasis_left (B := Algebra.traceForm F E) (traceForm_nondegenerate F E) (bE F E) j i
  rw [Algebra.traceForm_apply] at h
  rw [mul_comm]
  exact h

theorem sum_repr_mul (a b : AE F E) :
    ∑ i, (bA F E).repr a i * (bA' F E).repr b i = Algebra.trace (AF F) (AE F E) (a * b) := by
  conv_rhs => rw [← (bA F E).sum_repr a, ← (bA' F E).sum_repr b]
  rw [Finset.sum_mul_sum, map_sum]
  have hb : ∀ i j, Algebra.trace (AF F) (AE F E) (bA F E i * bA' F E j) = if i = j then 1 else 0 := by
    intro i j
    rw [bA, bA', Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have := GlobalTheory.VacIndic.trace_inclR (F := F) (E := E) (bE F E i * bE' F E j)
    rw [trace_bE_bE'] at this
    split_ifs at this ⊢ <;> simpa [inclR] using this
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_sum, smul_mul_smul_comm, map_smul, hb, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem planeMat_eq_frame {n n₁ : ℕ} (H : Plane E n n₁) : planeMat H = GlobalTheory.ThK.Adapt.frame H := by
  ext i (j | t)
  · rfl
  · fin_cases t <;> rfl

theorem planeMat_mul_planeCoef {σ : E →ₐ[F] E} {B : Base F E} {n n₁ i₀ i₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁}
    {H : Plane E n n₁} (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) (hL : Y.L.IsLattice E) : planeMat H * planeCoef H = 1 := by
  obtain ⟨Q, h1, -, -⟩ := GlobalTheory.ThK.Adapt.exists_frame_inv hH hL
  have hr : n₁ + 2 = n := hH.rank.symm
  have hM : (planeMat H).submatrix id (finSumFinEquiv.trans (finCongr hr)).symm *
      Q.submatrix (finSumFinEquiv.trans (finCongr hr)).symm id = 1 := by
    rw [Matrix.submatrix_mul_equiv _ _ _ (finSumFinEquiv.trans (finCongr hr)).symm, planeMat_eq_frame, h1]
    rfl
  have hC : planeCoef H = Q := by
    rw [planeCoef, dif_pos hr, Matrix.inv_eq_right_inv hM]
    ext i j
    simp
  rw [hC, planeMat_eq_frame, h1]

theorem sum_sI_mul_pairI (σ : E →ₐ[F] E) {n d n₁ d₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (H : Plane E n n₁) (H' : Plane E d d₁)
    (hGX : planeGram σ X.J H = Matrix.fromBlocks X₁.J 0 0 !![0, 1; 1, 0])
    (hGW : planeGram σ W.J H' = Matrix.fromBlocks W₁.J 0 0 !![0, 1; -1, 0]) (w w' : Matrix (Fin n) (Fin d) (AE F E)) :
    ∑ k, sI H H' w k * pairI σ X W H H' w' k =
      -((∑ j, ∑ l, coefLin H H' w (.inr 1) j * incM F (planeGram σ W.J H') j l * cA σ (coefLin H H' w' (.inr 0) l)) -
        ∑ i, ∑ k, coefLin H H' w (.inl i) (.inr 1) * incM F X₁.J i k * cA σ (coefLin H H' w' (.inl k) (.inr 0))) := by
  simp only [pairI, sI, tI, hGX, hGW, Fintype.sum_sum_type, Fin.sum_univ_two, posS, posT, incM, Matrix.map_apply,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
  simp only [map_mul, map_zero, map_one, map_neg, zero_mul, mul_zero, one_mul, mul_one, neg_mul, Finset.sum_const_zero,
    add_zero, zero_add, Finset.mul_sum, Finset.sum_neg_distrib, mul_neg, Finset.sum_add_distrib]
  simp only [neg_zero, zero_add, add_zero, mul_neg, neg_neg, Finset.mul_sum, Finset.sum_neg_distrib, mul_assoc, neg_add]
  ring

theorem gram_conj (σ : E →ₐ[F] E) (hσ : ∀ x : E, σ (σ x) = x) {m : ℕ} {κ : Type} [Fintype κ] {J : Matrix (Fin m) (Fin m) E}
    {η : E} (hJ : ∀ i j, σ (J j i) = η * J i j) (P : Matrix (Fin m) κ E) (i j : κ) :
    σ ((Pᵀ * J * P.map σ) j i) = η * (Pᵀ * J * P.map σ) i j := by
  have he : ∀ a b, (Pᵀ * J * P.map σ) a b = ∑ i, ∑ k, P i a * J i k * σ (P k b) := fun a b => by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    exact Finset.sum_comm
  rw [he, he, GlobalTheory.ThK.Adapt.conj_pair σ hσ hJ]

theorem incM_plane {α : Type} [Fintype α] (A : Matrix α α E) (η : E) :
    incM F (Matrix.fromBlocks A 0 0 !![0, 1; η, 0]) =
      Matrix.fromBlocks (incM F A) 0 0 !![0, 1; inclR (F := F) (AF F) η, 0] := by
  ext (i | i) (j | j)
  · rfl
  · simp [incM]
  · simp [incM]
  · fin_cases i <;> fin_cases j <;> simp [incM]

theorem form_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (H : Plane E n n₁) (H' : Plane E d d₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ w w' : Matrix (Fin n) (Fin d) (AE F E),
    symp (cA σ) (-1) (incM F X.J) (incM F W.J) w w' =
      (planeT σ X W H H' w).1.1 ⬝ᵥ (planeT σ X W H H' w').1.2 - (planeT σ X W H H' w').1.1 ⬝ᵥ (planeT σ X W H H' w).1.2 +
        symp (cA σ) (-1) (incM F X₁.J) (incM F W₁.J) (planeT σ X W H H' w).2 (planeT σ X W H H' w').2 := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' hB hX hW hH hH' w w'
  have hσ : ∀ x : E, σ (σ x) = x := GlobalTheory.ThK.Adapt.conj_conj hB
  have hc : ∀ z, cA σ (cA σ z) = z := GlobalTheory.ThK.Adapt.cA_cA hB
  have hP := planeMat_mul_planeCoef hH hX.lat
  have hQ := planeMat_mul_planeCoef hH' hW.lat
  have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h1' : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hrec : ∀ z, z = incM F (planeMat H) * coefLin (F := F) H H' z * (incM F (planeMat H'))ᵀ := fun z => by
    simp only [coefLin, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← GlobalTheory.ThK.Adapt.incM_mul, hP, h1, Matrix.one_mul, Matrix.mul_assoc,
      ← Matrix.transpose_mul, ← GlobalTheory.ThK.Adapt.incM_mul, hQ, h1', Matrix.transpose_one, Matrix.mul_one]
  have hg : ∀ {m m₁ : ℕ} (J : Matrix (Fin m) (Fin m) E) (P : Matrix (Fin m) (Fin m₁ ⊕ Fin 2) E),
      (incM F P)ᵀ * incM F J * (incM F P).map (cA σ) = incM F (Pᵀ * J * P.map σ) := by
    intro m m₁ J P
    rw [GlobalTheory.ThK.Adapt.incM_mul, GlobalTheory.ThK.Adapt.incM_mul]
    rfl
  have hT : ∀ z z', hTens (cA σ) (incM F X.J) (incM F W.J) z z' = hTens (cA σ) (incM F (planeGram σ X.J H))
      (incM F (planeGram σ W.J H')) (coefLin (F := F) H H' z) (coefLin (F := F) H H' z') := fun z z' => by
    conv_lhs => rw [hrec z, hrec z']
    refine (GlobalTheory.ThK.Adapt.hTens_mul (cA σ) _ _ _ _ _ _).trans ?_
    rw [hg, hg]
    rfl
  have hGX : planeGram σ X.J H = Matrix.fromBlocks X₁.J 0 0 !![0, 1; 1, 0] := by
    rw [planeGram, planeMat_eq_frame]
    exact GlobalTheory.ThK.Adapt.frame_gram hB hH (one_mul 1) (fun i j => by rw [hX.herm, one_mul])
  have hGW : planeGram σ W.J H' = Matrix.fromBlocks W₁.J 0 0 !![0, 1; -1, 0] := by
    rw [planeGram, planeMat_eq_frame]
    exact GlobalTheory.ThK.Adapt.frame_gram hB hH' (by norm_num) (fun i j => by rw [hW.skew]; ring)
  have hsX : ∀ i j, cA σ (incM F X₁.J j i) = 1 * incM F X₁.J i j := fun i j => by
    have := gram_conj σ hσ (J := X.J) (η := 1) (fun i j => by rw [hX.herm, one_mul]) (planeMat H) (.inl i) (.inl j)
    rw [← planeGram, hGX] at this
    simp only [Matrix.fromBlocks_apply₁₁] at this
    simp only [incM, Matrix.map_apply, GlobalTheory.VacIndic.cA_inclR, this, one_mul]
  have hsW : ∀ i j, cA σ (incM F (planeGram σ W.J H') j i) = -1 * incM F (planeGram σ W.J H') i j := fun i j => by
    have := gram_conj σ hσ (J := W.J) (η := -1) (fun i j => by rw [hW.skew]; ring) (planeMat H') i j
    rw [← planeGram] at this
    simp only [incM, Matrix.map_apply, GlobalTheory.VacIndic.cA_inclR, this, map_mul, map_neg, map_one]
  have hpq : ∀ z z', (planeT σ X W H H' z).1.1 ⬝ᵥ (planeT σ X W H H' z').1.2 =
      Algebra.trace (AF F) (AE F E) (∑ k, sI H H' z k * pairI σ X W H H' z' k) := by
    intro z z'
    simp only [planeT, LinearMap.coe_mk, AddHom.coe_mk, dotProduct, Fintype.sum_prod_type, sum_repr_mul, map_sum]
  have hR : ∀ z z' : Matrix (Fin n₁) (Fin d₁ ⊕ Fin 2) (AE F E),
      hTens (cA σ) (incM F X₁.J) (incM F (planeGram σ W.J H')) z z' =
        -1 * ∑ i, ∑ k, z i (.inr 1) * incM F X₁.J i k * cA σ (z' k (.inr 0)) +
          ∑ i, ∑ k, z i (.inr 0) * incM F X₁.J i k * cA σ (z' k (.inr 1)) +
          hTens (cA σ) (incM F X₁.J) (incM F W₁.J) (z.submatrix id .inl) (z'.submatrix id .inl) := by
    intro z z'
    rw [hGW, incM_plane, GlobalTheory.ThK.Adapt.hTens_plane_right, map_neg, map_one]
  have hL : ∀ z z', hTens (cA σ) (incM F (planeGram σ X.J H)) (incM F (planeGram σ W.J H')) z z' =
      ∑ j, ∑ l, z (.inr 1) j * incM F (planeGram σ W.J H') j l * cA σ (z' (.inr 0) l) +
        ∑ j, ∑ l, z (.inr 0) j * incM F (planeGram σ W.J H') j l * cA σ (z' (.inr 1) l) +
        hTens (cA σ) (incM F X₁.J) (incM F (planeGram σ W.J H')) (z.submatrix .inl id) (z'.submatrix .inl id) := by
    intro z z'
    rw [hGX, incM_plane, GlobalTheory.ThK.Adapt.hTens_plane_left, map_one, one_mul]
  have hkey : ∀ z z' : Matrix (Fin n₁ ⊕ Fin 2) (Fin d₁ ⊕ Fin 2) (AE F E),
      cA σ (∑ j, ∑ l, z (.inr 0) j * incM F (planeGram σ W.J H') j l * cA σ (z' (.inr 1) l) +
        ∑ i, ∑ k, z (.inl i) (.inr 0) * incM F X₁.J i k * cA σ (z' (.inl k) (.inr 1))) =
      -((∑ j, ∑ l, z' (.inr 1) j * incM F (planeGram σ W.J H') j l * cA σ (z (.inr 0) l)) -
        ∑ i, ∑ k, z' (.inl i) (.inr 1) * incM F X₁.J i k * cA σ (z (.inl k) (.inr 0))) := by
    intro z z'
    have e1 := GlobalTheory.ThK.Adapt.conj_pair (cA σ) hc hsW (fun j => z (.inr 0) j) (fun j => z' (.inr 1) j)
    have e2 := GlobalTheory.ThK.Adapt.conj_pair (cA σ) hc hsX (fun i => z (.inl i) (.inr 0)) (fun i => z' (.inl i) (.inr 1))
    rw [map_add, e1, e2]
    ring
  have htr := GlobalTheory.VacCocycle.trace_conj (R := AF F) (cA σ) hc
  rw [hpq, hpq, sum_sI_mul_pairI σ X W X₁ W₁ H H' hGX hGW, sum_sI_mul_pairI σ X W X₁ W₁ H H' hGX hGW, ← hkey (coefLin (F := F) H H' w) (coefLin (F := F) H H' w'), htr]
  unfold symp
  rw [hT, hL, hR]
  rw [← map_sub, ← map_add]
  refine congrArg (Algebra.trace (AF F) (AE F E)) ?_
  show _ = _ + -1 * hTens (cA σ) (incM F X₁.J) (incM F W₁.J) ((coefLin H H' w).submatrix Sum.inl Sum.inl)
    ((coefLin H H' w').submatrix Sum.inl Sum.inl)
  have hs : ∀ z : Matrix (Fin n₁ ⊕ Fin 2) (Fin d₁ ⊕ Fin 2) (AE F E),
      (z.submatrix Sum.inl id).submatrix id Sum.inl = z.submatrix Sum.inl Sum.inl := fun z => rfl
  simp only [hs, sI, Matrix.submatrix_apply, id_eq]
  ring

end GlobalTheory.ThK.PlaneForm
