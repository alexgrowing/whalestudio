import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemImLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingExistsDoublingConfiguration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCoordinateAdditive

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.UnipConj.MulLaw

open Matrix GlobalTheory.ThK.UnipDom GlobalTheory.LeviElem

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem fA_mulVec_left (σ : E →ₐ[F] E) {n : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
    (J : Matrix (Fin n) (Fin n) E) (M : Matrix (Fin n) κ (AE F E)) (u : κ → AE F E) (w : Fin n → AE F E) :
    fA σ J (M *ᵥ u) w = ∑ k, u k * fA σ J (M *ᵥ Pi.single k (1 : AE F E)) w := by
  simp only [fA, mulVec_single_one]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  conv_rhs => enter [2, x1]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  simp only [Matrix.col_apply]
  ring

theorem fA_gram (σ : E →ₐ[F] E) {b : ℕ} (J : Matrix (Fin (b + 2)) (Fin (b + 2)) E) (J₁ : Matrix (Fin b) (Fin b) E)
    (P : Matrix (Fin (b + 2)) (Fin b ⊕ Fin 2) (AE F E))
    (hK : Pᵀ * incM F J * P.map (cA σ) = fromBlocks (incM F J₁) 0 0 swap2) (u u' : Fin b ⊕ Fin 2 → AE F E) :
    fA σ J (P *ᵥ u) (P *ᵥ u') = (fun i => u (Sum.inl i)) ⬝ᵥ (incM F J₁ *ᵥ fun i => cA σ (u' (Sum.inl i))) +
      u (Sum.inr 0) * cA σ (u' (Sum.inr 1)) + u (Sum.inr 1) * cA σ (u' (Sum.inr 0)) := by
  have h1 : (fun i => cA σ ((P *ᵥ u') i)) = P.map (cA σ) *ᵥ fun i => cA σ (u' i) := by
    funext i; simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  unfold fA
  rw [h1, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul,
    ← Matrix.mul_assoc, hK, ← Matrix.dotProduct_mulVec]
  simp [dotProduct, Fintype.sum_sum_type, fromBlocks_mulVec, swap2, Fin.sum_univ_two, Matrix.mulVec]
  ring

theorem fA_mat (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : UA σ J) (v w : Fin n → AE F E) :
    fA σ J (mat g *ᵥ v) (mat g *ᵥ w) = fA σ J v w := by
  have hg : (mat g)ᵀ * incM F J * (mat g).map (cA σ) = incM F J := g.2
  have h1 : (fun i => cA σ ((mat g *ᵥ w) i)) = (mat g).map (cA σ) *ᵥ fun i => cA σ (w i) := by
    funext i; simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  unfold fA
  rw [h1, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul,
    ← Matrix.mul_assoc, hg, ← Matrix.dotProduct_mulVec]

end GlobalTheory.UnipConj.MulLaw

namespace GlobalTheory.UnipConj.MulLaw

open Matrix GlobalTheory.ThK.UnipDom GlobalTheory.LeviElem GlobalTheory.ThK.UnipDom.Additive

theorem coA_coC_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∀ n₁ ∈ unip σ G.V H, ∀ n₂ ∈ unip σ G.V H,
    GlobalTheory.ThK.UnipDom.coA σ G.V.J H (n₁ * n₂) = GlobalTheory.ThK.UnipDom.coA σ G.V.J H n₁ + GlobalTheory.ThK.UnipDom.coA σ G.V.J H n₂ ∧
    GlobalTheory.ThK.UnipDom.coC σ G.V.J H (n₁ * n₂) = GlobalTheory.ThK.UnipDom.coC σ G.V.J H n₁ + GlobalTheory.ThK.UnipDom.coC σ G.V.J H n₂ +
      GlobalTheory.ThK.UnipDom.coA σ G.V.J H n₁ ⬝ᵥ GlobalTheory.UnipConj.betaOf σ G₁.V.J (GlobalTheory.ThK.UnipDom.coA σ G.V.J H n₂) := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC hB hG hG₁ n₁ hn₁ n₂ hn₂
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ z, σ (σ z) = z := fun z => (B.emb w).1.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have hdet : G₁.V.J.det ≠ 0 := by
    have h := det_ne_of_sig _ (hG₁.hV.sig w)
    intro h0
    apply h
    have : (G₁.V.J.map (B.emb w).1).det = (B.emb w).1 G₁.V.J.det := (RingHom.map_det (B.emb w).1 _).symm
    rw [this, h0, map_zero]
  set P := fromCols H.ι (cols2 H.x H.y) with hP
  have hK : Pᵀ * G.V.J * P.map σ = fromBlocks G₁.V.J 0 0 swap2 := gram_block σ hσ B hG.hV.herm hC.hH
  set K : Matrix (Fin b ⊕ Fin 2) (Fin b ⊕ Fin 2) E := fromBlocks G₁.V.J 0 0 swap2 with hKdef
  have hKdet : IsUnit Kᵀ.det := by
    rw [det_transpose, hKdef, det_fromBlocks_zero₂₁]
    simp [swap2, det_fin_two, hdet]
  set Q := (Kᵀ)⁻¹ * ((P.map σ)ᵀ * G.V.Jᵀ) with hQ
  have hQP : Q * P = 1 := by
    have : (P.map σ)ᵀ * G.V.Jᵀ * P = Kᵀ := by
      rw [← hK]; simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [hQ, Matrix.mul_assoc, this, nonsing_inv_mul _ hKdet]
  set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf
  have hcf : ∀ e, cA σ (f e) = f (σ e) := fun e => by simp [cA, hf, inclR]
  set Pa := fromCols (incM F H.ι) (cols2 (incV F H.x) (incV F H.y)) with hPa
  have hPf : P.map f = Pa := by
    ext i (j | j)
    · rfl
    · fin_cases j <;> rfl
  have hQP' : Q.map f * Pa = 1 := by
    rw [← hPf, ← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero f) (map_one f)]
  have hPQ' : Pa * Q.map f = 1 := (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 hQP'
  have hK' : Paᵀ * incM F G.V.J * Pa.map (cA σ) = fromBlocks (incM F G₁.V.J) 0 0 swap2 := by
    rw [← hPf]
    have h1 : (P.map f).map (cA σ) = (P.map σ).map f := by
      ext i j; simp [hcf]
    have h2 : incM F G.V.J = G.V.J.map f := rfl
    rw [h1, h2, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hK, hKdef, fromBlocks_map]
    congr 1
    · simp
    · simp
    · ext i j; fin_cases i <;> fin_cases j <;> simp [swap2]

  have hX : Pa *ᵥ Pi.single (Sum.inr 0) 1 = incV F H.x := by
    rw [mulVec_single_one]; ext i; simp [Pa, cols2, Matrix.col]
  have hY : Pa *ᵥ Pi.single (Sum.inr 1) 1 = incV F H.y := by
    rw [mulVec_single_one]; ext i; simp [Pa, cols2, Matrix.col]
  have hI : ∀ j, Pa *ᵥ Pi.single (Sum.inl j) 1 = incM F H.ι *ᵥ Pi.single j 1 := by
    intro j; rw [mulVec_single_one, mulVec_single_one]; ext i; simp [Pa, Matrix.col]
  have gr := fA_gram σ G.V.J G₁.V.J Pa hK'
  have fXY : fA σ G.V.J (incV F H.x) (incV F H.y) = 1 := by rw [← hX, ← hY, gr]; simp [← Pi.zero_def]
  have fPY : ∀ u, fA σ G.V.J (Pa *ᵥ u) (incV F H.y) = u (Sum.inr 0) := by intro u; rw [← hY, gr]; simp [← Pi.zero_def]
  have fPX : ∀ u, fA σ G.V.J (Pa *ᵥ u) (incV F H.x) = u (Sum.inr 1) := by intro u; rw [← hX, gr]; simp [← Pi.zero_def]
  have hval : ∀ (j : Fin b) (c : AE F E),
      fA σ G.V.J (incM F H.ι *ᵥ Pi.single j 1 + c • incV F H.x) (incV F H.y) = c := by
    intro j c
    rw [fA_add_left, fA_smul_left, ← hI, fPY, fXY]; simp [← Pi.zero_def]
  have coord : ∀ n ∈ unip σ G.V H, ∃ u : Fin b ⊕ Fin 2 → AE F E, mat n *ᵥ incV F H.y = Pa *ᵥ u ∧
      u (Sum.inr 0) = coC σ G.V.J H n ∧ u (Sum.inr 1) = 1 ∧
      (fun i => u (Sum.inl i)) = betaOf σ G₁.V.J (coA σ G.V.J H n) := by
    intro n hn
    have hnx := (unip_spec hn).1
    obtain ⟨u, hu⟩ : ∃ u, mat n *ᵥ incV F H.y = Pa *ᵥ u :=
      ⟨Q.map f *ᵥ (mat n *ᵥ incV F H.y), by rw [Matrix.mulVec_mulVec, hPQ', Matrix.one_mulVec]⟩
    have hs : u (Sum.inr 0) = coC σ G.V.J H n := by
      simp only [coC]; rw [hu, fPY]
    have ht : u (Sum.inr 1) = 1 := by
      have h := fA_mat σ G.V.J n (incV F H.y) (incV F H.x)
      rw [hnx, hu, fPX, ← hX, ← hY, gr] at h
      simpa [← Pi.zero_def] using h
    refine ⟨u, hu, hs, ht, ?_⟩
    have hJ : incM F G₁.V.J *ᵥ (fun i => cA σ (u (Sum.inl i))) = -coA σ G.V.J H n := by
      funext j
      obtain ⟨a, ha⟩ := (unip_spec hn).2 (Pi.single j 1)
      have hcoA : coA σ G.V.J H n j = a := by simp only [coA]; rw [ha, hval]
      have h0 : fA σ G.V.J (incM F H.ι *ᵥ Pi.single j 1) (incV F H.y) = 0 := by rw [← hI, fPY]; simp [← Pi.zero_def]
      have h := fA_mat σ G.V.J n (incM F H.ι *ᵥ Pi.single j 1) (incV F H.y)
      rw [ha, hu, h0, fA_add_left, fA_smul_left, ← hI, ← hX, gr, gr, ht] at h
      simp [← Pi.zero_def] at h
      have hsl : (fun i => (Pi.single (Sum.inl j) (1 : AE F E) : Fin b ⊕ Fin 2 → AE F E) (Sum.inl i)) = Pi.single j 1 := by
        funext i; simp [Pi.single_apply]
      rw [hsl, single_dotProduct, one_mul] at h
      rw [Pi.neg_apply, hcoA]
      linear_combination h
    funext i
    have hinv : incM F G₁.V.J⁻¹ * incM F G₁.V.J = 1 := by
      show G₁.V.J⁻¹.map f * G₁.V.J.map f = 1
      rw [← Matrix.map_mul, nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet), Matrix.map_one _ (map_zero f) (map_one f)]
    have hb : incM F G₁.V.J⁻¹ *ᵥ coA σ G.V.J H n = -(fun i => cA σ (u (Sum.inl i))) := by
      rw [← neg_neg (coA σ G.V.J H n), ← hJ, Matrix.mulVec_neg, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    simp [betaOf, hb, cA_invol hσ]
  refine ⟨?_, ?_⟩
  · funext j
    obtain ⟨a, ha⟩ := (unip_spec hn₁).2 (Pi.single j 1)
    obtain ⟨c, hc⟩ := (unip_spec hn₂).2 (Pi.single j 1)
    have hux := (unip_spec hn₁).1
    have huv : mat (n₁ * n₂) *ᵥ (incM F H.ι *ᵥ Pi.single j 1) = incM F H.ι *ᵥ Pi.single j 1 + (a + c) • incV F H.x := by
      rw [mat_mul', ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_add, Matrix.mulVec_smul, hux, ha, add_smul, add_assoc]
    simp only [Pi.add_apply, coA]
    rw [huv, hval, ha, hval, hc, hval]
  · obtain ⟨u₂, hu₂, hs₂, ht₂, hp₂⟩ := coord n₂ hn₂
    have hc1 : fA σ G.V.J (mat n₁ *ᵥ incV F H.x) (incV F H.y) = 1 := by rw [(unip_spec hn₁).1, fXY]
    have hsum : coC σ G.V.J H (n₁ * n₂) =
        ∑ k, u₂ k * fA σ G.V.J (mat n₁ *ᵥ (Pa *ᵥ Pi.single k 1)) (incV F H.y) := by
      simp only [coC]
      rw [mat_mul', ← Matrix.mulVec_mulVec, hu₂, Matrix.mulVec_mulVec, fA_mulVec_left]
      simp only [Matrix.mulVec_mulVec]
    rw [hsum, Fintype.sum_sum_type, Fin.sum_univ_two, hX, hY, hc1, hs₂, ht₂]
    simp only [hI]
    rw [← hp₂]
    have hdot : coA σ G.V.J H n₁ ⬝ᵥ (fun i => u₂ (Sum.inl i)) =
        ∑ x, u₂ (Sum.inl x) * fA σ G.V.J (mat n₁ *ᵥ (incM F H.ι *ᵥ Pi.single x 1)) (incV F H.y) := by
      simp only [dotProduct, coA]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    rw [hdot]; simp only [coC]; ring

end GlobalTheory.UnipConj.MulLaw
