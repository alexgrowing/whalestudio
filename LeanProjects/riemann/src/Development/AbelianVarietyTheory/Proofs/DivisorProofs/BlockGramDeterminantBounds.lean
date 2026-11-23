import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelHodgeGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedSqInverseTransposeRevStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedGramReEqSqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelHodgeGramPosDefQuotientStatement
open Matrix
open scoped ComplexOrder
open GlobalTheory.HodgeLocGeo

noncomputable section

namespace GlobalTheory.HodgeLocGeo.Pointwise

theorem log_prod_rpow_neg {κ : Type} [Fintype κ] (x l : κ → ℝ) (hx : ∀ i, 0 < x i) :
    Real.log (∏ i, x i ^ (-l i)) = -∑ i, l i * Real.log (x i) := by
  rw [Real.log_prod (fun i _ => (Real.rpow_pos_of_pos (hx i) _).ne'), ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.log_rpow (hx i)]; ring

theorem rootNorm_castAdd {N j : ℕ} (hpq : j + (N - j) = N) (cW cΩ : ℝ)
    (GW : Matrix (Fin j) (Fin j) ℂ) (GΩ : Matrix (Fin (N - j)) (Fin (N - j)) ℂ)
    (Z : Matrix (Fin j) (Fin (N - j)) ℂ) (i : Fin j) :
    rootNorm N j cW cΩ GW GΩ Z (Fin.cast hpq (Fin.castAdd (N - j) i)) =
      GlobalTheory.GradedNorm.grSq (wLine cW GW Z) i := by
  unfold rootNorm
  rw [dif_pos (by simp)]
  exact congrArg _ (Fin.ext (by simp))

theorem rootNorm_natAdd {N j : ℕ} (hpq : j + (N - j) = N) (cW cΩ : ℝ)
    (GW : Matrix (Fin j) (Fin j) ℂ) (GΩ : Matrix (Fin (N - j)) (Fin (N - j)) ℂ)
    (Z : Matrix (Fin j) (Fin (N - j)) ℂ) (k : Fin (N - j)) :
    rootNorm N j cW cΩ GW GΩ Z (Fin.cast hpq (Fin.natAdd j k)) =
      (GlobalTheory.GradedNorm.grSq (oLine cΩ GΩ Z) (Fin.rev k))⁻¹ := by
  unfold rootNorm
  rw [dif_neg (by simp)]
  congr 2
  ext; simp [Fin.val_rev]; omega

theorem conjT_eq {m n : Type} (A : Matrix m n ℂ) : Aᴴᵀ = A.map (starRingEnd ℂ) := by
  unfold Matrix.conjTranspose; ext a b; simp

theorem conjT_conjTranspose {m n : Type} (A : Matrix m n ℂ) : (Aᴴᵀ)ᴴ = Aᵀ := by
  ext a b; simp

theorem adaptedGram_smul_quotGram_eq_wLine {ι : Type} [Fintype ι] {j q : ℕ} (c : ℝ)
    (G : (ι → ℂ) → Matrix (Fin j) (Fin j) ℂ) (Z : (ι → ℂ) → Matrix (Fin j) (Fin q) ℂ) (v : ι → ℂ)
    (hQ : GlobalTheory.HermFrame.quotGram (modelHodgeGram (Z v)) = (1 - (Z v).map (starRingEnd ℂ) * (Z v)ᵀ)⁻¹) :
    GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.adaptedGram (fun x => (c : ℂ) • GlobalTheory.HermFrame.quotGram (modelHodgeGram (Z x))) id
      (fun x => (G x)ᵀ) v = wLine c (G v) (Z v) := by
  have e : ((G v)ᵀ)ᴴᵀ = (G v)ᴴ := by unfold Matrix.conjTranspose; ext a b; simp
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.adaptedGram, id, transpose_transpose, e, hQ, wLine, Matrix.mul_smul,
    Matrix.smul_mul]

theorem det_rev_isUnit {q : ℕ} (G : Matrix (Fin q) (Fin q) ℂ) (h : IsUnit G.det) :
    IsUnit (G.submatrix Fin.rev id).det := by
  have := Matrix.det_permute Fin.revPerm G
  have e0 : G.submatrix Fin.rev id = G.submatrix (⇑Fin.revPerm) id := by ext a b; simp
  rw [e0, this]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm (n := q))) with e | e <;> simp [e, h.ne_zero]

theorem adaptedOmega {q : ℕ} (c : ℝ) (hc : 0 < c) (G : Matrix (Fin q) (Fin q) ℂ) (hG : IsUnit G.det)
    (Y : Matrix (Fin q) (Fin q) ℂ) (hY : Y.PosDef) :
    (((G.submatrix Fin.rev id)⁻¹)ᵀ * ((((c)⁻¹ : ℝ) : ℂ) • Y) * ((G.submatrix Fin.rev id)⁻¹)ᴴᵀ).PosDef ∧
    ((((G.submatrix Fin.rev id)⁻¹)ᵀ * ((((c)⁻¹ : ℝ) : ℂ) • Y) * ((G.submatrix Fin.rev id)⁻¹)ᴴᵀ)⁻¹)ᵀ.submatrix
      Fin.rev Fin.rev = (c : ℂ) • (G * (Yᵀ)⁻¹ * Gᴴ) := by
  set R := G.submatrix Fin.rev id with hR
  have hRu : IsUnit R.det := det_rev_isUnit G hG
  have hYu : IsUnit Y.det := (isUnit_iff_isUnit_det _).1 hY.isUnit
  have hc' : (0 : ℂ) < (((c)⁻¹ : ℝ) : ℂ) := Complex.zero_lt_real.2 (inv_pos.2 hc)
  constructor
  · have hB : IsUnit ((R⁻¹)ᴴᵀ).det := by
      rw [det_transpose, det_conjTranspose]; exact (isUnit_nonsing_inv_det R hRu).star
    have := (hY.smul hc').conjTranspose_mul_mul_same
      (mulVec_injective_of_isUnit ((isUnit_iff_isUnit_det _).2 hB))
    rwa [conjT_conjTranspose] at this
  · have e1 : (R⁻¹)ᴴᵀ * Rᴴᵀ = 1 := by
      rw [← transpose_mul, ← conjTranspose_mul, nonsing_inv_mul R hRu, conjTranspose_one, transpose_one]
    have e2 : ((((c)⁻¹ : ℝ) : ℂ) • Y) * ((c : ℂ) • Y⁻¹) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_nonsing_inv Y hYu]
      have : (((c)⁻¹ : ℝ) : ℂ) * (c : ℂ) = 1 := by
        push_cast; exact inv_mul_cancel₀ (by exact_mod_cast hc.ne')
      rw [this, one_smul]
    have e3 : (R⁻¹)ᵀ * Rᵀ = 1 := by
      rw [← transpose_mul, mul_nonsing_inv R hRu, transpose_one]
    have hK : ((R⁻¹)ᵀ * ((((c)⁻¹ : ℝ) : ℂ) • Y) * (R⁻¹)ᴴᵀ)⁻¹ = Rᴴᵀ * ((c : ℂ) • Y⁻¹) * Rᵀ := by
      apply inv_eq_right_inv
      calc (R⁻¹)ᵀ * ((((c)⁻¹ : ℝ) : ℂ) • Y) * (R⁻¹)ᴴᵀ * (Rᴴᵀ * ((c : ℂ) • Y⁻¹) * Rᵀ)
          = (R⁻¹)ᵀ * (((((c)⁻¹ : ℝ) : ℂ) • Y) * (((R⁻¹)ᴴᵀ * Rᴴᵀ) * (((c : ℂ) • Y⁻¹) * Rᵀ))) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [e1, Matrix.one_mul, ← Matrix.mul_assoc ((((c)⁻¹ : ℝ) : ℂ) • Y), e2, Matrix.one_mul, e3]
    rw [hK]
    ext a b
    simp only [transpose_mul, transpose_transpose, transpose_smul, transpose_nonsing_inv, submatrix_apply,
      mul_apply, Matrix.smul_apply, conjTranspose_apply, hR, id, Fin.rev_rev, smul_eq_mul, transpose_apply,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring

end GlobalTheory.HodgeLocGeo.Pointwise

namespace GlobalTheory.HodgeLocGeo.Pointwise

theorem transpose_modelY {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℂ) :
    (1 - Zᵀ * Z.map (starRingEnd ℂ))ᵀ = 1 - Zᴴ * Z := by
  rw [transpose_sub, transpose_one, transpose_mul, transpose_transpose]
  rfl

theorem pointwise : ∀ {T : Type} [Fintype T] {ι : Type} [Fintype ι] {N j : ℕ} (hpq : j + (N - j) = N)
    (Zm : T → (ι → ℂ) → Matrix (Fin j) (Fin (N - j)) ℂ) (GW : T → (ι → ℂ) → Matrix (Fin j) (Fin j) ℂ)
    (GΩ : T → (ι → ℂ) → Matrix (Fin (N - j)) (Fin (N - j)) ℂ) (cW cΩ : T → ℝ) (v : ι → ℂ),
    (∀ τ, 0 < cW τ) → (∀ τ, 0 < cΩ τ) → (∀ τ, (1 - (Zm τ v)ᴴ * Zm τ v).PosDef) → (∀ τ, IsUnit (GW τ v).det) →
    (∀ τ, IsUnit (GΩ τ v).det) → ∀ u : T → Fin N → ℝ,
    ∑ x : T × Fin N, u x.1 x.2 * (Real.log (rootNorm N j (cW x.1) (cΩ x.1) (GW x.1 v) (GΩ x.1 v) (Zm x.1 v) x.2) / 2) =
      -Real.log (GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.pairWeightNormSq (p := fun _ => j) (q := fun _ => N - j)
          (fun τ x => (cW τ : ℂ) • GlobalTheory.HermFrame.quotGram (modelHodgeGram (Zm τ x)))
          (fun τ x => (((cΩ τ)⁻¹ : ℝ) : ℂ) • -GlobalTheory.HermFrame.subGram (modelHodgeGram (Zm τ x))) id
          (fun τ x => (GW τ x)ᵀ) (fun τ x => ((GΩ τ x).submatrix Fin.rev id)⁻¹)
          (fun τ k => u τ (Fin.cast hpq k)) v) / 2 := by
  intro T _ ι _ N j hpq Zm GW GΩ cW cΩ v hcW hcΩ hZ hGW hGΩ u
  have hWl : ∀ τ (i : Fin j),
      (GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.lineGram (fun x => (cW τ : ℂ) • GlobalTheory.HermFrame.quotGram (modelHodgeGram (Zm τ x))) id
        (fun x => (GW τ x)ᵀ) i v () ()).re =
        rootNorm N j (cW τ) (cΩ τ) (GW τ v) (GΩ τ v) (Zm τ v) (Fin.cast hpq (Fin.castAdd (N - j) i)) ∧
      0 < rootNorm N j (cW τ) (cΩ τ) (GW τ v) (GΩ τ v) (Zm τ v) (Fin.cast hpq (Fin.castAdd (N - j) i)) := by
    intro τ i
    obtain ⟨h1, -, h3, -⟩ := GlobalTheory.T.model_hodge_gram_pos_def_quotient (Zm τ v) (hZ τ)
    have hP : (wLine (cW τ) (GW τ v) (Zm τ v)).PosDef := by
      unfold wLine
      exact (h1.inv.mul_mul_conjTranspose_same
        (vecMul_injective_of_isUnit ((isUnit_iff_isUnit_det _).2 (hGW τ)))).smul
        (Complex.zero_lt_real.2 (hcW τ))
    rw [rootNorm_castAdd]
    refine ⟨?_, GlobalTheory.GradedNorm.grSq_pos hP i⟩
    rw [GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.lineGram, adaptedGram_smul_quotGram_eq_wLine _ _ _ _ h3]
    exact GlobalTheory.T.graded_gram_re_eq_sq _ hP i
  have hΩl : ∀ τ (k : Fin (N - j)),
      (GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.lineGram
        (fun x => (((cΩ τ)⁻¹ : ℝ) : ℂ) • -GlobalTheory.HermFrame.subGram (modelHodgeGram (Zm τ x))) id
        (fun x => ((GΩ τ x).submatrix Fin.rev id)⁻¹) k v () ()).re =
        rootNorm N j (cW τ) (cΩ τ) (GW τ v) (GΩ τ v) (Zm τ v) (Fin.cast hpq (Fin.natAdd j k)) ∧
      0 < rootNorm N j (cW τ) (cΩ τ) (GW τ v) (GΩ τ v) (Zm τ v) (Fin.cast hpq (Fin.natAdd j k)) := by
    intro τ k
    obtain ⟨-, h2, -, h4⟩ := GlobalTheory.T.model_hodge_gram_pos_def_quotient (Zm τ v) (hZ τ)
    obtain ⟨hP, hI⟩ := adaptedOmega (cΩ τ) (hcΩ τ) (GΩ τ v) (hGΩ τ) _ h2
    have hA : GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.adaptedGram
        (fun x => (((cΩ τ)⁻¹ : ℝ) : ℂ) • -GlobalTheory.HermFrame.subGram (modelHodgeGram (Zm τ x))) id
        (fun x => ((GΩ τ x).submatrix Fin.rev id)⁻¹) v =
        ((GΩ τ v).submatrix Fin.rev id)⁻¹ᵀ *
          ((((cΩ τ)⁻¹ : ℝ) : ℂ) • (1 - (Zm τ v)ᵀ * (Zm τ v).map (starRingEnd ℂ))) *
          ((GΩ τ v).submatrix Fin.rev id)⁻¹ᴴᵀ := by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.adaptedGram, id, h4]
    rw [transpose_modelY] at hI
    rw [rootNorm_natAdd, GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.lineGram, hA, GlobalTheory.T.graded_gram_re_eq_sq _ hP k]
    have hd := GlobalTheory.T.graded_sq_inverse_transpose_rev _ hP k
    rw [hI] at hd
    have hoL : oLine (cΩ τ) (GΩ τ v) (Zm τ v) =
        (cΩ τ : ℂ) • (GΩ τ v * (1 - (Zm τ v)ᴴ * Zm τ v)⁻¹ * (GΩ τ v)ᴴ) := rfl
    rw [hoL, hd, inv_inv]
    exact ⟨rfl, GlobalTheory.GradedNorm.grSq_pos hP k⟩
  have hW1 := fun τ i => (hWl τ i).1
  have hΩ1 := fun τ k => (hΩl τ k).1
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.pairWeightNormSq, GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.weightNormSq, hW1, hΩ1]
  rw [Real.log_prod (fun τ _ => (mul_pos (Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hWl τ i).2 _)
    (Finset.prod_pos fun k _ => Real.rpow_pos_of_pos (hΩl τ k).2 _)).ne')]
  rw [Fintype.sum_prod_type, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Real.log_mul (Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hWl τ i).2 _).ne'
    (Finset.prod_pos fun k _ => Real.rpow_pos_of_pos (hΩl τ k).2 _).ne',
    log_prod_rpow_neg _ _ fun i => (hWl τ i).2, log_prod_rpow_neg _ _ fun k => (hΩl τ k).2,
    ← Fin.sum_congr' _ hpq, Fin.sum_univ_add]
  simp only [← mul_div_assoc, ← Finset.sum_div]
  ring

end GlobalTheory.HodgeLocGeo.Pointwise
