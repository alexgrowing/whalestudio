import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetAdaptedBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordsPreserveGramMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisMulHeisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordsMultiplicativeConjugationStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.QhtUnip

noncomputable section

namespace GlobalTheory.QhtUnip

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_cA_eq (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [cA, hσ]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem conj_mulVec_eq {n : ℕ} {P M : Matrix (Fin n) (Fin n) (AE F E)} (hP : IsUnit P.det)
    {v v' : Fin n → AE F E} (h : M *ᵥ (P *ᵥ v) = P *ᵥ v') : (P⁻¹ * M * P) *ᵥ v = v' := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hP, Matrix.one_mulVec]

theorem incM_basQ_col {m : ℕ} (H : Plane E (m + 2) m) (j : Ix m) :
    incM F (basQ H) *ᵥ Pi.single ((ixE m).symm j) 1 = fun r => inclR (F := F) (AF F) (basP H r j) := by
  funext r
  simp [Matrix.mulVec_single_one, incM, basQ, Matrix.transpose_apply]

theorem crd_apply {σ : E →ₐ[F] E} {m : ℕ} {J : Matrix (Fin (m + 2)) (Fin (m + 2)) E} (H : Plane E (m + 2) m)
    (g : UA σ J) (i j : Ix m) : crd H g i j =
      (((incM F (basQ H))⁻¹ * mat g * incM F (basQ H)) *ᵥ Pi.single ((ixE m).symm j) 1) ((ixE m).symm i) := by
  simp [crd, Matrix.mulVec_single_one, Matrix.transpose_apply]

theorem isUnit_det_incM_basQ {m : ℕ} (H : Plane E (m + 2) m) : IsUnit (basQ H).det → IsUnit (incM F (basQ H)).det := by
  intro hP
  have : (incM F (basQ H)).det = inclR (F := F) (AF F) (basQ H).det := by
    rw [RingHom.map_det]; rfl
  rw [this]; exact hP.map _

theorem crd_eq_heis_of_gen (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {m : ℕ} {J : Matrix (Fin (m + 2)) (Fin (m + 2)) E}
    (J₁ : Matrix (Fin m) (Fin m) E) (H : Plane E (m + 2) m) (hP : IsUnit (basQ H).det)
    (u : UA σ J)
    (hU : (crd H u)ᵀ * (gI J₁).map (inclR (F := F) (AF F)) * (crd H u).map (cA σ) = (gI J₁).map (inclR (F := F) (AF F)))
    (hx : mat u *ᵥ incV F H.x = incV F H.x)
    (hι : ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + a • incV F H.x) :
    ∃ (a w : Fin m → AE F E) (α : AE F E), crd H u = Heisenberg₂ a w α := by
  have hQ := isUnit_det_incM_basQ (F := F) H hP
  set Q := incM F (basQ H) with hQdef
  choose a ha using fun k : Fin m => hι (Pi.single k 1)
  have cx : Q *ᵥ Pi.single ((ixE m).symm (Sum.inl (Sum.inl 0))) 1 = incV F H.x := by
    rw [incM_basQ_col]; rfl
  have cι : ∀ k, Q *ᵥ Pi.single ((ixE m).symm (Sum.inl (Sum.inr k))) 1 = incM F H.ι *ᵥ Pi.single k 1 := by
    intro k; rw [incM_basQ_col]; funext r; simp [Matrix.mulVec_single_one, incM, basP, Matrix.transpose_apply]
  have hcx : ((Q⁻¹ * mat u * Q) *ᵥ Pi.single ((ixE m).symm (Sum.inl (Sum.inl 0))) 1) =
      Pi.single ((ixE m).symm (Sum.inl (Sum.inl 0))) 1 := conj_mulVec_eq hQ (by rw [cx, hx])
  have hcι : ∀ k, ((Q⁻¹ * mat u * Q) *ᵥ Pi.single ((ixE m).symm (Sum.inl (Sum.inr k))) 1) =
      Pi.single ((ixE m).symm (Sum.inl (Sum.inr k))) 1 + a k • Pi.single ((ixE m).symm (Sum.inl (Sum.inl 0))) 1 := by
    intro k
    refine conj_mulVec_eq hQ ?_
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, cx, cι, ha]
  have ex : ∀ i, crd H u i (Sum.inl (Sum.inl 0)) = if i = Sum.inl (Sum.inl 0) then 1 else 0 := by
    intro i; rw [crd_apply, hcx]; simp [Pi.single_apply]
  have eι : ∀ i k, crd H u i (Sum.inl (Sum.inr k)) = (if i = Sum.inl (Sum.inr k) then 1 else 0) +
      a k * (if i = Sum.inl (Sum.inl 0) then 1 else 0) := by
    intro i k; rw [crd_apply, hcι]; simp [Pi.single_apply]
  have eyy : crd H u (Sum.inr 0) (Sum.inr 0) = 1 := by
    have h := congrFun (congrFun hU (Sum.inl (Sum.inl 0))) (Sum.inr 0)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, ex, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    simp [Fintype.sum_sum_type, gI, Matrix.fromBlocks] at h
    have h2 := congrArg (cA σ) h
    rwa [cA_cA_eq σ hσ, map_one] at h2
  refine ⟨a, fun k => crd H u (Sum.inl (Sum.inr k)) (Sum.inr 0), crd H u (Sum.inl (Sum.inl 0)) (Sum.inr 0), ?_⟩
  ext ((i | i) | i) ((j | j) | j)
  · rw [Subsingleton.elim i 0, Subsingleton.elim j 0, ex]; simp [Heisenberg₂, Matrix.fromBlocks]
  · rw [Subsingleton.elim i 0, eι]; simp [Heisenberg₂, Matrix.fromBlocks]
  · rw [Subsingleton.elim i 0, Subsingleton.elim j 0]; simp [Heisenberg₂, Matrix.fromBlocks]
  · rw [Subsingleton.elim j 0, ex]; simp [Heisenberg₂, Matrix.fromBlocks]
  · rw [eι]; simp [Heisenberg₂, Matrix.fromBlocks, Matrix.one_apply]
  · rw [Subsingleton.elim j 0]; simp [Heisenberg₂, Matrix.fromBlocks]
  · rw [Subsingleton.elim i 0, Subsingleton.elim j 0, ex]; simp [Heisenberg₂, Matrix.fromBlocks]
  · rw [Subsingleton.elim i 0, eι]; simp [Heisenberg₂, Matrix.fromBlocks]
  · rw [Subsingleton.elim i 0, Subsingleton.elim j 0, eyy]; simp [Heisenberg₂, Matrix.fromBlocks]

theorem crd_unip_eq_heis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ e, σ (σ e) = e) → ∀ (B : Base F E) {m : ℕ} (W : Spc F E (m + 2)) (r s : ℕ), W.IsSkew σ B r s →
    ∀ (W₁ : Spc F E m) (H : Plane E (m + 2) m) (i₀ i₁ : ℕ), H.IsAdapted σ B W W₁ i₀ i₁ → ∀ u ∈ unip σ W H, ∃ (a w : Fin m → AE F E) (α : AE F E), crd H u = Heisenberg₂ a w α := by
  intro F E _ _ _ _ _ σ hσ B m W r s hW W₁ H i₀ i₁ hA u hu
  have hP := GlobalTheory.T.isUnit_det_adapted_basis F E σ B W r s hW W₁ H i₀ i₁ hA
  obtain ⟨hmul, hone, -⟩ := GlobalTheory.T.coords_multiplicative_conjugation F E σ W.J H hP
  have hU := GlobalTheory.T.coords_preserve_gram_matrix F E σ hσ B W r s hW W₁ H i₀ i₁ hA
  unfold unip at hu
  induction hu using Subgroup.closure_induction with
  | mem x hx => exact crd_eq_heis_of_gen σ hσ W₁.J H hP x (hU x) hx.1 hx.2
  | one => exact ⟨0, 0, 0, by rw [hone, heis_zero]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, w, α, ha⟩ := hx
    obtain ⟨a', w', α', hb⟩ := hy
    exact ⟨_, _, _, by rw [hmul, ha, hb, GlobalTheory.T.heis_mul_heis]⟩
  | inv x _ hx =>
    obtain ⟨a, w, α, ha⟩ := hx
    refine ⟨-a, -w, -α + ∑ k, a k * w k, ?_⟩
    have h1 : crd H x * Heisenberg₂ (-a) (-w) (-α + ∑ k, a k * w k) = 1 := by
      rw [ha, GlobalTheory.T.heis_mul_heis, ← heis_zero]
      congr 1
      · simp
      · simp
      · simp [Finset.sum_neg_distrib]
    calc crd H x⁻¹ = crd H x⁻¹ * (crd H x * Heisenberg₂ (-a) (-w) (-α + ∑ k, a k * w k)) := by rw [h1, Matrix.mul_one]
      _ = crd H (x⁻¹ * x) * Heisenberg₂ (-a) (-w) (-α + ∑ k, a k * w k) := by rw [hmul, Matrix.mul_assoc]
      _ = _ := by rw [inv_mul_cancel, hone, Matrix.one_mul]

end GlobalTheory.QhtUnip
