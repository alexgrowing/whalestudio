import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicStabilizerInertPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLeviElement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine

noncomputable section

namespace GlobalTheory.ParabExtract

open GlobalTheory.PlaneLeviExt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

lemma cA_cA (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [cA, hσ]
  | add x y hx hy => simp only [map_add, hx, hy]

variable {d d₁ : ℕ}

lemma frame_mulVec_single_eq_x (H' : Plane E d d₁) :
    incM F (frame H') *ᵥ Pi.single (Sum.inr 0) 1 = incV F H'.x := by
  ext i; simp [Matrix.mulVec_single, incM, frame, twoCols, incV]

lemma conj_unitary (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) (B : Base F E) {W : Spc F E d} {W₁ : Spc F E d₁}
    {H' : Plane E d d₁} {i₀ i₁ r s : ℕ} (hW : W.IsSkew σ B r s) (hA : H'.IsAdapted σ B W W₁ i₀ i₁)
    (hu : IsUnit (sq hA.rank H')) (m : Matrix (Fin d) (Fin d) (AE F E))
    (hm : mᵀ * incM F W.J * m.map (cA σ) = incM F W.J) :
    (incM F (coframe hA.rank H') * m * incM F (frame H'))ᵀ * incM F (Matrix.fromBlocks W₁.J 0 0 hyp) *
      (incM F (coframe hA.rank H') * m * incM F (frame H')).map (cA σ) = incM F (Matrix.fromBlocks W₁.J 0 0 hyp) := by
  have hmap : ∀ {a b c : Type} [Fintype b] (X : Matrix a b (AE F E)) (Y : Matrix b c (AE F E)),
      (X * Y).map (cA σ) = X.map (cA σ) * Y.map (cA σ) := fun X Y => Matrix.map_mul (f := (cA σ).toRingHom)
  have hG : (incM F (frame H'))ᵀ * incM F W.J * (incM F (frame H')).map (cA σ) =
      incM F (Matrix.fromBlocks W₁.J 0 0 hyp) := by
    rw [← gram_frame σ hσ B hW hA, incM_mul, incM_mul, incM_transpose, cA_incM]
  have hJ : incM F W.J = (incM F (coframe hA.rank H'))ᵀ * incM F (Matrix.fromBlocks W₁.J 0 0 hyp) *
      (incM F (coframe hA.rank H')).map (cA σ) := by
    have h1 : (incM F (frame H') * incM F (coframe hA.rank H'))ᵀ * incM F W.J *
        (incM F (frame H') * incM F (coframe hA.rank H')).map (cA σ) = incM F W.J := by
      rw [S_T hu, Matrix.transpose_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, Matrix.mul_one]
    calc incM F W.J = (incM F (frame H') * incM F (coframe hA.rank H'))ᵀ * incM F W.J *
          (incM F (frame H') * incM F (coframe hA.rank H')).map (cA σ) := h1.symm
      _ = (incM F (coframe hA.rank H'))ᵀ * ((incM F (frame H'))ᵀ * incM F W.J * (incM F (frame H')).map (cA σ)) *
          (incM F (coframe hA.rank H')).map (cA σ) := by
        rw [Matrix.transpose_mul, hmap]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hG]
  calc _ = (incM F (frame H'))ᵀ * (mᵀ * ((incM F (coframe hA.rank H'))ᵀ * incM F (Matrix.fromBlocks W₁.J 0 0 hyp) *
          (incM F (coframe hA.rank H')).map (cA σ)) * m.map (cA σ)) * (incM F (frame H')).map (cA σ) := by
        simp only [Matrix.transpose_mul, hmap, Matrix.mul_assoc]
    _ = _ := by rw [← hJ, hm, hG]

lemma row_y (σ : E →ₐ[F] E) (J₁ : Matrix (Fin d₁) (Fin d₁) E) (q : Matrix (Fin d₁ ⊕ Fin 2) (Fin d₁ ⊕ Fin 2) (AE F E))
    (b : AE F E) (hq : qᵀ * incM F (Matrix.fromBlocks J₁ 0 0 hyp) * q.map (cA σ) = incM F (Matrix.fromBlocks J₁ 0 0 hyp))
    (hx : q *ᵥ Pi.single (Sum.inr 0) 1 = b • Pi.single (Sum.inr 0) 1) :
    q (Sum.inr 1) (Sum.inr 1) * cA σ b = 1 ∧ (∀ i, q (Sum.inr 1) (Sum.inl i) = 0) ∧
      (∀ i, q (Sum.inl i) (Sum.inr 0) = 0) ∧ q (Sum.inr 0) (Sum.inr 0) = b := by
  have hcol : ∀ j, q j (Sum.inr 0) = if j = Sum.inr 0 then b else 0 := by
    intro j
    have := congrFun hx j
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Pi.smul_apply, smul_eq_mul] at this
    rw [this]
  have key : ∀ k, (qᵀ * incM F (Matrix.fromBlocks J₁ 0 0 hyp) * q.map (cA σ)) k (Sum.inr 0) =
      -(q (Sum.inr 1) k * cA σ b) := by
    intro k
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, hcol, incM, hyp]
  have h1 : q (Sum.inr 1) (Sum.inr 1) * cA σ b = 1 := by
    have := key (Sum.inr 1); rw [hq] at this
    simp [incM, hyp] at this
    linear_combination -this
  refine ⟨h1, fun i => ?_, fun i => by simpa using hcol (Sum.inl i), by simpa using hcol (Sum.inr 0)⟩
  have h2 : q (Sum.inr 1) (Sum.inl i) * cA σ b = 0 := by
    have := key (Sum.inl i); rw [hq] at this
    simp [incM] at this
    exact this
  calc q (Sum.inr 1) (Sum.inl i) = q (Sum.inr 1) (Sum.inl i) * (q (Sum.inr 1) (Sum.inr 1) * cA σ b) := by rw [h1, mul_one]
    _ = (q (Sum.inr 1) (Sum.inl i) * cA σ b) * q (Sum.inr 1) (Sum.inr 1) := by ring
    _ = 0 := by rw [h2, zero_mul]

end GlobalTheory.ParabExtract

open GlobalTheory.PlaneLeviExt GlobalTheory.ParabExtract in

theorem GlobalTheory.ParabExtract.extract : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r s r₁ s₁ : ℕ), B.IsGood σ →
    W.IsSkew σ B r s → W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ v : Pl F,
    ∀ p ∈ UAt σ W (evFin F v), ∀ a : AE F E, mat p *ᵥ incV F H'.x = a • incV F H'.x →
    ∃ (t : (AE F E)ˣ) (h₁ : UA σ W₁.J), (t : AE F E) = a ∧ At (evFin F v) ((t : AE F E) - 1) ∧
      h₁ ∈ UAt σ W₁ (evFin F v) ∧ ∀ z : Fin d₁ → AE F E, ∃ c : AE F E,
        mat p *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ (mat h₁ *ᵥ z) + c • incV F H'.x := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H' i₀ i₁ r s r₁ s₁ hB hW hW₁ hA v p hp a ha
  have hσ : ∀ z, σ (σ z) = z := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hu := isUnit_sq σ hσ B hW hW₁ hA
  obtain ⟨S, hS⟩ : ∃ S, S = incM F (frame H') := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, T = incM F (coframe hA.rank H') := ⟨_, rfl⟩
  have hST : S * T = 1 := by rw [hS, hT]; exact S_T hu
  have hTS : T * S = 1 := by rw [hS, hT]; exact T_S hu
  have hpinv : mat p * mat p⁻¹ = 1 := by
    show ((p.1 * (p⁻¹).1 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) = 1
    rw [← Subgroup.coe_mul, mul_inv_cancel]; rfl
  have hpinv' : mat p⁻¹ * mat p = 1 := by
    show (((p⁻¹).1 * p.1 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) = 1
    rw [← Subgroup.coe_mul, inv_mul_cancel]; rfl
  obtain ⟨q, hq⟩ : ∃ q, q = T * mat p * S := ⟨_, rfl⟩
  obtain ⟨q', hq'⟩ : ∃ q', q' = T * mat p⁻¹ * S := ⟨_, rfl⟩
  have hqq' : q * q' = 1 := by
    rw [hq, hq']; simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc S T, hST, Matrix.one_mul, ← Matrix.mul_assoc (mat p), hpinv, Matrix.one_mul, hTS]
  have hGq : qᵀ * incM F (Matrix.fromBlocks W₁.J 0 0 hyp) * q.map (cA σ) = incM F (Matrix.fromBlocks W₁.J 0 0 hyp) := by
    rw [hq, hT, hS]; exact conj_unitary σ hσ B hW hA hu (mat p) p.2
  have hGq' : q'ᵀ * incM F (Matrix.fromBlocks W₁.J 0 0 hyp) * q'.map (cA σ) = incM F (Matrix.fromBlocks W₁.J 0 0 hyp) := by
    rw [hq', hT, hS]; exact conj_unitary σ hσ B hW hA hu (mat p⁻¹) (p⁻¹).2
  have hSe : S *ᵥ Pi.single (Sum.inr 0) 1 = incV F H'.x := by rw [hS]; exact frame_mulVec_single_eq_x H'
  have hqx : ∀ (m : Matrix (Fin d) (Fin d) (AE F E)) (b : AE F E), m *ᵥ incV F H'.x = b • incV F H'.x →
      (T * m * S) *ᵥ Pi.single (Sum.inr 0) 1 = b • Pi.single (Sum.inr 0) 1 := by
    intro m b hm
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hSe, hm, Matrix.mulVec_smul, ← hSe, Matrix.mulVec_mulVec, hTS,
      Matrix.one_mulVec]
  have ry := row_y σ W₁.J q a hGq (by rw [hq]; exact hqx _ _ ha)
  have hya : a * cA σ (q (Sum.inr 1) (Sum.inr 1)) = 1 := by
    have := congrArg (cA σ) ry.1
    rw [map_mul, cA_cA σ hσ, map_one] at this
    rw [mul_comm]; exact this
  let t : (AE F E)ˣ := Units.mkOfMulEqOne a _ hya
  have ht : (t : AE F E) = a := rfl
  have ha' : mat p⁻¹ *ᵥ incV F H'.x = ((t⁻¹ : (AE F E)ˣ) : AE F E) • incV F H'.x := by
    have h1 : incV F H'.x = a • (mat p⁻¹ *ᵥ incV F H'.x) := by
      rw [← Matrix.mulVec_smul, ← ha, Matrix.mulVec_mulVec, hpinv', Matrix.one_mulVec]
    conv_rhs => rw [h1]
    rw [smul_smul, ← ht, Units.inv_mul, one_smul]
  have ry' := row_y σ W₁.J q' _ hGq' (by rw [hq']; exact hqx _ _ ha')
  let A : Matrix (Fin d₁) (Fin d₁) (AE F E) := Matrix.of fun i j => q (Sum.inl i) (Sum.inl j)
  let A' : Matrix (Fin d₁) (Fin d₁) (AE F E) := Matrix.of fun i j => q' (Sum.inl i) (Sum.inl j)
  have hAA' : A * A' = 1 := by
    ext i j
    have := congrFun (congrFun hqq' (Sum.inl i)) (Sum.inl j)
    simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, ry.2.2.1 i, ry'.2.1 j, zero_mul, mul_zero,
      add_zero] at this
    simpa [A, A', Matrix.mul_apply, Matrix.one_apply] using this
  have hA'A : A' * A = 1 := by first | exact mul_eq_one_comm.mp hAA' | exact Matrix.mul_eq_one_comm.mp hAA' | exact (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp hAA'
  have hAU : Aᵀ * incM F W₁.J * A.map (cA σ) = incM F W₁.J := by
    ext i j
    have := congrFun (congrFun hGq (Sum.inl i)) (Sum.inl j)
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, incM, hyp, ry.2.1] at this
    simpa [A, Matrix.mul_apply, incM] using this
  let h₁ : UA σ W₁.J := ⟨⟨A, A', hAA', hA'A⟩, hAU⟩
  have hp' : ∀ u, evFin F v u = 0 → u • (mat p - 1) = 0 := hp
  have hq1 : ∀ u, evFin F v u = 0 → u • (q - 1) = 0 := by
    intro u hu0
    have e : q - 1 = T * (mat p - 1) * S := by
      rw [hq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hTS]
    rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, hp' u hu0, Matrix.mul_zero, Matrix.zero_mul]
  refine ⟨t, h₁, rfl, ?_, ?_, ?_⟩
  · show ∀ u, evFin F v u = 0 → u • (a - 1) = 0
    intro u hu0
    have := congrFun (congrFun (hq1 u hu0) (Sum.inr 0)) (Sum.inr 0)
    simpa [ry.2.2.2] using this
  · show ∀ u, evFin F v u = 0 → u • (A - 1) = 0
    intro u hu0
    ext i j
    have := congrFun (congrFun (hq1 u hu0) (Sum.inl i)) (Sum.inl j)
    simpa [A, Matrix.one_apply] using this
  · intro z
    have hpS : mat p * S = S * q := by
      rw [hq, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hST, Matrix.one_mul]
    have hw : incM F H'.ι *ᵥ z = S *ᵥ Sum.elim z 0 := by
      rw [hS, incM_frame, Matrix.fromCols_mulVec]
      simp
    have hy1 : (q *ᵥ Sum.elim z 0) (Sum.inr 1) = 0 := by
      simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, ry.2.1]
    have hinl : (fun k => (q *ᵥ Sum.elim z 0) (Sum.inl k)) = A *ᵥ z := by
      funext k; simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, A]
    refine ⟨(q *ᵥ Sum.elim z 0) (Sum.inr 0), ?_⟩
    rw [hw, Matrix.mulVec_mulVec, hpS, ← Matrix.mulVec_mulVec, hS, incM_frame, Matrix.fromCols_mulVec]
    show _ = incM F H'.ι *ᵥ (A *ᵥ z) + _
    rw [← hinl]
    congr 1
    generalize q *ᵥ Sum.elim z 0 = w at hy1 ⊢
    ext i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, incM, twoCols, incV, hy1, mul_comm]
