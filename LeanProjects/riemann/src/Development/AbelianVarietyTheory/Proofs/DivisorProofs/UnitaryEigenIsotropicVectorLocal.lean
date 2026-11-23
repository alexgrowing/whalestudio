import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLeviElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementSkewCm
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.PlaneLeviBlock

open GlobalTheory.PlaneLeviExt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

lemma cA_cA (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) (a : AE F E) : cA σ (cA σ a) = a := by
  have hs : σ.comp σ = AlgHom.id F E := AlgHom.ext hσ
  have h : (cA σ).comp (cA σ) = AlgHom.id (AF F) (AE F E) := by
    simp only [cA, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id, hs, Algebra.TensorProduct.map_id]
  exact DFunLike.congr_fun h a

end GlobalTheory.PlaneLeviBlock

open GlobalTheory.PlaneLeviExt GlobalTheory.PlaneLeviBlock in

theorem GlobalTheory.PlaneLeviBlock.levi_block : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r s r₁ s₁ : ℕ),
    B.IsGood σ → W.IsSkew σ B r s → W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (v : Pl F) (p : UA σ W.J), p ∈ UAt σ W (evFin F v) → ∀ t : (AE F E)ˣ, mat p *ᵥ incV F H'.x = t.1 • incV F H'.x →
      At (F := F) (evFin F v) (t.1 - 1) ∧ ∃ h₁ : UA σ W₁.J, h₁ ∈ UAt σ W₁ (evFin F v) ∧
        ∀ z, ∃ a : AE F E, mat p *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ (mat h₁ *ᵥ z) + a • incV F H'.x := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H' i₀ i₁ r s r₁ s₁ hB hW hW₁ hA v p hp t ht
  have hσ : ∀ z, σ (σ z) = z := GlobalTheory.ThK.Inhab.conj_conj hB.cm
  have hu := isUnit_sq σ hσ B hW hW₁ hA
  set S := incM F (frame H') with hSdef
  set T := incM F (coframe hA.rank H') with hTdef
  have hST : S * T = 1 := S_T hu
  have hTS : T * S = 1 := T_S hu
  set P := mat p with hPdef
  set q := T * P * S with hqdef
  set G := incM F (Matrix.fromBlocks W₁.J 0 0 hyp) with hGdef
  have hmap : ∀ {a b c : Type} [Fintype b] (X : Matrix a b (AE F E)) (Y : Matrix b c (AE F E)),
      (X * Y).map (cA σ) = X.map (cA σ) * Y.map (cA σ) := fun X Y => Matrix.map_mul (f := (cA σ).toRingHom)
  have hP : Pᵀ * incM F W.J * P.map (cA σ) = incM F W.J := p.2
  clear_value S T P q G
  have hG : Sᵀ * incM F W.J * S.map (cA σ) = G := by
    rw [hSdef, hGdef, ← gram_frame σ hσ B hW hA, incM_mul, incM_mul, incM_transpose, cA_incM]
  have hSq : S * q = P * S := by
    rw [hqdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hST, Matrix.one_mul]
  have hq : qᵀ * G * q.map (cA σ) = G := by
    rw [← hG]
    calc qᵀ * (Sᵀ * incM F W.J * S.map (cA σ)) * q.map (cA σ)
        = (S * q)ᵀ * incM F W.J * (S * q).map (cA σ) := by
          rw [Matrix.transpose_mul, hmap]; simp only [Matrix.mul_assoc]
      _ = Sᵀ * (Pᵀ * incM F W.J * P.map (cA σ)) * S.map (cA σ) := by
          rw [hSq, Matrix.transpose_mul, hmap]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hP]
  have hSe : S *ᵥ Pi.single (Sum.inr 0) 1 = incV F H'.x := by
    rw [Matrix.mulVec_single_one]
    ext i; simp [hSdef, incM, frame, twoCols, incV]
  have hqe : q *ᵥ Pi.single (Sum.inr 0) 1 = t.1 • Pi.single (Sum.inr 0) 1 := by
    rw [hqdef, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hSe, ht, Matrix.mulVec_smul, ← hSe,
      Matrix.mulVec_mulVec, hTS, Matrix.one_mulVec]
  have hcol : ∀ k, q k (Sum.inr 0) = if k = Sum.inr 0 then t.1 else 0 := by
    intro k
    have := congrFun hqe k
    rw [Matrix.mulVec_single_one] at this
    simpa [Pi.single_apply] using this

  have hC1 : ∀ j, q (Sum.inr 1) (Sum.inl j) = 0 := by
    intro j
    have h := congrFun (congrFun hq (Sum.inr 0)) (Sum.inl j)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hcol, Fintype.sum_sum_type,
      Fin.sum_univ_two, hGdef, incM, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, hyp] at h
    simp at h
    rw [← cA_cA σ hσ (q _ _), h, map_zero]
  set A : Matrix (Fin d₁) (Fin d₁) (AE F E) := Matrix.of fun i j => q (Sum.inl i) (Sum.inl j) with hAdef
  have hA1 : Aᵀ * incM F W₁.J * A.map (cA σ) = incM F W₁.J := by
    ext i j
    have h := congrFun (congrFun hq (Sum.inl i)) (Sum.inl j)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two, hGdef, incM, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, hyp, hC1] at h
    simp at h
    rw [hAdef]
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, incM] using h
  have hdetJ : IsUnit (incM F W₁.J).det := by
    have := RingHom.map_det (inclR (F := F) (AF F)) W₁.J
    rw [incM]
    exact (this ▸ (GlobalTheory.LeviAdapted.det_ne_zero hW₁).isUnit.map (inclR (F := F) (AF F)) :)
  have hdetA : IsUnit A.det := by
    have h := congrArg Matrix.det hA1
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
    have h2 : (A.map (cA σ)).det = cA σ A.det := (AlgHom.map_det (cA σ) A).symm
    rw [h2] at h
    have h3 : A.det * cA σ A.det = 1 := by
      refine hdetJ.mul_left_cancel ?_
      linear_combination h
    exact isUnit_iff_exists.mpr ⟨_, h3, by rw [mul_comm]; exact h3⟩
  have hAu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr hdetA
  let h₁ : UA σ W₁.J := ⟨hAu.unit, by show (hAu.unit.1)ᵀ * incM F W₁.J * (hAu.unit.1).map (cA σ) = incM F W₁.J; exact hA1⟩
  have hmat : mat h₁ = A := IsUnit.unit_spec hAu
  have hsupp : ∀ u : AF F, evFin F v u = 0 → u • (q - 1) = 0 := by
    intro u hu0
    have e1 : q - 1 = T * (P - 1) * S := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hTS, hqdef]
    rw [e1, ← Matrix.smul_mul, ← Matrix.mul_smul, hPdef, hp u hu0, Matrix.mul_zero, Matrix.zero_mul]
  refine ⟨fun u hu0 => ?_, h₁, fun u hu0 => ?_, fun z => ?_⟩
  · have := congrFun (congrFun (hsupp u hu0) (Sum.inr 0)) (Sum.inr 0)
    simpa [hcol] using this
  · rw [hmat]
    ext i j
    have := congrFun (congrFun (hsupp u hu0) (Sum.inl i)) (Sum.inl j)
    simpa [hAdef, Matrix.one_apply] using this
  · set w : Fin d₁ ⊕ Fin 2 → AE F E := Sum.elim z 0 with hwdef
    have hιS : incM F H'.ι *ᵥ z = S *ᵥ w := by
      rw [hSdef, incM_frame, Matrix.fromCols_mulVec, hwdef, Sum.elim_comp_inl, Sum.elim_comp_inr]
      simp
    set w' := q *ᵥ w with hw'def
    have hw1 : w' (Sum.inr 1) = 0 := by
      simp [hw'def, hwdef, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, hC1]
    have hwl : w' ∘ Sum.inl = A *ᵥ z := by
      ext i; simp [hw'def, hwdef, hAdef, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
    have hwr : incM F (twoCols H') *ᵥ (w' ∘ Sum.inr) = w' (Sum.inr 0) • incV F H'.x := by
      ext i
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Function.comp_apply, hw1, mul_zero, add_zero]
      simp [incM, twoCols, incV, mul_comm]
    refine ⟨w' (Sum.inr 0), ?_⟩
    rw [hmat, hιS, Matrix.mulVec_mulVec, ← hSq, ← Matrix.mulVec_mulVec, ← hw'def, hSdef, incM_frame,
      Matrix.fromCols_mulVec, hwl, hwr]
