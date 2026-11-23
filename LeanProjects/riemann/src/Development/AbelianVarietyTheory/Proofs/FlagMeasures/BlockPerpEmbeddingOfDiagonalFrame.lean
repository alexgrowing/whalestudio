import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CdScaleIsTrueScale
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousGaussSp

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

namespace GlobalTheory.PerpSort

theorem herm_comp {n P Q : ℕ} {ε : Fin n → Bool} {f : Fin P ⊕ Fin Q ≃ Fin n} (hf : Sorts ε f)
    (x y : Fin n → ℂ) : herm (x ∘ f) (y ∘ f) = star y ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) := by
  obtain ⟨h1, h2⟩ := hf
  rw [dotProduct, ← Equiv.sum_comp f, Fintype.sum_sum_type, herm]
  simp only [Function.comp_apply, Pi.star_apply, Formalism.REAL.Jm, mulVec_diagonal, h1, h2, if_true,
    Bool.false_eq_true, if_false, one_mul, neg_one_mul, mul_neg, Finset.sum_neg_distrib, ← sub_eq_add_neg]
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem form_self {n : ℕ} (ε : Fin n → Bool) (x : Fin n → ℂ) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) = (GlobalTheory.GaussMean.qEps ε x : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Formalism.REAL.Jm, mulVec_diagonal, GlobalTheory.GaussMean.qEps]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  have hx : star (x i) * x i = ((‖x i‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']
    push_cast; ring
  rw [mul_left_comm, hx]
  split_ifs <;> push_cast <;> ring

theorem mat_symm {n P Q : ℕ} {ε : Fin n → Bool} {f : Fin P ⊕ Fin Q ≃ Fin n} (hf : Sorts ε f)
    (k : Formalism.REAL.UJ ε) : (hf.equiv.symm k).mat = (Formalism.MainNotions.S.uMat k).submatrix f f := by
  have h := hf.umat_equiv (hf.equiv.symm k)
  rw [ContinuousMulEquiv.apply_symm_apply] at h
  ext i j
  have e := congrFun (congrFun h (f i)) (f j)
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply] at e
  exact e.symm

theorem act_symm {n P Q : ℕ} {ε : Fin n → Bool} {f : Fin P ⊕ Fin Q ≃ Fin n} (hf : Sorts ε f)
    (k : Formalism.REAL.UJ ε) (x : Fin n → ℂ) :
    act (hf.equiv.symm k) (x ∘ f) = (Formalism.MainNotions.S.uMat k *ᵥ x) ∘ f := by
  rw [act, mat_symm hf, Matrix.submatrix_mulVec_equiv, Function.comp_assoc, f.self_comp_symm,
    Function.comp_id]

private theorem of_fin_cases_mulVec {n : ℕ} (x₀ : Fin (n + 1) → ℂ) (B : Matrix (Fin (n + 1)) (Fin n) ℂ)
    (w : Fin (n + 1) → ℂ) :
    (Matrix.of fun i j => Fin.cases (motive := fun _ => ℂ) (x₀ i) (fun k => B i k) j) *ᵥ w =
      w 0 • x₀ + B *ᵥ fun k => w k.succ := by
  ext i
  simp only [mulVec, dotProduct, Fin.sum_univ_succ, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem exists_mulVec_eq {n : ℕ} (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool)
    (x₀ : Fin (n + 1) → ℂ) (B : Matrix (Fin (n + 1)) (Fin n) ℂ)
    (h0 : star x₀ ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x₀) ≠ 0) (h1 : star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0)
    (h2 : Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε') (y : Fin (n + 1) → ℂ)
    (hy : star x₀ ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0) : ∃ u, B *ᵥ u = y := by
  set J := Formalism.REAL.Jm ε
  set M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    Matrix.of fun i j => Fin.cases (motive := fun _ => ℂ) (x₀ i) (fun k => B i k) j with hM
  have hMv : ∀ w, M *ᵥ w = w 0 • x₀ + B *ᵥ fun k : Fin n => w k.succ := fun w => of_fin_cases_mulVec x₀ B w
  have key : ∀ t : Fin n → ℂ, star x₀ ⬝ᵥ (J *ᵥ (B *ᵥ t)) = 0 := by
    intro t
    rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, h1, zero_dotProduct]
  have hval : ∀ w, star x₀ ⬝ᵥ (J *ᵥ (M *ᵥ w)) = w 0 * (star x₀ ⬝ᵥ (J *ᵥ x₀)) := by
    intro w
    rw [hMv, Matrix.mulVec_add, dotProduct_add, key, add_zero, Matrix.mulVec_smul,
      dotProduct_smul, smul_eq_mul]
  have hinj : Function.Injective M.mulVec := by
    intro a b hab
    have hz : M *ᵥ (a - b) = 0 := by
      rw [Matrix.mulVec_sub]; exact sub_eq_zero.mpr hab
    have hw0 : (a - b) 0 = 0 := by
      have e := hval (a - b)
      rw [hz, Matrix.mulVec_zero, dotProduct_zero] at e
      exact (mul_eq_zero.mp e.symm).resolve_right h0
    have hBt : B *ᵥ (fun k : Fin n => (a - b) k.succ) = 0 := by
      have e := hMv (a - b)
      rw [hz, hw0, zero_smul, zero_add] at e
      exact e.symm
    have ht : (fun k : Fin n => (a - b) k.succ) = 0 := by
      have hJ' : Formalism.REAL.Jm ε' *ᵥ (fun k : Fin n => (a - b) k.succ) = 0 := by
        rw [← h2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hBt, Matrix.mulVec_zero,
          Matrix.mulVec_zero]
      rw [← Matrix.one_mulVec (fun k : Fin n => (a - b) k.succ), ← Formalism.REAL.Jm_mul_self ε',
        ← Matrix.mulVec_mulVec, hJ', Matrix.mulVec_zero]
    rw [← sub_eq_zero]
    funext i
    refine Fin.cases hw0 (fun k => ?_) i
    exact congrFun ht k
  have hsurj : Function.Surjective M.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  obtain ⟨w, hw⟩ := hsurj y
  have hw0 : w 0 = 0 := by
    have e := hval w
    rw [hw, hy] at e
    exact (mul_eq_zero.mp e.symm).resolve_right h0
  refine ⟨fun k : Fin n => w k.succ, ?_⟩
  rw [← hw, hMv, hw0, zero_smul, zero_add]

theorem isPerpEmb_of_sorts : ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (s : Bool) (x₀ : Fin (n + 1) → ℂ) (B : Matrix (Fin (n + 1)) (Fin n) ℂ) (j : Formalism.REAL.UJ ε' → Formalism.REAL.UJ ε), GlobalTheory.GaussMean.qEps ε x₀ = GlobalTheory.GaussMean.sgn ℝ s → star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0 → Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε' → (∀ g, Formalism.MainNotions.S.uMat (j g) *ᵥ x₀ = x₀ ∧ Formalism.MainNotions.S.uMat (j g) * B = B * Formalism.MainNotions.S.uMat g) → ∀ (P Q P' Q' : ℕ) (f : Fin P ⊕ Fin Q ≃ Fin (n + 1)) (f' : Fin P' ⊕ Fin Q' ≃ Fin n) (hf : Sorts ε f) (hf' : Sorts ε' f'), IsPerpEmb (fun i => x₀ (f i)) (B.submatrix f f') (fun g => hf.equiv.symm (j (hf'.equiv g))) := by
  intro n ε ε' s x₀ B j hq h1 h2 hj P Q P' Q' f f' hf hf'
  change IsPerpEmb (x₀ ∘ f) _ _
  have hsub : ∀ u : Fin P' ⊕ Fin Q' → ℂ, B.submatrix f f' *ᵥ u = (B *ᵥ (u ∘ f'.symm)) ∘ f :=
    fun u => Matrix.submatrix_mulVec_equiv _ _ _ _
  have hc : star x₀ ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x₀) ≠ 0 := by
    rw [form_self, hq]
    cases s <;> simp [GlobalTheory.GaussMean.sgn]
  refine ⟨fun u v => ?_, fun y => ⟨fun h0 => ?_, ?_⟩, fun g => ?_⟩
  · have e := herm_comp hf' (u ∘ f'.symm) (v ∘ f'.symm)
    rw [Function.comp_assoc, f'.symm_comp_self, Function.comp_id, Function.comp_assoc,
      f'.symm_comp_self, Function.comp_id] at e
    rw [e, hsub, hsub, herm_comp hf, ← h2, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  · have e := herm_comp hf (y ∘ f.symm) x₀
    rw [Function.comp_assoc, f.symm_comp_self, Function.comp_id] at e
    rw [e] at h0
    obtain ⟨u, hu⟩ := exists_mulVec_eq ε ε' x₀ B hc h1 h2 _ h0
    refine ⟨u ∘ f', ?_⟩
    rw [hsub, Function.comp_assoc, f'.self_comp_symm, Function.comp_id, hu, Function.comp_assoc,
      f.symm_comp_self, Function.comp_id]
  · rintro ⟨u, rfl⟩
    rw [hsub, herm_comp hf, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, h1,
      zero_dotProduct]
  · obtain ⟨hfix, hcomm⟩ := hj (hf'.equiv g)
    refine ⟨?_, fun u => ?_⟩
    · show act (hf.equiv.symm (j (hf'.equiv g))) (x₀ ∘ f) = x₀ ∘ f
      rw [act_symm hf, hfix]
    · show act (hf.equiv.symm (j (hf'.equiv g))) _ = _
      have e := act_symm hf' (hf'.equiv g) (u ∘ f'.symm)
      rw [ContinuousMulEquiv.symm_apply_apply, Function.comp_assoc, f'.symm_comp_self,
        Function.comp_id] at e
      rw [hsub, hsub, act_symm hf, Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, e,
        Function.comp_assoc, f'.self_comp_symm, Function.comp_id]

end GlobalTheory.PerpSort
