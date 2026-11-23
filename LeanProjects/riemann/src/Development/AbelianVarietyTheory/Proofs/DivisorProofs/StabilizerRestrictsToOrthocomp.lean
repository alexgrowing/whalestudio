import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeviIdeleHomExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentStabilizerLeviDecomposition
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IsoPlaneProj

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem det_ne_zero_of_cartan (B : Base F E) {n : ℕ} (Y : Spc F E n)
    (h : ∀ w, IsCartan (Complex.I • Y.J.map (B.emb w).1) (Y.θ w)) : Y.J.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hJv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  let w : InfinitePlace F := Classical.arbitrary _
  let τ : E →+* ℂ := (B.emb w).1
  let M : Matrix (Fin n) (Fin n) ℂ := Complex.I • Y.J.map τ
  let v' : Fin n → ℂ := fun i => τ (v i)
  have hv' : v' ≠ 0 := fun h => hv (funext fun i => τ.injective (by simpa [v'] using congrFun h i))
  have hMv : M *ᵥ v' = 0 := by
    ext i
    have := congrArg τ (congrFun hJv i)
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.zero_apply, map_zero] at this
    simp only [M, v', Matrix.smul_mulVec, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, Matrix.smul_apply, mul_assoc, ← Finset.mul_sum, this, mul_zero]
  have hx : star v' ≠ 0 := fun h => hv' (by simpa using congrArg star h)
  have := (h w).2.2 (star v') hx
  rw [star_star] at this
  change 0 < (_ ⬝ᵥ M *ᵥ v').re at this
  rw [hMv, dotProduct_zero, Complex.zero_re] at this
  exact lt_irrefl _ this

theorem frame_of_gram {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) {n n₁ : ℕ} {J : Matrix (Fin n) (Fin n) E}
    {J₁ : Matrix (Fin n₁) (Fin n₁) E} (hsk : ∀ i j, σ (J j i) = -J i j) {x y : Fin n → E} {ι : Matrix (Fin n) (Fin n₁) E}
    (hn : n = n₁ + 2) (hxx : form σ J x x = 0) (hyy : form σ J y y = 0) (hxy : form σ J x y = 1)
    (horth : ∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) (hgram : ιᵀ * J * ι.map σ = J₁)
    (hJ₁ : IsUnit J₁.det) :
    ∃ π : Matrix (Fin n₁) (Fin n) E, vecMulVec x (J *ᵥ (⇑σ ∘ y)) + ι * π - vecMulVec y (J *ᵥ (⇑σ ∘ x)) = 1 := by
  obtain ⟨hax, hay, hbx, hby, hxJ, hyJ, haι, hbι⟩ := GlobalTheory.LeviIdeleHom.dual_facts hσ hsk hxx hyy hxy horth
  set aE := J *ᵥ (⇑σ ∘ y) with haE
  set bE := -(J *ᵥ (⇑σ ∘ x)) with hbE
  let π : Matrix (Fin n₁) (Fin n) E := (J₁⁻¹)ᵀ * (J * ι.map σ)ᵀ
  have hπι : π * ι = 1 := by
    calc π * ι = (J₁⁻¹)ᵀ * (ιᵀ * J * ι.map σ)ᵀ := by
          simp only [π, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = 1 := by rw [hgram, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hJ₁, Matrix.transpose_one]
  have hv : ∀ w : Fin n → E, (⇑σ ∘ w) ᵥ* ι.map σ = ⇑σ ∘ (w ᵥ* ι) := fun w =>
    funext fun j => by simp [vecMul, dotProduct, map_sum]
  have hπx : π *ᵥ x = 0 := by
    have inner : (J * ι.map σ)ᵀ *ᵥ x = 0 := by
      rw [mulVec_transpose, ← vecMul_vecMul, hxJ, hv, hbι]
      funext j; simp
    simp only [π]
    rw [← mulVec_mulVec, inner, mulVec_zero]
  have hπy : π *ᵥ y = 0 := by
    have inner : (J * ι.map σ)ᵀ *ᵥ y = 0 := by
      rw [mulVec_transpose, ← vecMul_vecMul, hyJ, neg_vecMul, hv, haι]
      funext j; simp
    simp only [π]
    rw [← mulVec_mulVec, inner, mulVec_zero]
  let X : Matrix (Fin n) (Fin 2) E := Matrix.of fun i k => ![x i, y i] k
  let L : Matrix (Fin 2) (Fin n) E := Matrix.of ![aE, bE]
  have hLX : L * X = 1 := by
    ext k l
    fin_cases k <;> fin_cases l <;> simp [Matrix.mul_apply, L, X, Matrix.one_apply]
    · exact hax
    · exact hay
    · exact hbx
    · exact hby
  have hLι : L * ι = 0 := by
    ext k j
    fin_cases k <;> simp [Matrix.mul_apply, L]
    · exact congrFun haι j
    · exact congrFun hbι j
  have hπX : π * X = 0 := by
    ext k l
    fin_cases l <;> simp [Matrix.mul_apply, X]
    · exact congrFun hπx k
    · exact congrFun hπy k
  have hXL : X * L = vecMulVec x aE + vecMulVec y bE := by
    ext i j
    simp [Matrix.mul_apply, X, L, Fin.sum_univ_two, vecMulVec_apply]
  have h1 : Matrix.fromRows π L * Matrix.fromCols ι X = 1 := by
    rw [Matrix.fromRows_mul_fromCols, hπι, hπX, hLι, hLX, Matrix.fromBlocks_one]
  have e : Fin n₁ ⊕ Fin 2 ≃ Fin n := finSumFinEquiv.trans (finCongr hn.symm)
  have h2 := (Matrix.mul_eq_one_comm_of_equiv e).1 h1
  rw [Matrix.fromCols_mul_fromRows, hXL] at h2
  refine ⟨π, ?_⟩
  rw [← h2, hbE, Matrix.vecMulVec_neg]
  abel

end GlobalTheory.IsoPlaneProj
