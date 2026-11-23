import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsRationalDblCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAdeleE
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cont

namespace GlobalTheory.DefiniteAniso

theorem eq_zero_of_congr_one {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι ≃ Fin n)
    {M : Matrix (Fin n) (Fin n) ℂ} {A : Matrix (Fin n) ι ℂ} (h1 : Aᵀ * M * A.map star = 1) (x : Fin n → ℂ)
    (hx : x ⬝ᵥ M *ᵥ star x = 0) : x = 0 := by
  have h2 : A * (M * A.map star)ᵀ = 1 := by
    have h3 : (M * A.map star) * Aᵀ = 1 :=
      (Matrix.mul_eq_one_comm_of_equiv e).1 (by rw [← Matrix.mul_assoc]; exact h1)
    have h4 := congrArg Matrix.transpose h3
    simpa [Matrix.transpose_mul] using h4
  obtain ⟨z, hxz⟩ : ∃ z, x = A *ᵥ z :=
    ⟨(M * A.map star)ᵀ *ᵥ x, by rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]⟩
  have hstar : star (A *ᵥ z) = A.map star *ᵥ star z := by
    ext i; simp [Matrix.mulVec, dotProduct, star_sum, mul_comm]
  have key : x ⬝ᵥ M *ᵥ star x = z ⬝ᵥ star z := by
    rw [hxz, hstar, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose A z, Matrix.dotProduct_mulVec,
      Matrix.vecMul_vecMul, ← Matrix.mul_assoc, h1, Matrix.vecMul_one]
  rw [key] at hx
  have h5 := congrArg Complex.re hx
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.re_sum, Complex.ofReal_re,
    Complex.zero_re] at h5
  have hz : z = 0 := funext fun i => by
    have h6 := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => Complex.normSq_nonneg _).1 h5 i (Finset.mem_univ i)
    simpa using h6
  rw [hxz, hz, Matrix.mulVec_zero]

theorem eq_zero_of_hasSig {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M n 0 ∨ HasSig M 0 n) (x : Fin n → ℂ)
    (hx : x ⬝ᵥ M *ᵥ star x = 0) : x = 0 := by
  rcases h with ⟨-, A, hA⟩ | ⟨-, A, hA⟩
  · refine eq_zero_of_congr_one (A := A) (M := M) (Equiv.sumEmpty (Fin n) (Fin 0)) ?_ x hx
    rw [hA]; ext i j
    rcases i with i | i
    · rcases j with j | j
      · simp [Matrix.one_apply]
      · exact j.elim0
    · exact i.elim0
  · refine eq_zero_of_congr_one (A := A) (M := -M) (Equiv.emptySum (Fin 0) (Fin n)) ?_ x ?_
    · rw [Matrix.mul_neg, Matrix.neg_mul, hA]; ext i j
      rcases i with i | i
      · exact i.elim0
      · rcases j with j | j
        · exact j.elim0
        · simp [Matrix.one_apply]
    · rw [Matrix.neg_mulVec, dotProduct_neg, hx, neg_zero]

end GlobalTheory.DefiniteAniso

namespace GlobalTheory

theorem DefiniteAniso.anisotropic_of_definite : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ {B : Base F E} {n : ℕ} {X : Spc F E n}, (X.IsHerm σ B n 0 ∨ X.IsHerm σ B 0 n) → ∀ (x : Fin n → E), form σ X.J x x = 0 → x = 0 := by
  intro F E _ _ _ _ _ σ h B n X hX x hx
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hs : HasSig (X.J.map (B.emb w).1) n 0 ∨ HasSig (X.J.map (B.emb w).1) 0 n :=
    hX.imp (fun h => h.sig w) fun h => h.sig w
  have h1 := congrArg (B.emb w).1 hx
  have h2 := DefiniteAniso.eq_zero_of_hasSig hs (fun i => (B.emb w).1 (x i)) (by
    rw [map_zero] at h1
    rw [← h1]
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, h.2.2.2, Matrix.map_apply, Pi.star_apply])
  funext i
  simpa using congrFun h2 i

end GlobalTheory
