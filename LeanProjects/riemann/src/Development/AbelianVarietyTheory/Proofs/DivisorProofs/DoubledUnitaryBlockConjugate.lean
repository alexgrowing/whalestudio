import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagColsZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLeviElement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.DblWitt

open Matrix GlobalTheory.PlaneLeviExt

variable {E : Type} [Field E] [NumberField E]

def q₁ : Matrix (Fin 2) (Fin 2) E := !![2⁻¹, 2⁻¹; -2⁻¹, 2⁻¹]

def q₂ : Matrix (Fin 2) (Fin 2) E := !![2⁻¹, 2⁻¹; 2⁻¹, -2⁻¹]

def q₃ : Matrix (Fin 2) (Fin 2) E := !![2⁻¹, -2⁻¹; -2⁻¹, -2⁻¹]

def q₄ : Matrix (Fin 2) (Fin 2) E := !![2⁻¹, -2⁻¹; 2⁻¹, 2⁻¹]

def rot (d₁ : ℕ) : Matrix ((Fin d₁ ⊕ Fin 2) ⊕ (Fin d₁ ⊕ Fin 2)) ((Fin d₁ ⊕ Fin 2) ⊕ (Fin d₁ ⊕ Fin 2)) E :=
  fromBlocks (fromBlocks 1 0 0 q₁) (fromBlocks 0 0 0 q₂) (fromBlocks 0 0 0 q₃) (fromBlocks 1 0 0 q₄)

def sd (d₁ : ℕ) : Matrix (Fin 2 ⊕ Fin d₁) (Fin d₁ ⊕ Fin 2) E := fromBlocks 0 !![1, 1; 1, -1] 1 0

def sdInv (d₁ : ℕ) : Matrix (Fin d₁ ⊕ Fin 2) (Fin 2 ⊕ Fin d₁) E := fromBlocks 0 1 !![2⁻¹, 2⁻¹; 2⁻¹, -2⁻¹] 0

def lagCoord (d₁ : ℕ) : Matrix ((Fin d₁ ⊕ Fin 2) ⊕ (Fin d₁ ⊕ Fin 2)) (Fin 2 ⊕ Fin d₁) E :=
  fromRows (fromBlocks 0 1 !![1, 0; 0, 0] 0) (fromBlocks 0 1 !![0, 1; 0, 0] 0)

theorem two_by_two :
    (q₁ᵀ * (hyp : Matrix (Fin 2) (Fin 2) E) * q₁ + -(q₃ᵀ * hyp * q₃) = hyp) ∧ (q₁ᵀ * (hyp : Matrix (Fin 2) (Fin 2) E) * q₂ + -(q₃ᵀ * hyp * q₄) = 0) ∧
    (q₂ᵀ * (hyp : Matrix (Fin 2) (Fin 2) E) * q₁ + -(q₄ᵀ * hyp * q₃) = 0) ∧ (q₂ᵀ * (hyp : Matrix (Fin 2) (Fin 2) E) * q₂ + -(q₄ᵀ * hyp * q₄) = -hyp) ∧
    (q₁ * q₁ᵀ + q₂ * q₂ᵀ = (1 : Matrix (Fin 2) (Fin 2) E)) ∧ (q₁ * q₃ᵀ + q₂ * q₄ᵀ = (0 : Matrix (Fin 2) (Fin 2) E)) ∧
    (q₃ * q₁ᵀ + q₄ * q₂ᵀ = (0 : Matrix (Fin 2) (Fin 2) E)) ∧ (q₃ * q₃ᵀ + q₄ * q₄ᵀ = (1 : Matrix (Fin 2) (Fin 2) E)) ∧
    (q₁ + q₂ = !![(1 : E), 1; 0, 0]) ∧ (q₃ + q₄ = !![(1 : E), -1; 0, 0]) ∧
    ((!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) E) * !![2⁻¹, 2⁻¹; 2⁻¹, -2⁻¹] = 1) ∧ ((!![2⁻¹, 2⁻¹; 2⁻¹, -2⁻¹] : Matrix (Fin 2) (Fin 2) E) * !![1, 1; 1, -1] = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [q₁, q₂, q₃, q₄, hyp, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.vecMul, dotProduct, Matrix.transpose_apply] <;> ring

end GlobalTheory.DblWitt

namespace GlobalTheory.DblWitt
open Matrix GlobalTheory.PlaneLeviExt
variable {E : Type} [Field E] [NumberField E]

theorem rot_gram {d₁ : ℕ} (J₁ : Matrix (Fin d₁) (Fin d₁) E) :
    (rot d₁)ᵀ * dbl (fromBlocks J₁ 0 0 hyp) * rot d₁ = dbl (fromBlocks J₁ 0 0 (hyp : Matrix (Fin 2) (Fin 2) E)) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := two_by_two (E := E)
  simp only [rot, dbl, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_neg, transpose_one, transpose_zero,
    Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add, neg_zero, Matrix.mul_neg,
    Matrix.neg_mul, fromBlocks_add, h1, h2, h3, h4, fromBlocks_zero]

theorem rot_mul_transpose (d₁ : ℕ) :
    rot d₁ * (rot d₁)ᵀ = (1 : Matrix ((Fin d₁ ⊕ Fin 2) ⊕ (Fin d₁ ⊕ Fin 2)) ((Fin d₁ ⊕ Fin 2) ⊕ (Fin d₁ ⊕ Fin 2)) E) := by
  obtain ⟨-, -, -, -, h5, h6, h7, h8, -⟩ := two_by_two (E := E)
  simp only [rot, fromBlocks_transpose, fromBlocks_multiply, transpose_one, transpose_zero, fromBlocks_add,
    Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add, h5, h6, h7, h8,
    fromBlocks_one, fromBlocks_zero]

theorem rot_diag (d₁ : ℕ) :
    (rot d₁ : Matrix ((Fin d₁ ⊕ Fin 2) ⊕ (Fin d₁ ⊕ Fin 2)) ((Fin d₁ ⊕ Fin 2) ⊕ (Fin d₁ ⊕ Fin 2)) E) *
      (diagCols (Fin d₁ ⊕ Fin 2) : Matrix ((Fin d₁ ⊕ Fin 2) ⊕ (Fin d₁ ⊕ Fin 2)) (Fin d₁ ⊕ Fin 2) E) =
      (lagCoord d₁ : Matrix ((Fin d₁ ⊕ Fin 2) ⊕ (Fin d₁ ⊕ Fin 2)) (Fin 2 ⊕ Fin d₁) E) *
        (sd d₁ : Matrix (Fin 2 ⊕ Fin d₁) (Fin d₁ ⊕ Fin 2) E) := by
  obtain ⟨-, -, -, -, -, -, -, -, h9, h10, -⟩ := two_by_two (E := E)
  simp only [rot, diagCols, lagCoord, sd, fromBlocks_mul_fromRows, fromRows_mul, fromBlocks_multiply, fromBlocks_add,
    Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add, h9, h10]
  have e1 : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) E) * !![1, 1; 1, -1] = !![1, 1; 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e2 : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) E) * !![1, 1; 1, -1] = !![1, -1; 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [e1, e2]

theorem sd_sdInv (d₁ : ℕ) : (sd d₁ : Matrix (Fin 2 ⊕ Fin d₁) (Fin d₁ ⊕ Fin 2) E) *
      (sdInv d₁ : Matrix (Fin d₁ ⊕ Fin 2) (Fin 2 ⊕ Fin d₁) E) = 1 ∧
    (sdInv d₁ : Matrix (Fin d₁ ⊕ Fin 2) (Fin 2 ⊕ Fin d₁) E) * (sd d₁ : Matrix (Fin 2 ⊕ Fin d₁) (Fin d₁ ⊕ Fin 2) E) = 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h11, h12⟩ := two_by_two (E := E)
  constructor <;> simp only [sd, sdInv, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
    Matrix.one_mul, add_zero, zero_add, h11, h12, fromBlocks_one]

end GlobalTheory.DblWitt

namespace GlobalTheory.DblWitt
open Matrix GlobalTheory.PlaneLeviExt

theorem frame_lagCoord {E : Type} [Field E] [NumberField E] {d d₁ : ℕ} (H' : Plane E d d₁) :
    (fromBlocks (frame H') 0 0 (frame H') : Matrix (Fin d ⊕ Fin d) ((Fin d₁ ⊕ Fin 2) ⊕ (Fin d₁ ⊕ Fin 2)) E) *
      (lagCoord d₁ : Matrix ((Fin d₁ ⊕ Fin 2) ⊕ (Fin d₁ ⊕ Fin 2)) (Fin 2 ⊕ Fin d₁) E) =
      GlobalTheory.DblSiegel.lagCols H'.x H'.ι := by
  ext (r | r) (k | k)
  all_goals first
    | (fin_cases k <;> simp [lagCoord, frame, twoCols, GlobalTheory.DblSiegel.lagCols, Matrix.mul_apply, Fintype.sum_sum_type,
        Fin.sum_univ_two, Matrix.one_apply])
    | simp [lagCoord, frame, twoCols, GlobalTheory.DblSiegel.lagCols, Matrix.mul_apply, Fintype.sum_sum_type,
        Fin.sum_univ_two, Matrix.one_apply]

end GlobalTheory.DblWitt

namespace GlobalTheory.DblWitt
open Matrix GlobalTheory.PlaneLeviExt

theorem exists_unitary_diag_lag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r' s' r₁ s₁ : ℕ),
    W.IsSkew σ B r' s' → W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∃ (γ : UG (cA σ) (dbl (incM F W.J))) (S : Matrix (Fin 2 ⊕ Fin d₁) (Fin d) (AE F E))
      (S' : Matrix (Fin d) (Fin 2 ⊕ Fin d₁) (AE F E)),
      ((γ : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) *
          (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) =
        GlobalTheory.DblSiegel.lagCols (incV F H'.x) (incM F H'.ι) * S ∧ S * S' = 1 ∧ S' * S = 1 := by
  intro F E _ _ _ _ _ σ B hB d d₁ W W₁ H' i₀ i₁ r' s' r₁ s₁ hW hW₁ hA
  have hσ : ∀ z, σ (σ z) = z := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    intro z; apply τ.injective; rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]
  have hmm : ∀ {l m n : Type} [Fintype m] (X : Matrix l m E) (Y : Matrix m n E), (X * Y).map σ = X.map σ * Y.map σ :=
    fun X Y => Matrix.map_mul (f := (σ : E →+* E))
  have hu := isUnit_sq σ hσ B hW hW₁ hA
  have hPQ := frame_mul_coframe hA.rank H' hu
  have hQP := coframe_mul_frame hA.rank H' hu
  have hG := gram_frame σ hσ B hW hA
  set P := frame H' with hPdef
  set Q := coframe hA.rank H' with hQdef
  have hPQσ : P.map σ * Q.map σ = 1 := by rw [← hmm, hPQ, Matrix.map_one _ (map_zero σ) (map_one σ)]
  have hJ : Qᵀ * fromBlocks W₁.J 0 0 hyp * Q.map σ = W.J := by
    rw [← hG]
    calc Qᵀ * (Pᵀ * W.J * P.map σ) * Q.map σ = (P * Q)ᵀ * W.J * (P.map σ * Q.map σ) := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = W.J := by rw [hPQ, hPQσ, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  let Pd : Matrix (Fin d ⊕ Fin d) ((Fin d₁ ⊕ Fin 2) ⊕ (Fin d₁ ⊕ Fin 2)) E := fromBlocks P 0 0 P
  let Qd : Matrix ((Fin d₁ ⊕ Fin 2) ⊕ (Fin d₁ ⊕ Fin 2)) (Fin d ⊕ Fin d) E := fromBlocks Q 0 0 Q
  have hQdPd : Qd * Pd = 1 := by
    simp only [Qd, Pd, fromBlocks_multiply, hQP, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, fromBlocks_one]
  have hPdQd : Pd * Qd = 1 := by
    simp only [Qd, Pd, fromBlocks_multiply, hPQ, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, fromBlocks_one]
  let T : Matrix (Fin 2 ⊕ Fin d₁) (Fin d₁ ⊕ Fin 2) E := sd d₁
  let Ti : Matrix (Fin d₁ ⊕ Fin 2) (Fin 2 ⊕ Fin d₁) E := sdInv d₁
  let R : Matrix ((Fin d₁ ⊕ Fin 2) ⊕ (Fin d₁ ⊕ Fin 2)) ((Fin d₁ ⊕ Fin 2) ⊕ (Fin d₁ ⊕ Fin 2)) E := rot d₁
  let g₀ : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) E := Pd * R * Qd
  let g₁ : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) E := Pd * Rᵀ * Qd
  have hT : T * Ti = 1 := (sd_sdInv d₁).1
  have hT' : Ti * T = 1 := (sd_sdInv d₁).2
  have hRR : R * Rᵀ = 1 := rot_mul_transpose d₁
  have hRR' : Rᵀ * R = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp hRR
  have h01 : g₀ * g₁ = 1 := by
    calc g₀ * g₁ = Pd * (R * (Qd * Pd) * Rᵀ) * Qd := by simp only [g₀, g₁, Matrix.mul_assoc]
      _ = 1 := by rw [hQdPd, Matrix.mul_one, hRR, Matrix.mul_one, hPdQd]
  have h10 : g₁ * g₀ = 1 := by
    calc g₁ * g₀ = Pd * (Rᵀ * (Qd * Pd) * R) * Qd := by simp only [g₀, g₁, Matrix.mul_assoc]
      _ = 1 := by rw [hQdPd, Matrix.mul_one, hRR', Matrix.mul_one, hPdQd]
  have hmap : ∀ (a b c e : E), σ a = a → σ b = b → σ c = c → σ e = e →
      (!![a, b; c, e] : Matrix (Fin 2) (Fin 2) E).map σ = !![a, b; c, e] := by
    intro a b c e ha hb hc he; ext i j; fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, he]
  have h2 : σ (2⁻¹) = 2⁻¹ := by simp [map_inv₀, map_ofNat]
  have h2' : σ (-2⁻¹) = -2⁻¹ := by simp [map_neg, h2]
  have hRσ : R.map σ = R := by
    simp only [R, rot, q₁, q₂, q₃, q₄, Matrix.fromBlocks_map, hmap _ _ _ _ h2 h2 h2' h2, hmap _ _ _ _ h2 h2 h2 h2',
      hmap _ _ _ _ h2 h2' h2' h2', hmap _ _ _ _ h2 h2' h2 h2, Matrix.map_zero _ (map_zero σ), Matrix.map_one _ (map_zero σ) (map_one σ)]
  have hPd : Pdᵀ * dbl W.J * Pd.map σ = dbl (fromBlocks W₁.J 0 0 hyp) := by
    simp only [Pd, dbl, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, transpose_zero, Matrix.map_zero _ (map_zero σ),
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul, hG, neg_zero]
  have hQd : Qdᵀ * dbl (fromBlocks W₁.J 0 0 hyp) * Qd.map σ = dbl W.J := by
    simp only [Qd, dbl, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, transpose_zero, Matrix.map_zero _ (map_zero σ),
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul, hJ, neg_zero]
  have hunit : g₀ᵀ * dbl W.J * g₀.map σ = dbl W.J := by
    calc g₀ᵀ * dbl W.J * g₀.map σ = Qdᵀ * (Rᵀ * (Pdᵀ * dbl W.J * Pd.map σ) * R.map σ) * Qd.map σ := by
          simp only [g₀, Matrix.transpose_mul, hmm, Matrix.mul_assoc]
      _ = dbl W.J := by rw [hPd, hRσ, show Rᵀ * dbl (fromBlocks W₁.J 0 0 hyp) * R = dbl (fromBlocks W₁.J 0 0 hyp) from rot_gram W₁.J, hQd]
  have h1 : Qd * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) E) =
      (diagCols (Fin d₁ ⊕ Fin 2) : Matrix ((Fin d₁ ⊕ Fin 2) ⊕ (Fin d₁ ⊕ Fin 2)) (Fin d₁ ⊕ Fin 2) E) * Q := by
    simp only [Qd, diagCols, fromBlocks_mul_fromRows, fromRows_mul, Matrix.mul_one, Matrix.one_mul, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, zero_add]
  have hdiag : g₀ * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) E) = GlobalTheory.DblSiegel.lagCols H'.x H'.ι * (T * Q) := by
    calc g₀ * (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) E) =
          Pd * (R * (diagCols (Fin d₁ ⊕ Fin 2) : Matrix ((Fin d₁ ⊕ Fin 2) ⊕ (Fin d₁ ⊕ Fin 2)) (Fin d₁ ⊕ Fin 2) E)) * Q := by
          simp only [g₀, Matrix.mul_assoc, h1]
      _ = Pd * (lagCoord d₁ : Matrix ((Fin d₁ ⊕ Fin 2) ⊕ (Fin d₁ ⊕ Fin 2)) (Fin 2 ⊕ Fin d₁) E) * (T * Q) := by
          rw [show R * (diagCols (Fin d₁ ⊕ Fin 2) : Matrix ((Fin d₁ ⊕ Fin 2) ⊕ (Fin d₁ ⊕ Fin 2)) (Fin d₁ ⊕ Fin 2) E) = _ from rot_diag d₁]
          simp only [T, Matrix.mul_assoc]
      _ = _ := by rw [frame_lagCoord]
  have hdbl : dbl (incM F W.J) = incM F (dbl W.J) := by
    ext (i | i) (j | j) <;> simp [dbl, incM]
  let γ : UG (cA σ) (dbl (incM F W.J)) := ⟨⟨incM F g₀, incM F g₁, by rw [← incM_mul, h01, incM_one],
    by rw [← incM_mul, h10, incM_one]⟩, by
      show (incM F g₀)ᵀ * dbl (incM F W.J) * (incM F g₀).map (cA σ) = dbl (incM F W.J)
      rw [hdbl, cA_incM, ← incM_transpose, ← incM_mul, ← incM_mul, hunit]⟩
  let S₀ : Matrix (Fin 2 ⊕ Fin d₁) (Fin d) E := T * Q
  let S₀' : Matrix (Fin d) (Fin 2 ⊕ Fin d₁) E := P * Ti
  have hS : S₀ * S₀' = 1 := by
    calc S₀ * S₀' = T * (Q * P) * Ti := by simp only [S₀, S₀', Matrix.mul_assoc]
      _ = 1 := by rw [hQP, Matrix.mul_one, hT]
  have hS' : S₀' * S₀ = 1 := by
    calc S₀' * S₀ = P * (Ti * T) * Q := by simp only [S₀, S₀', Matrix.mul_assoc]
      _ = 1 := by rw [hT', Matrix.mul_one, hPQ]
  refine ⟨γ, incM F S₀, incM F S₀', ?_, ?_, ?_⟩
  · have hdc : (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) = incM F (diagCols (Fin d)) := by
      ext (i | i) j <;> by_cases h : i = j <;> simp [diagCols, incM, Matrix.one_apply, h]
    have hlc : GlobalTheory.DblSiegel.lagCols (incV F H'.x) (incM F H'.ι) = incM F (GlobalTheory.DblSiegel.lagCols H'.x H'.ι) := by
      ext (i | i) (k | k) <;> (try fin_cases k) <;> simp [GlobalTheory.DblSiegel.lagCols, incM, incV]
    rw [show ((γ : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) = incM F g₀ from rfl,
      hdc, hlc, ← incM_mul, ← incM_mul, hdiag]
  · rw [← incM_mul, hS, incM_one]
  · rw [← incM_mul, hS', incM_one]

end GlobalTheory.DblWitt
