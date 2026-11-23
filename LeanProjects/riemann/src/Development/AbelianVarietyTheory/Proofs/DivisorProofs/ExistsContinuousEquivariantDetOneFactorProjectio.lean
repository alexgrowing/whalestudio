import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.Proj

variable {p q r : ℕ}

theorem Jpq_eq_diagonal (p q : ℕ) :
    Formalism.UG.Jpq p q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem det_Jpq_ne (p q : ℕ) : (Formalism.UG.Jpq p q).det ≠ 0 := by
  rw [Jpq_eq_diagonal, Matrix.det_diagonal]
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  rcases i with i | i <;> simp

theorem star_det_mul_det (u : UpqT p q) : star (UpqT.mat u).det * (UpqT.mat u).det = 1 := by
  have h := congrArg Matrix.det (GlobalTheory.UpqExpChart.mat_unitary u)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h
  have hJ := det_Jpq_ne p q
  apply mul_left_cancel₀ hJ
  linear_combination h

theorem det_mat_ne (u : UpqT p q) : (UpqT.mat u).det ≠ 0 := by
  intro h
  have := star_det_mul_det u
  rw [h, mul_zero] at this
  exact zero_ne_one this

theorem dg_unitary (a₀ : Fin p ⊕ Fin q) (z : ℂ) (hz : star z * z = 1) :
    (dg a₀ z)ᴴ * Formalism.UG.Jpq p q * dg a₀ z = Formalism.UG.Jpq p q := by
  rw [Jpq_eq_diagonal, dg, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases h : i = a₀
  · subst h
    simp only [Pi.star_apply, Function.update_self]
    linear_combination (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) i) * hz
  · simp [Function.update_of_ne h]

theorem det_sMat (a₀ : Fin p ⊕ Fin q) (u : UpqT p q) : (sMat a₀ u).det = 1 := by
  rw [sMat, Matrix.det_mul, det_dg, mul_inv_cancel₀ (det_mat_ne u)]

theorem sMat_unitary (a₀ : Fin p ⊕ Fin q) (u : UpqT p q) :
    (sMat a₀ u)ᴴ * Formalism.UG.Jpq p q * sMat a₀ u = Formalism.UG.Jpq p q := by
  have hz : star (UpqT.mat u).det⁻¹ * (UpqT.mat u).det⁻¹ = 1 := by
    rw [star_inv₀, ← mul_inv, star_det_mul_det, inv_one]
  have h1 := GlobalTheory.UpqExpChart.mat_unitary u
  have h2 := dg_unitary a₀ _ hz
  calc _ = (dg a₀ (UpqT.mat u).det⁻¹)ᴴ * ((UpqT.mat u)ᴴ * Formalism.UG.Jpq p q * UpqT.mat u) *
        dg a₀ (UpqT.mat u).det⁻¹ := by
        simp only [sMat, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1, h2]

theorem continuous_sMat (a₀ : Fin p ⊕ Fin q) : Continuous (sMat a₀ : UpqT p q → _) := by
  unfold sMat dg
  refine GlobalTheory.UpqExpChart.continuous_mat.matrix_mul (Continuous.matrix_diagonal ?_)
  exact continuous_const.update a₀
    (GlobalTheory.UpqExpChart.continuous_mat.matrix_det.inv₀ det_mat_ne)

theorem sMat_mul (a₀ : Fin p ⊕ Fin q) (u v : UpqT p q) (hu : (UpqT.mat u).det = 1) :
    sMat a₀ (u * v) = UpqT.mat u * sMat a₀ v := by
  have h : UpqT.mat (u * v) = UpqT.mat u * UpqT.mat v := rfl
  rw [sMat, sMat, h, Matrix.det_mul, hu, one_mul, Matrix.mul_assoc]

theorem det_conj {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι ≃ Fin r) (A : Matrix ι (Fin r) ℂ)
    (B : Matrix (Fin r) ι ℂ) (hAB : A * B = 1) (S : Matrix ι ι ℂ) : (B * S * A).det = S.det := by
  have h1 : (B * S * A).submatrix e e = B.submatrix e id * S * A.submatrix id e := by
    ext i j
    simp [Matrix.mul_apply]
  have h2 : A.submatrix id e * B.submatrix e id = 1 := by
    rw [Matrix.submatrix_mul_equiv, hAB]
    rfl
  rw [← Matrix.det_submatrix_equiv_self e, h1, Matrix.det_mul_comm, ← Matrix.mul_assoc, h2, Matrix.one_mul]

def gl (a₀ : Fin p ⊕ Fin q) (A : Matrix (Fin p ⊕ Fin q) (Fin r) ℂ) (B : Matrix (Fin r) (Fin p ⊕ Fin q) ℂ)
    (hAB : A * B = 1) (hBA : B * A = 1) (u : UpqT p q) : GL (Fin r) ℂ where
  val := B * sMat a₀ u * A
  inv := B * (sMat a₀ u).adjugate * A
  val_inv := by
    calc _ = B * (sMat a₀ u * (A * B) * (sMat a₀ u).adjugate) * A := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hAB, Matrix.mul_one, Matrix.mul_adjugate, det_sMat, one_smul, Matrix.mul_one, hBA]
  inv_val := by
    calc _ = B * ((sMat a₀ u).adjugate * (A * B) * sMat a₀ u) * A := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hAB, Matrix.mul_one, Matrix.adjugate_mul, det_sMat, one_smul, Matrix.mul_one, hBA]

section
variable (a₀ : Fin p ⊕ Fin q) (A : Matrix (Fin p ⊕ Fin q) (Fin r) ℂ) (B : Matrix (Fin r) (Fin p ⊕ Fin q) ℂ)
    (hAB : A * B = 1) (hBA : B * A = 1)

theorem gl_val (u : UpqT p q) :
    (gl a₀ A B hAB hBA u : Matrix (Fin r) (Fin r) ℂ) = B * sMat a₀ u * A := rfl

theorem continuous_gl : Continuous (gl a₀ A B hAB hBA) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_const.matrix_mul (continuous_sMat a₀)).matrix_mul continuous_const
  · exact (continuous_const.matrix_mul (continuous_sMat a₀).matrix_adjugate).matrix_mul continuous_const

theorem mul_gl (u : UpqT p q) :
    A * (gl a₀ A B hAB hBA u : Matrix (Fin r) (Fin r) ℂ) = sMat a₀ u * A := by
  rw [gl_val, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hAB, Matrix.one_mul]

theorem gl_keeps (H : Matrix (Fin r) (Fin r) ℂ) (hH : Aᴴ * Formalism.UG.Jpq p q * A = -Hᵀ) (u : UpqT p q) :
    (gl a₀ A B hAB hBA u : Matrix (Fin r) (Fin r) ℂ)ᵀ * H *
      (gl a₀ A B hAB hBA u : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) = H := by
  have hm := mul_gl a₀ A B hAB hBA u
  generalize (gl a₀ A B hAB hBA u : Matrix (Fin r) (Fin r) ℂ) = g at hm ⊢
  have h : gᴴ * (-Hᵀ) * g = -Hᵀ := by
    calc _ = (A * g)ᴴ * Formalism.UG.Jpq p q * (A * g) := by
          rw [← hH]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Aᴴ * ((sMat a₀ u)ᴴ * Formalism.UG.Jpq p q * sMat a₀ u) * A := by
          rw [hm]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [sMat_unitary, hH]
  rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj] at h
  have h' := congrArg Matrix.transpose h
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc] at h'
  exact h'

end

theorem exists_proj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) [Fintype κ] (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r) (a₀ : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ)), IsIdent p q Ψ G x σ A e → ∃ π : (∀ ρ, UpqT (p ρ) (q ρ)) → realSU Ψ G, Continuous π ∧ IsProj p q Ψ G σ A a₀ π ∧ (∀ (s : realSU Ψ G) (b₀ : ∀ ρ, UpqT (p ρ) (q ρ)), (∀ ρ, UpqT.mat (b₀ ρ) * A ρ = A ρ * ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) → ∀ b, π (b₀ * b) = s * π b) := by
  intro E _ _ _ r κ _ p q Ψ G x σ A e a₀ hI
  let B : ∀ ρ, Matrix (Fin r) (Fin (p ρ) ⊕ Fin (q ρ)) ℂ := fun ρ => mat x (σ ρ) * (permM (e ρ))ᵀ
  have hAB : ∀ ρ, A ρ * B ρ = 1 := fun ρ => by
    simp only [B]
    rw [← Matrix.mul_assoc, (hI ρ).2, permM_mul_transpose]
  have hBA : ∀ ρ, B ρ * A ρ = 1 := fun ρ => (Matrix.mul_eq_one_comm_of_equiv (e ρ)).1 (hAB ρ)
  let F : (∀ ρ, UpqT (p ρ) (q ρ)) → κ → GL (Fin r) ℂ :=
    fun b ρ => gl (a₀ ρ) (A ρ) (B ρ) (hAB ρ) (hBA ρ) (b ρ)
  have hF : ∀ b ρ, F b (σ.symm (σ ρ)) = gl (a₀ ρ) (A ρ) (B ρ) (hAB ρ) (hBA ρ) (b ρ) := fun b ρ => by
    rw [Equiv.symm_apply_apply]
  have hmem : ∀ b, (fun τ => F b (σ.symm τ)) ∈ realSU Ψ G := fun b => by
    rw [DensOne.mem_realSU_iff]
    intro τ
    obtain ⟨ρ, rfl⟩ := σ.surjective τ
    simp only [hF]
    exact ⟨gl_keeps _ _ _ _ _ _ (hI ρ).1 _, by rw [gl_val, det_conj (e ρ) _ _ (hAB ρ), det_sMat]⟩
  refine ⟨fun b => ⟨_, hmem b⟩, ?_, ?_, ?_⟩
  · refine Continuous.subtype_mk (continuous_pi fun τ => ?_) _
    exact (continuous_gl _ _ _ _ _).comp (continuous_apply _)
  · intro b ρ
    simp only [hF]
    exact mul_gl _ _ _ _ _ _
  · intro s b₀ hs b
    refine Subtype.ext (funext fun τ => ?_)
    obtain ⟨ρ, rfl⟩ := σ.surjective τ
    apply Units.ext
    change ((F (b₀ * b) (σ.symm (σ ρ)) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      (s.1 (σ ρ) : GL (Fin r) ℂ) * ((F b (σ.symm (σ ρ)) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)
    have h1 : ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = B ρ * UpqT.mat (b₀ ρ) * A ρ := by
      rw [Matrix.mul_assoc, hs ρ, ← Matrix.mul_assoc, hBA, Matrix.one_mul]
    have h2 : (UpqT.mat (b₀ ρ)).det = 1 := by
      rw [← det_conj (e ρ) _ _ (hAB ρ), ← h1]
      exact (((DensOne.mem_realSU_iff Ψ G _).1 s.2) (σ ρ)).2
    rw [hF, hF, gl_val, gl_val, h1, Pi.mul_apply, sMat_mul _ _ _ h2]
    calc _ = B ρ * UpqT.mat (b₀ ρ) * (A ρ * B ρ) * sMat (a₀ ρ) (b ρ) * A ρ := by
          rw [hAB]; simp only [Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]

end GlobalTheory.CovTop.VolUp.Proj
