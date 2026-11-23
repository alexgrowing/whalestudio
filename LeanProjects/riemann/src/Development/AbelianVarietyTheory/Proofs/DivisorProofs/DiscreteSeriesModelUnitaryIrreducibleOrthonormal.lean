import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.ModelRep

section Conj

variable {n : ℕ} {ε : Fin n → Bool} {P G : Matrix (Fin n) (Fin n) ℂ}

theorem conj_mem (hP : IsUnit P) (hG : Pᴴ * Formalism.REAL.Jm ε * P = G) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH G) : P * g * P⁻¹ ∈ UJset ε := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have hg' : gᴴ * G * g = G := hg
  show (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) = Formalism.REAL.Jm ε
  calc (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹)
      = (P⁻¹)ᴴ * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * P⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
        rw [hG, hg', ← hG]; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1]; simp

theorem conj_mem_inv (hP : IsUnit P) (hG : Pᴴ * Formalism.REAL.Jm ε * P = G) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) : P⁻¹ * g * P ∈ Formalism.QuantumDeterminants.UH G := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  show (P⁻¹ * g * P)ᴴ * G * (P⁻¹ * g * P) = G
  calc (P⁻¹ * g * P)ᴴ * G * (P⁻¹ * g * P)
      = Pᴴ * (gᴴ * ((P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹)) * g) * P := by
        rw [← hG]; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = G := by
        rw [h1, conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hg', hG]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem isURepOn_conj (hP : IsUnit P) (hG : Pᴴ * Formalism.REAL.Jm ε * P = G) (hσ : IsURepOn (UJset ε) σ) :
    IsURepOn (Formalism.QuantumDeterminants.UH G) (fun g => σ (P * g * P⁻¹)) := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  obtain ⟨⟨ha, hb⟩, hc, hd⟩ := hσ
  refine ⟨⟨?_, ?_⟩, fun g hg v => hc _ (conj_mem hP hG hg) v, fun v => ?_⟩
  · simpa only [Matrix.mul_one, h1] using ha
  · intro a ha' b hb'
    have e : P * (a * b) * P⁻¹ = (P * a * P⁻¹) * (P * b * P⁻¹) := by
      calc P * (a * b) * P⁻¹ = P * a * (P⁻¹ * P) * b * P⁻¹ := by rw [h2]; simp only [Matrix.mul_assoc, Matrix.one_mul]
        _ = _ := by simp only [Matrix.mul_assoc]
    show σ (P * (a * b) * P⁻¹) = _
    rw [e]
    exact hb _ (conj_mem hP hG ha') _ (conj_mem hP hG hb')
  · have hc : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => P * g * P⁻¹ :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact (hd v).comp hc.continuousOn fun g hg => conj_mem hP hG hg

theorem isIrredOn_conj (hP : IsUnit P) (hG : Pᴴ * Formalism.REAL.Jm ε * P = G) (hσ : IsIrredOn (UJset ε) σ) :
    IsIrredOn (Formalism.QuantumDeterminants.UH G) (fun g => σ (P * g * P⁻¹)) := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  intro S hS h
  refine hσ S hS fun g hg v hv => ?_
  have := h _ (conj_mem_inv hP hG hg) v hv
  have e : P * (P⁻¹ * g * P) * P⁻¹ = g := by
    calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [h1]; simp
  simpa only [e] using this

theorem arr_injective {q : ℕ} (hq : q ≤ n) : Function.Injective (arr q : Fin n → Fin n) := by
  intro a b h
  have h' := congrArg Fin.val h
  have := a.2
  have := b.2
  apply Fin.ext
  unfold arr at h'
  split_ifs at h' <;> simp only at h' <;> omega

def arrEquiv {q : ℕ} (hq : q ≤ n) : Fin n ≃ Fin n :=
  Equiv.ofBijective (arr q) (Finite.injective_iff_bijective.1 (arr_injective hq))

theorem orth_sub (hP : IsUnit P) (hG : Pᴴ * Formalism.REAL.Jm ε * P = G) (f : Fin n → Fin n) :
    ((P⁻¹).submatrix id f)ᴴ * G * (P⁻¹).submatrix id f = (Formalism.REAL.Jm ε).submatrix f f := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h3 : (P⁻¹)ᴴ * G * P⁻¹ = Formalism.REAL.Jm ε := by
    calc (P⁻¹)ᴴ * G * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
          rw [← hG]; simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp
  rw [← h3]
  rfl

theorem conj_single (hP : IsUnit P) (e : Fin n ≃ Fin n) (a c : Fin n) :
    (P⁻¹).submatrix id e * Matrix.single a c 1 * ((P⁻¹).submatrix id e)⁻¹ =
      P⁻¹ * Matrix.single (e a) (e c) 1 * P := by
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h3 : ((P⁻¹).submatrix id e)⁻¹ = P.submatrix e id := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.submatrix_mul_equiv, h2]
    rfl
  have h4 : (Matrix.single a c 1 : Matrix (Fin n) (Fin n) ℂ) = (Matrix.single (e a) (e c) 1).submatrix e e := by
    ext i j
    simp [Matrix.single_apply]
  rw [h3, h4, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  rfl

end Conj

theorem model_rep : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau), CompleteSpace (M.H τ) ∧ IsURepOn (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (M.rep τ) ∧ IsIrredOn (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (M.rep τ) ∧ (HolShape M → OrthFr (gramAt D V τ) (nNeg (M.ε τ)) (x0Mat M τ) ∧ ∀ a c, x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹ = (M.fr τ)⁻¹ * Matrix.single (arr (nNeg (M.ε τ)) a) (arr (nNeg (M.ε τ)) c) 1 * M.fr τ) := by
  intro D V S M τ
  obtain ⟨h1, -, h3, h4, -⟩ := M.ds τ
  refine ⟨h1, isURepOn_conj (M.fr_unit τ) (M.fr_gram τ) h3, isIrredOn_conj (M.fr_unit τ) (M.fr_gram τ) h4, fun hs => ⟨⟨nNeg_le _, ?_⟩, fun a c => ?_⟩⟩
  · obtain ⟨-, p, hp, h⟩ := hs τ
    have := orth_sub (M.fr_unit τ) (M.fr_gram τ) (arr (nNeg (M.ε τ)))
    refine this.trans ?_
    have hinj := arr_injective (nNeg_le (M.ε τ))
    unfold Formalism.REAL.Jm
    rw [Matrix.submatrix_diagonal _ _ hinj]
    congr 1
    funext a
    have := a.2
    simp only [Function.comp, h, nNeg_shape hp h, ReciprocityTheory.ChartRestriction.G.FD.sgn, arr, decide_eq_true_eq]
    split_ifs <;> first | (simp; done) | (exfalso; simp only at *; omega)
  · exact conj_single (M.fr_unit τ) (arrEquiv (nNeg_le (M.ε τ))) a c

end GlobalTheory.HolDict.ModelRep
