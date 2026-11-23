import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.gramq :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (h : HS L N), (gram h).IsHermitian ∧
    (∀ x : Fin N × BI L → ℝ, x ⬝ᵥ (gram h *ᵥ x) = qR h (realVec x)) ∧
    (∀ c : Fin N × BI L → ℤ, realVec (fun s => (c s : ℝ)) = toR (intVec c)) ∧
    Function.Bijective (intVec : (Fin N × BI L → ℤ) → Lat L N) := by
  intro L _ _ N h
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Matrix.IsHermitian.ext fun s t => ?_
    simp only [gram, of_apply, star_trivial]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← (mat_herm h w).apply t.1 s.1]
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.mul_im]
    ring
  · intro x
    have key : ∀ w, (star (realVec x w) ⬝ᵥ mat h w *ᵥ realVec x w).re =
        ∑ s, ∑ t, x s * ((star (embO w (RingOfIntegers.basis L s.2)) * mat h w s.1 t.1 *
          embO w (RingOfIntegers.basis L t.2)).re * x t) := by
      intro w
      have hr : ∀ s t, x s * ((star (embO w (RingOfIntegers.basis L s.2)) * mat h w s.1 t.1 *
          embO w (RingOfIntegers.basis L t.2)).re * x t) =
          ((x s : ℂ) * (star (embO w (RingOfIntegers.basis L s.2)) * mat h w s.1 t.1 *
          embO w (RingOfIntegers.basis L t.2)) * (x t : ℂ)).re := by
        intro s t
        rw [Complex.re_mul_ofReal, Complex.re_ofReal_mul]
        ring
      simp only [hr, ← Complex.re_sum]
      congr 1
      simp only [realVec, dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', Complex.star_def,
        Complex.conj_ofReal, Finset.mul_sum, Finset.sum_mul, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a _ => ?_
      refine Eq.trans ?_ Finset.sum_comm.symm
      refine Finset.sum_congr rfl fun b _ => ?_
      refine Eq.trans ?_ Finset.sum_comm.symm
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      ring
    simp only [qR, key]
    simp only [dotProduct, mulVec, gram, of_apply, Finset.mul_sum, Finset.sum_mul]
    calc ∑ s, ∑ t, ∑ w, x s * ((star (embO w (RingOfIntegers.basis L s.2)) * mat h w s.1 t.1 *
          embO w (RingOfIntegers.basis L t.2)).re * x t)
        = ∑ s, ∑ w, ∑ t, x s * ((star (embO w (RingOfIntegers.basis L s.2)) * mat h w s.1 t.1 *
          embO w (RingOfIntegers.basis L t.2)).re * x t) :=
          Finset.sum_congr rfl fun s _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  · intro c
    funext w a
    simp [realVec, toR, intVec, map_sum, zsmul_eq_mul]
  · let E : (Fin N × BI L → ℤ) ≃ Lat L N :=
      (Equiv.curry _ _ _).trans
        (Equiv.piCongrRight fun _ => (RingOfIntegers.basis L).equivFun.symm.toEquiv)
    have hE : (intVec : (Fin N × BI L → ℤ) → Lat L N) = E := by
      funext c a
      simp [E, intVec, Module.Basis.equivFun_symm_apply, Equiv.curry]
    rw [hE]
    exact E.bijective
