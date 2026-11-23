import Mathlib

open MvPolynomial Filter Topology

theorem UpperTheory.ConvolutionTheory.FX.esymm_pow :
    ∀ (n f : ℕ) (i : Fin n), ∃ g : MvPolynomial (Fin n) ℂ, aeval (fun j : Fin n => esymm (Fin n) ℂ (j + 1)) g = aeval (fun r : Fin n => (X r : MvPolynomial (Fin n) ℂ) ^ f) (esymm (Fin n) ℂ (i + 1)) := by
  intro n f i
  have hs : (aeval (fun r : Fin n => (X r : MvPolynomial (Fin n) ℂ) ^ f)
      (esymm (Fin n) ℂ (i + 1))).IsSymmetric := by
    intro e
    have h : (rename e).comp (aeval (fun r : Fin n => (X r : MvPolynomial (Fin n) ℂ) ^ f))
        = (aeval (fun r : Fin n => (X r : MvPolynomial (Fin n) ℂ) ^ f)).comp
            (rename e : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ) := by
      apply MvPolynomial.algHom_ext
      intro r
      simp
    have h2 := DFunLike.congr_fun h (esymm (Fin n) ℂ (i + 1))
    simp only [AlgHom.comp_apply] at h2
    rw [h2, esymm_isSymmetric (Fin n) ℂ (i + 1) e]
  obtain ⟨g, hg⟩ := esymmAlgHom_surjective (σ := Fin n) ℂ (n := n) (by simp)
    ⟨_, (mem_symmetricSubalgebra _).2 hs⟩
  refine ⟨g, ?_⟩
  have := congrArg Subtype.val hg
  rw [esymmAlgHom_apply] at this
  exact this
