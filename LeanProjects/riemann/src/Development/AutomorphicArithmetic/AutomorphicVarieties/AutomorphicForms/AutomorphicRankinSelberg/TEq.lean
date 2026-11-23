import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

open MeasureTheory Set UpperTheory.V.Af.Rs
open UpperHalfPlane hiding I
open scoped MatrixGroups

theorem UpperTheory.V.Af.Rs.tEq :
    UpperTheory.V.Af.Rs.RowBij → UpperTheory.V.Af.Rs.StripInt → UpperTheory.V.Af.Rs.Unfold → UpperTheory.V.Af.Rs.GcdSum → UpperTheory.V.Af.Rs.KerBd → UpperTheory.V.Af.Rs.Swap → UpperTheory.V.Af.Rs.LBd → UpperTheory.V.Af.Rs.TEq := by
  intro hRB hSI hUnf hGcd hKer hSw hLB L _ ψ F G hG hF hGn s hs
  have hs' : s ∈ Icc (1 : ℝ) 2 := ⟨hs.1.le, hs.2⟩
  obtain ⟨hkc, hk0, hkz, hkrow, hkn, -⟩ := hKer s hs'
  obtain ⟨hint, hsum⟩ := hSw L G hGn s hs
  have hrow : ∀ x : Cop, ∃ γ : SL(2, ℤ), row γ = (x : Fin 2 → ℤ) := fun x =>
    ((hRB.2 UpperHalfPlane.I x).exists).imp fun γ h => h.1
  have hone : ∀ (γ : SL(2, ℤ)) (z : ℍ), G (cls L (row γ)) z = F (γ • z) := by
    intro γ z
    have := hG 1 γ z
    simpa using this
  have hGn' : ∀ (n : ℕ) (γ : SL(2, ℤ)) (z : ℍ),
      G (cls L ((n : ℤ) • row γ)) z = ψ n * G (cls L (row γ)) z := by
    intro n γ z
    rw [hG, hone]
  set a : (Fin 2 → ℤ) → ℂ := fun x => ∫ z in ModularGroup.fd, G (cls L x) z * (ker s x z : ℂ) with ha
  set c : ℕ → ℂ := fun n => ψ n / ((n : ℝ) ^ (2 * s) : ℝ) with hc
  have hs2 : (2 * s) ≠ 0 := by have := hs.1; linarith
  have hgcd := hGcd a c hsum.summable (hLB L ψ s hs.1.le).1
    (by simp [ha, hkz])
    (by simp [hc, Real.zero_rpow hs2])
    (by
      intro n x
      obtain ⟨γ, hγ⟩ := hrow x
      simp only [ha, hc]
      rw [← hγ, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [hkn]
      rw [hGn', Complex.ofReal_div]
      ring)
  have hunf := hUnf (fun z => F z * ((z.im ^ s : ℝ) : ℂ)) (fun x z => G (cls L x) z * (ker s x z : ℂ))
    (by
      have hc1 : Continuous (fun z : ℍ => z.im ^ s) :=
        UpperHalfPlane.continuous_im.rpow_const (fun _ => Or.inr (by linarith [hs.1]))
      exact hF.1.mul (Complex.continuous_ofReal.comp hc1))
    (hSI F hF s hs)
    (by intro γ z; rw [hkrow, hone])
    (fun x => hint x)
  rw [← hsum.tsum_eq, hgcd]
  congr 1
  exact hunf.tsum_eq
