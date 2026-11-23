import Formalism.HermitianCurvature.HermitianCurvatureProofs.ResidueSquareIntegrablePositiveRank

open MeasureTheory
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerD

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC

section ShiftJ

variable {r : ℕ}

def shIdxJ (i j : Fin (r + 1)) (jl : Fin (r - i + 1)) (hjl : jl.val + i.val = j.val) :
    {m : Fin (r - i) // jl.val ≤ m.val} ≃ {p : Fin r // j.val ≤ p.val} where
  toFun m := ⟨⟨m.1.val + i.val, by have := m.1.isLt; have := i.isLt; omega⟩, by
    have := m.2; show j.val ≤ m.1.val + i.val; omega⟩
  invFun p := ⟨⟨p.1.val - i.val, by have := p.1.isLt; have := p.2; omega⟩, by
    have := p.2; show jl.val ≤ p.1.val - i.val; omega⟩
  left_inv m := by
    apply Subtype.ext; apply Fin.ext
    show m.1.val + i.val - i.val = m.1.val
    omega
  right_inv p := by
    apply Subtype.ext; apply Fin.ext
    show p.1.val - i.val + i.val = p.1.val
    have := p.2; omega

def shEqJ (i j : Fin (r + 1)) (jl : Fin (r - i + 1)) (hjl : jl.val + i.val = j.val) : Cf (r - i) (jl) ≃ᵐ Cf r j :=
  MeasurableEquiv.piCongrLeft (fun _ => ℂ) (shIdxJ i j jl hjl)

theorem shEqJ_mp (i j : Fin (r + 1)) (jl : Fin (r - i + 1)) (hjl : jl.val + i.val = j.val) : MeasurePreserving (shEqJ i j jl hjl) volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ => ℂ) (shIdxJ i j jl hjl)

theorem shEqJ_apply (i j : Fin (r + 1)) (jl : Fin (r - i + 1)) (hjl : jl.val + i.val = j.val) (c' : Cf (r - i) (jl))
    (p : {p : Fin r // j.val ≤ p.val}) : shEqJ i j jl hjl c' p = c' ((shIdxJ i j jl hjl).symm p) := by
  unfold shEqJ
  rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rfl

def shiftV (i : Fin (r + 1)) (c' : Fin r → ℂ) : Fin (r - i) → ℂ :=
  fun m => c' ⟨m.val + i.val, by have := m.isLt; have := i.isLt; omega⟩

theorem glue_shEqJ (i j : Fin (r + 1)) (jl : Fin (r - i + 1)) (hjl : jl.val + i.val = j.val) (c c' : Fin r → ℂ)
    (hc : ∀ p : Fin r, p.val < i.val → c' p = c p) (c'' : Cf (r - i) (jl)) :
    glue j c' (shEqJ i j jl hjl c'') =
      glue i c (Formalism.FourierDecayAlt.P.PTie.shiftCf i (glue (jl) (shiftV i c') c'')) := by
  funext p
  by_cases h1 : j.val ≤ p.val
  · have h2 : i.val ≤ p.val := by omega
    have h3 : (jl).val ≤ p.val - i.val := by omega
    simp only [glue, dif_pos h1, dif_pos h2, Formalism.FourierDecayAlt.P.PTie.shiftCf, dif_pos h3, shEqJ_apply]
    rfl
  · by_cases h2 : i.val ≤ p.val
    · have h3 : ¬ (jl).val ≤ p.val - i.val := by omega
      simp only [glue, dif_neg h1, dif_pos h2, Formalism.FourierDecayAlt.P.PTie.shiftCf, dif_neg h3, shiftV]
      congr 1
      apply Fin.ext
      show p.val = p.val - i.val + i.val
      omega
    · simp only [glue, dif_neg h1, dif_neg h2]
      exact hc p (by omega)

theorem wtI_shEqJ (i j : Fin (r + 1)) (jl : Fin (r - i + 1)) (hjl : jl.val + i.val = j.val) (c'' : Cf (r - i) (jl)) :
    wtI j (shEqJ i j jl hjl c'') = wtI (jl) c'' := by
  unfold wtI
  congr 1
  simp_rw [shEqJ_apply]
  exact Fintype.prod_equiv (shIdxJ i j jl hjl).symm _ _ fun l => rfl

end ShiftJ

section Tr

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem integrand_tr (μ : Measure (Mt k r)) (i j : Fin (r + 1)) (jl : Fin (r - i + 1)) (hjl : jl.val + i.val = j.val) (c c' : Fin r → ℂ)
    (hc : ∀ p : Fin r, p.val < i.val → c' p = c p) {zi zi' : Fin (2 * (r - i) + k + 1) → ℂ}
    {πi : Mx k (r - i) → (Wp →L[ℂ] Wp)} {πi' : Mx k (r - i) → (Wq →L[ℂ] Wq)} (μi : Measure (Mt k (r - i)))
    (T : RadSp k r z z' π π' →ₗ[ℂ] RadSp k (r - i) zi zi' πi πi') (κ : ℝ) (hκ : 0 < κ)
    (hT : ∀ Φ Ψ c'', pairAt μi (T Φ) (T Ψ) c'' = (κ : ℂ) * pairAt μ Φ Ψ (glue i c (Formalism.FourierDecayAlt.P.PTie.shiftCf i c'')))
    (u v : Ix S → RadSp k r z z' π π') (c'' : Cf (r - i) (jl)) :
    wtI j (shEqJ i j jl hjl c'') * ∑ a, pairAt μ (u a) (v a) (glue j c' (shEqJ i j jl hjl c'')) =
      (κ : ℂ)⁻¹ * (wtI (jl) c'' *
        ∑ a, pairAt μi (T (u a)) (T (v a)) (glue (jl) (shiftV i c') c'')) := by
  have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  rw [wtI_shEqJ, glue_shEqJ i j jl hjl c c' hc]
  simp_rw [hT]
  rw [← Finset.mul_sum]
  field_simp

theorem form_tr (μ : Measure (Mt k r)) (i j : Fin (r + 1)) (jl : Fin (r - i + 1)) (hjl : jl.val + i.val = j.val) (c c' : Fin r → ℂ)
    (hc : ∀ p : Fin r, p.val < i.val → c' p = c p) {zi zi' : Fin (2 * (r - i) + k + 1) → ℂ}
    {πi : Mx k (r - i) → (Wp →L[ℂ] Wp)} {πi' : Mx k (r - i) → (Wq →L[ℂ] Wq)} (μi : Measure (Mt k (r - i)))
    (T : RadSp k r z z' π π' →ₗ[ℂ] RadSp k (r - i) zi zi' πi πi') (κ : ℝ) (hκ : 0 < κ)
    (hT : ∀ Φ Ψ c'', pairAt μi (T Φ) (T Ψ) c'' = (κ : ℂ) * pairAt μ Φ Ψ (glue i c (Formalism.FourierDecayAlt.P.PTie.shiftCf i c'')))
    (u v : Ix S → RadSp k r z z' π π') :
    form μ j u v c' = (κ : ℂ)⁻¹ * form μi (jl) (fun a => T (u a)) (fun a => T (v a)) (shiftV i c') := by
  unfold form
  rw [← (shEqJ_mp i j jl hjl).integral_comp', ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun c'' => ?_)
  exact integrand_tr μ i j jl hjl c c' hc μi T κ hκ hT u v c''

end Tr

theorem arel_star {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {S : Type}
    [Fintype S] [DecidableEq S] {T : V →ₗ[ℂ] V'} {M : SlopeTestRemainingChoices S (Pr V)} {M' : SlopeTestRemainingChoices S (Pr V')}
    (h : Formalism.FourierDecayAlt.P.PBH.ARel T M M') : Formalism.FourierDecayAlt.P.PBH.ARel T (star M) (star M') := fun a b => by
  rw [Matrix.star_apply, Matrix.star_apply]
  exact Formalism.FourierDecayAlt.P.PBH.rel_star (h b a)

end Formalism.FourierDecayAlt.P5.HerD
