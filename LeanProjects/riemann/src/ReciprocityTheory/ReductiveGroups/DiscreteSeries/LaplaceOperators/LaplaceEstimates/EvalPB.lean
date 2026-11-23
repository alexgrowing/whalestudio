import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.EvalPA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.ListProdMemOfForall
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.EvalMD

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

namespace CapelliMinorRestriction

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem le_gen {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M) : V ≤ genSub E V :=
  le_sInf fun _ hT => hT.1

theorem gen_stable {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M) (a b : Fin n) {v : M}
    (hv : v ∈ genSub E V) : E a b v ∈ genSub E V :=
  Submodule.mem_sInf.mpr fun T hT => hT.2 a b v (Submodule.mem_sInf.mp hv T hT)

theorem gen_stable_frame {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (Q : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) {v : M} (hv : v ∈ genSub E V) :
    frameE Q E i j v ∈ genSub E V := by
  unfold frameE
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (gen_stable E V a b hv)

theorem isGlRep_reindex {n n' : ℕ} (E : Fin n' → Fin n' → Module.End ℂ M) (e : Fin n → Fin n')
    (he : Function.Injective e) (hE : IsGlRep E) : IsGlRep (fun a b => E (e a) (e b)) := by
  intro a b c d
  have := hE (e a) (e b) (e c) (e d)
  simp only [he.eq_iff] at this
  exact this

theorem sum_beta_nnPlus (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ M) (hE : IsGlRep E)
    (Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hQ : Q⁻¹ * Q = 1) (c₀ : ℂ) (j₀ : Fin (m + 1)) (om : ℂ) (v : M) :
    ∑ d, (c₀ * Q (Fin.last m) d) • Capelli.nnPlus E (Q⁻¹ *ᵥ Pi.single j₀ 1) om v d =
      (c₀ * (-1 : ℂ) ^ (m + (j₀ : ℕ))) •
        Capelli.cminor (frameE Q E) (Fin.last m).succAbove j₀.succAbove (om - 1) v := by
  have h := congrArg (fun f => f v)
    (capelliCov (Module.End ℂ M) m E Q⁻¹ Q (om - 1) hE hQ (Fin.last m) j₀)
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, Fin.val_last] at h
  have hF : (fun a b => ∑ c', ∑ d', (Q⁻¹ c' a * Q b d') • E c' d') = frameE Q E := rfl
  rw [hF] at h
  rw [mul_smul, h, Finset.smul_sum]
  unfold Capelli.nnPlus
  simp_rw [Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  congr 1
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  ring

end CapelliMinorRestriction

end ReciprocityTheory.ChartRestriction.DS.Lap

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

namespace CapelliMinorRestriction

variable {k r : ℕ}

theorem frameGl {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M] (Q : Matrix (Fin n) (Fin n) ℂ)
    (E : Fin n → Fin n → Module.End ℂ M) (hQ : Q * Q⁻¹ = 1) (hQ' : Q⁻¹ * Q = 1) (hE : IsGlRep E) :
    IsGlRep (frameE Q E) :=
  frameE_glRep Q hQ E hE

theorem per_add {Vp : Type*} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]
    (P : Mat k r) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (ψ : Mat k r → ℂ)
    (π : Mat k r → (Vp →L[ℂ] Vp)) (F₁ F₂ : Mat k r → ℂ) (ξ : Vp) (x : Mat k r)
    (h₁ : Integrable (perI P ψ π F₁ ξ x) (μW.prod μN)) (h₂ : Integrable (perI P ψ π F₂ ξ x) (μW.prod μN)) :
    per P μW μN ψ π (fun G => F₁ G + F₂ G) ξ x = per P μW μN ψ π F₁ ξ x + per P μW μN ψ π F₂ ξ x := by
  rw [per_eq, per_eq, per_eq, ← integral_add h₁ h₂]
  congr 1
  funext p
  simp [perI, add_smul]

theorem hpk_mulVec (i : Fin (2 * r + k + 1)) (u : Fin (2 * r + k + 1) → ℂ) :
    (Formalism.QuantumDeterminants.Hpk k r *ᵥ u) i = (if i.val = r + k then -1 else 1) * u (ExponentialSlopeDerivatives.sg k r i) := by
  simp only [Matrix.mulVec, dotProduct, ExponentialSlopeDerivatives.hpk_apply, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem beta_formula (ε : Fin (2 * r + k + 1) → Bool) (P : Mat k r)
    (hP : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r) (z : Fin (2 * r + k + 1) → ℂ)
    (hTz : 0 < Formalism.QuantumDeterminants.Tz k r z) (g g₀ Q : Mat k r) (hg₀ : Formalism.MainNotions.S.IsFrameW k r z g₀)
    (hgQ : g * P⁻¹ = g₀ * Q) :
    ∃ c₀ : ℂ, c₀ ≠ 0 ∧ ∀ d, cJ ε (xJ P z) (Pi.single d 1) (P * g * P⁻¹) = c₀ * Q (Fin.last (2 * r + k)) d := by
  have hg₀U : g₀ᴴ * Formalism.QuantumDeterminants.Hpk k r * g₀ = Formalism.QuantumDeterminants.Hpk k r := hg₀.1
  have key : ∀ x' : Fin (2 * r + k + 1) → ℂ, g₀ *ᵥ x' = xOne k r z → ∀ d,
      cJ ε (xJ P z) (Pi.single d 1) (P * g * P⁻¹) =
        star x' ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ (Q *ᵥ Pi.single d 1)) := by
    intro x' hx' d
    unfold xJ
    rw [cJ_transport ε P hP, Matrix.mulVec_mulVec (Pi.single d 1) g P⁻¹, hgQ,
      ← Matrix.mulVec_mulVec (Pi.single d 1) g₀ Q, ← hx']
    exact ExponentialSlopeDerivatives.herm_UH hg₀U x' _
  have hQe : ∀ d, (Q *ᵥ Pi.single d (1 : ℂ)) (Fin.last (2 * r + k)) = Q (Fin.last (2 * r + k)) d := by
    intro d; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  by_cases hr : r = 0
  · refine ⟨-((Real.sqrt (Formalism.QuantumDeterminants.Tz k r z) : ℝ) : ℂ), ?_, fun d => ?_⟩
    · rw [neg_ne_zero, Complex.ofReal_ne_zero]
      exact (Real.sqrt_pos.mpr hTz).ne'
    · have hx : g₀ *ᵥ (((Real.sqrt (Formalism.QuantumDeterminants.Tz k r z) : ℝ) : ℂ) •
          Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI k r (Fin.last k))) = xOne k r z := by
        rw [hg₀.2.2]; unfold xOne; rw [if_pos hr]
      rw [key _ hx]
      have hw : Formalism.QuantumDeterminants.wI k r (Fin.last k) = Fin.last (2 * r + k) := Fin.ext (by simp [Formalism.QuantumDeterminants.wI]; omega)
      have hsg : ExponentialSlopeDerivatives.sg k r (Fin.last (2 * r + k)) = Fin.last (2 * r + k) := by
        apply Fin.ext; rw [ExponentialSlopeDerivatives.sg_val]; split_ifs <;> simp <;> omega
      have hst : star (((Real.sqrt (Formalism.QuantumDeterminants.Tz k r z) : ℝ) : ℂ) • Formalism.QuantumDeterminants.bvec (Fin.last (2 * r + k))) =
          ((Real.sqrt (Formalism.QuantumDeterminants.Tz k r z) : ℝ) : ℂ) • Formalism.QuantumDeterminants.bvec (Fin.last (2 * r + k)) := by
        funext i; by_cases hi : i = Fin.last (2 * r + k) <;> simp [Formalism.QuantumDeterminants.bvec, hi]
      rw [hw, hst, smul_dotProduct, Formalism.QuantumDeterminants.bvec, single_dotProduct, one_mul, hpk_mulVec, hsg,
        if_pos (by simp; omega), hQe, smul_eq_mul]
      ring
  · refine ⟨1, one_ne_zero, fun d => ?_⟩
    have hx : g₀ *ᵥ Pi.single (⟨0, by omega⟩ : Fin (2 * r + k + 1)) 1 = xOne k r z := by
      have := (hg₀.2.1 ⟨0, by omega⟩).1
      unfold xOne
      rw [if_neg hr]
      exact this
    have hsg : ExponentialSlopeDerivatives.sg k r ⟨0, by omega⟩ = Fin.last (2 * r + k) := by
      apply Fin.ext; rw [ExponentialSlopeDerivatives.sg_val]; simp only [Fin.val_last]; split_ifs <;> omega
    have hst : star (Pi.single (⟨0, by omega⟩ : Fin (2 * r + k + 1)) (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) =
        (Pi.single (⟨0, by omega⟩ : Fin (2 * r + k + 1)) (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) := by
      funext i; simp [Pi.single_apply]
    rw [key _ hx, hst, single_dotProduct, one_mul, hpk_mulVec, hsg, if_neg (by simp; omega), hQe]

end CapelliMinorRestriction

end ReciprocityTheory.ChartRestriction.DS.Lap
