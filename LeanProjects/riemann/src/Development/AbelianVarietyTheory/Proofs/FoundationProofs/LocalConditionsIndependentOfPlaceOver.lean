import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

open Pointwise

namespace GlobalTheory.Ord2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem cocycle_mulVec {W : R2 Ω l} {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ Z1 (Loc.colRep W)) (g h : G ℚ Ω) :
    z (g * h) = z g + mat W g *ᵥ z h :=
  hz.2 g h

theorem mat_mul' (W : R2 Ω l) (g h : G ℚ Ω) : mat W (g * h) = mat W g * mat W h := by
  simp [mat, map_mul, Units.val_mul]

theorem mat_one' (W : R2 Ω l) : mat W 1 = 1 := by
  simp [mat]

theorem cob_conj {W : R2 Ω l} {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ Z1 (Loc.colRep W)) (γ t : G ℚ Ω)
    (x : Fin 2 → Qbar l) (ht : z t = mat W t *ᵥ x - x) :
    z (γ * t * γ⁻¹) = mat W (γ * t * γ⁻¹) *ᵥ (mat W γ *ᵥ x - z γ) - (mat W γ *ᵥ x - z γ) := by
  have h0 : z 1 = 0 := by
    have := cocycle_mulVec hz 1 1
    rw [mul_one, mat_one', Matrix.one_mulVec] at this
    simpa using this
  have h2 : z γ⁻¹ = -(mat W γ⁻¹ *ᵥ z γ) := by
    have := cocycle_mulVec hz γ⁻¹ γ
    rw [inv_mul_cancel, h0] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  have hinv : mat W γ⁻¹ * mat W γ = 1 := by rw [← mat_mul', inv_mul_cancel, mat_one']
  rw [cocycle_mulVec hz, cocycle_mulVec hz, ht, h2, mat_mul', mat_mul', mat_mul']
  simp only [Matrix.mulVec_sub, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_assoc, hinv, Matrix.mul_one]
  abel

theorem cob_of_conj_le {W : R2 Ω l} {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ Z1 (Loc.colRep W)) (γ : G ℚ Ω)
    (H H' : Subgroup (G ℚ Ω)) (hH : ∀ s ∈ H', γ⁻¹ * s * γ ∈ H)
    (h : ∃ x : Fin 2 → Qbar l, ∀ s ∈ H, z s = mat W s *ᵥ x - x) :
    ∃ x : Fin 2 → Qbar l, ∀ s ∈ H', z s = mat W s *ᵥ x - x := by
  obtain ⟨x, hx⟩ := h
  refine ⟨mat W γ *ᵥ x - z γ, fun s hs => ?_⟩
  have e : s = γ * (γ⁻¹ * s * γ) * γ⁻¹ := by group
  rw [e]
  exact cob_conj hz γ _ x (hx _ (hH s hs))

theorem place_indep : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l)
    (z : G ℚ Ω → Fin 2 → Qbar l), z ∈ Z1 (Loc.colRep W) → ∀ (w : Pl) (B B' : ValuationSubring Ω),
    IsPlaceOver B w → IsPlaceOver B' w →
    ((∃ x : Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B, z s = mat W s *ᵥ x - x) →
      ∃ x : Fin 2 → Qbar l, ∀ s ∈ Ine (F := ℚ) B', z s = mat W s *ᵥ x - x) ∧ (Triv W B z → Triv W B' z) := by
  intro l _ Ω _ _ _ W z hz w B B' hB hB'
  obtain ⟨γ, hγ⟩ := exists_smul_eq_of_isPlaceOver hB hB'
  refine ⟨cob_of_conj_le hz γ _ _ (fun s hs => ?_), cob_of_conj_le hz γ _ _ (fun s hs => ?_)⟩
  · have := conj_mem_Ine_smul (F := ℚ) (A := B') (γ := γ⁻¹) (σ := s) hs
    rw [inv_inv, ← hγ, inv_smul_smul] at this
    exact this
  · have hs' : s • B' = B' := hs
    show (γ⁻¹ * s * γ) • B = B
    rw [mul_smul, mul_smul, hγ, hs', ← hγ, inv_smul_smul]

end GlobalTheory.Ord2
