import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ResidueInjectivityAt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links

namespace GlobalTheory.Survey.SobolevContinuityLowGeneration

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sobCont_zero {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Lie : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Sobolev₂ Lie σ 0 :=
  ⟨[], 0, by simp, by simp⟩

theorem sobCont_smul {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Lie : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {ℓ : H →ₗ[ℂ] ℂ} (c : ℂ)
    (h : Sobolev₂ Lie σ ℓ) : Sobolev₂ Lie σ (c • ℓ) := by
  obtain ⟨S, C, h1, h2⟩ := h
  refine ⟨S, ‖c‖ * C, h1, fun w hw => ?_⟩
  rw [LinearMap.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h2 w hw) (norm_nonneg c)

theorem sobCont_add {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Lie : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {ℓ ℓ' : H →ₗ[ℂ] ℂ}
    (h : Sobolev₂ Lie σ ℓ) (h' : Sobolev₂ Lie σ ℓ') : Sobolev₂ Lie σ (ℓ + ℓ') := by
  obtain ⟨S, C, h1, h2⟩ := h
  obtain ⟨S', C', h1', h2'⟩ := h'
  refine ⟨S ++ S', max C C', fun l hl => (List.mem_append.1 hl).elim (h1 l) (h1' l), fun w hw => ?_⟩
  have p : ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), 0 ≤ (S.map fun l => ‖l.foldr (dRep σ) w‖).sum := by
    intro S
    refine List.sum_nonneg fun x hx => ?_
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
    exact norm_nonneg _
  rw [LinearMap.add_apply, List.map_append, List.sum_append, mul_add]
  refine (norm_add_le _ _).trans (add_le_add ((h2 w hw).trans ?_) ((h2' w hw).trans ?_))
  · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (p S)
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (p S')

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def LowGenerates (M : DSModel V S) (τ : D.what₂.Tau) : Prop :=
  ∀ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ →
    (∀ u ∈ lowT M τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w : M.sm τ, (w : M.H τ) = M.rep τ g u → ℓ w = 0) →
    ∀ w : M.sm τ, ℓ w = 0

open Classical in
theorem mult_equiv_cont {θ} {M : DSModel V S} {J χ} {U : MMap M} (hU : U ∈ Mult θ M J χ) :
    (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ),
      (w : M.H τ) = M.rep τ g (v τ) → U (Function.update v τ w) = rTr V (atTau θ V τ g) (U v)) ∧
    ∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
      ∀ w : M.sm τ, ℓ w = U (Function.update v τ w) x := by
  induction hU using Submodule.span_induction with
  | mem T hT => exact ⟨hT.equiv, hT.cont⟩
  | zero => exact ⟨fun _ _ _ _ _ _ => rfl, fun τ v x => ⟨0, sobCont_zero _ _, fun _ => rfl⟩⟩
  | add T T' _ _ h h' =>
    refine ⟨fun τ g hg v w hw => ?_, fun τ v x => ?_⟩
    · rw [MultilinearMap.add_apply, h.1 τ g hg v w hw, h'.1 τ g hg v w hw]; rfl
    · obtain ⟨ℓ, a, b⟩ := h.2 τ v x
      obtain ⟨ℓ', a', b'⟩ := h'.2 τ v x
      exact ⟨ℓ + ℓ', sobCont_add a a', fun w => by rw [LinearMap.add_apply, b, b']; rfl⟩
  | smul c T _ h =>
    refine ⟨fun τ g hg v w hw => ?_, fun τ v x => ?_⟩
    · rw [MultilinearMap.smul_apply, h.1 τ g hg v w hw]; rfl
    · obtain ⟨ℓ, a, b⟩ := h.2 τ v x
      exact ⟨c • ℓ, sobCont_smul c a, fun w => by rw [LinearMap.smul_apply, b]; rfl⟩

theorem eq_zero_of_lowGenerates {θ} {M : DSModel V S} (hM : ∀ τ, LowGenerates M τ) {J χ} {U : MMap M}
    (hU : U ∈ Mult θ M J χ) (h0 : ∀ v : ∀ ρ, lowT M ρ, U (fun ρ => (v ρ : M.sm ρ)) = 0) : U = 0 := by
  classical
  obtain ⟨he, hc⟩ := mult_equiv_cont hU
  have key : ∀ s : Finset D.what₂.Tau, ∀ v : M.Vec, (∀ ρ, ρ ∉ s → v ρ ∈ lowT M ρ) → U v = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro v hv; exact h0 fun ρ => ⟨v ρ, hv ρ (by simp)⟩
    | insert τ s _ ih =>
      intro v hv
      funext x
      obtain ⟨ℓ, hℓ, e⟩ := hc τ v x
      have := hM τ ℓ hℓ (fun u hu g hg w hw => ?_) (v τ)
      · rw [e] at this
        simpa using this
      · have h1 := he τ g hg (Function.update v τ u) w (by simpa using hw)
        have h2 : U (Function.update v τ u) = 0 := by
          refine ih _ fun ρ hρ => ?_
          by_cases hh : ρ = τ
          · subst hh; simpa using hu
          · rw [Function.update_of_ne hh]; exact hv ρ (by simp [hh, hρ])
        rw [e]
        simp only [Function.update_idem] at h1
        have h3 := congrFun h1 x
        simp only [rTr] at h3
        rw [h3, h2]; rfl
  exact MultilinearMap.ext fun v => key Finset.univ v (by simp)

end GlobalTheory.Survey.SobolevContinuityLowGeneration

end
