import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems

noncomputable section

open scoped Matrix

namespace GlobalTheory.CommutingExistence

variable {k : Type} [Field k]

theorem trace_two (A : Matrix (Fin 2) (Fin 2) k) (h1 : A.det = 1) (h2 : (A - 1).det = 0) :
    A 0 0 + A 1 1 = 2 := by
  rw [Matrix.det_fin_two] at h1 h2
  simp at h2
  linear_combination h1 - h2

theorem mul_nil (A B : Matrix (Fin 2) (Fin 2) k) (hA : A.det = 1) (hB : B.det = 1)
    (hA' : (A - 1).det = 0) (hB' : (B - 1).det = 0) (hAB : (A * B - 1).det = 0) :
    (A - 1) * (B - 1) = 0 := by
  have tA := trace_two A hA hA'
  have tB := trace_two B hB hB'
  have tAB := trace_two (A * B) (by rw [Matrix.det_mul, hA, hB, mul_one]) hAB
  rw [Matrix.det_fin_two] at hA hB
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at tAB
  obtain ⟨x, hx⟩ : ∃ x, A 0 0 = 1 + x := ⟨A 0 0 - 1, by ring⟩
  obtain ⟨a, ha⟩ : ∃ a, B 0 0 = 1 + a := ⟨B 0 0 - 1, by ring⟩
  have hx' : A 1 1 = 1 - x := by linear_combination tA - hx
  have ha' : B 1 1 = 1 - a := by linear_combination tB - ha
  rw [hx, hx'] at hA tAB
  rw [ha, ha'] at hB tAB
  have e1 : x ^ 2 + A 0 1 * A 1 0 = 0 := by linear_combination -hA
  have e2 : a ^ 2 + B 0 1 * B 1 0 = 0 := by linear_combination -hB
  have e3 : 2 * x * a + A 0 1 * B 1 0 + A 1 0 * B 0 1 = 0 := by linear_combination tAB
  have f00 : x * a + A 0 1 * B 1 0 = 0 := by
    apply pow_eq_zero_iff (two_ne_zero) |>.mp
    linear_combination a ^ 2 * e1 - A 0 1 * A 1 0 * e2 + A 0 1 * B 1 0 * e3
  have f01 : x * B 0 1 - A 0 1 * a = 0 := by
    apply pow_eq_zero_iff (two_ne_zero) |>.mp
    linear_combination B 0 1 ^ 2 * e1 + A 0 1 ^ 2 * e2 - A 0 1 * B 0 1 * e3
  have f10 : A 1 0 * a - x * B 1 0 = 0 := by
    apply pow_eq_zero_iff (two_ne_zero) |>.mp
    linear_combination B 1 0 ^ 2 * e1 + A 1 0 ^ 2 * e2 - A 1 0 * B 1 0 * e3
  have f11 : A 1 0 * B 0 1 + x * a = 0 := by
    linear_combination e3 - f00
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hx, hx', ha, ha']
  · linear_combination f00
  · linear_combination f01
  · linear_combination f10
  · linear_combination f11

theorem exists_comm [IsAlgClosed k] {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin 2) k) (H : Subgroup Γ)
    (hdet : ∀ s ∈ H, (ρ s : Matrix (Fin 2) (Fin 2) k).det = 1)
    (hirr : ∀ V : Submodule k (Fin 2 → k),
      (∀ g ∈ H, ∀ v ∈ V, (ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ v ∈ V) → V = ⊥ ∨ V = ⊤) :
    ∃ φ ∈ ⁅H, H⁆, ((ρ φ : Matrix (Fin 2) (Fin 2) k) - 1).det ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hle : ⁅H, H⁆ ≤ H := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
  have hconj : ∀ g ∈ H, ∀ φ ∈ ⁅H, H⁆, g⁻¹ * φ * g ∈ ⁅H, H⁆ := by
    intro g hg φ hφ
    have := Subgroup.commutator_mem_commutator (H.inv_mem hg) (hle hφ)
    have h2 := Subgroup.mul_mem _ this hφ
    convert h2 using 1
    rw [commutatorElement_def]
    group
  let F : Submodule k (Fin 2 → k) :=
    { carrier := {v | ∀ φ ∈ ⁅H, H⁆, (ρ φ : Matrix (Fin 2) (Fin 2) k) *ᵥ v = v}
      add_mem' := by
        intro a b ha hb φ hφ
        rw [Matrix.mulVec_add, ha φ hφ, hb φ hφ]
      zero_mem' := by
        intro φ _
        simp
      smul_mem' := by
        intro c a ha φ hφ
        rw [Matrix.mulVec_smul, ha φ hφ] }
  have hF : ∀ v, v ∈ F ↔ ∀ φ ∈ ⁅H, H⁆, (ρ φ : Matrix (Fin 2) (Fin 2) k) *ᵥ v = v := fun _ => Iff.rfl
  have hFinv : ∀ g ∈ H, ∀ v ∈ F, (ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ v ∈ F := by
    intro g hg v hv
    rw [hF] at hv ⊢
    intro φ hφ
    have h1 := hv _ (hconj g hg φ hφ)
    have h2 : φ * g = g * (g⁻¹ * φ * g) := by group
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, h2, map_mul, Units.val_mul,
      ← Matrix.mulVec_mulVec, h1]
  have hFtop : ∀ v, v ∈ F := by
    rcases hirr F hFinv with h | h
    · intro w
      rw [hF]
      intro ψ hψ
      have : ((ρ ψ : Matrix (Fin 2) (Fin 2) k) - 1) *ᵥ w ∈ F := by
        rw [hF]
        intro φ hφ
        have h0 := mul_nil (ρ φ : Matrix (Fin 2) (Fin 2) k) (ρ ψ : Matrix (Fin 2) (Fin 2) k)
          (hdet _ (hle hφ)) (hdet _ (hle hψ)) (hcon _ hφ) (hcon _ hψ)
          (by rw [← Units.val_mul, ← map_mul]; exact hcon _ (Subgroup.mul_mem _ hφ hψ))
        rw [Matrix.mulVec_mulVec]
        congr 1
        rw [sub_mul, one_mul, sub_eq_zero] at h0
        exact h0
      rw [h, Submodule.mem_bot, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
      exact this
    · intro w
      rw [h]
      trivial
  have hcomm : ∀ g ∈ H, ∀ g' ∈ H, ∀ v, (ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ ((ρ g' : Matrix (Fin 2) (Fin 2) k) *ᵥ v) =
      (ρ g' : Matrix (Fin 2) (Fin 2) k) *ᵥ ((ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ v) := by
    intro g hg g' hg' v
    have h1 := (hF _).1 (hFtop ((ρ g' : Matrix (Fin 2) (Fin 2) k) *ᵥ ((ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ v))) _
      (Subgroup.commutator_mem_commutator hg hg')
    rw [← h1]
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul]
    congr 3
    rw [commutatorElement_def]
    group
  have hscal : ∀ g ∈ H, ∃ c : k, ∀ v, (ρ g : Matrix (Fin 2) (Fin 2) k) *ᵥ v = c • v := by
    intro g hg
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' (ρ g : Matrix (Fin 2) (Fin 2) k))
    refine ⟨c, ?_⟩
    rcases hirr (Module.End.eigenspace (Matrix.toLin' (ρ g : Matrix (Fin 2) (Fin 2) k)) c) (by
      intro g' hg' v hv
      rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv ⊢
      rw [hcomm g hg g' hg', hv, Matrix.mulVec_smul]) with h | h
    · exact absurd h (Module.End.hasEigenvalue_iff.1 hc)
    · intro v
      have : v ∈ Module.End.eigenspace (Matrix.toLin' (ρ g : Matrix (Fin 2) (Fin 2) k)) c := by
        rw [h]; trivial
      rwa [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at this
  rcases hirr (Submodule.span k {(![1, 0] : Fin 2 → k)}) (by
    intro g hg v hv
    obtain ⟨c, hc⟩ := hscal g hg
    rw [hc]
    exact Submodule.smul_mem _ _ hv) with h | h
  · rw [Submodule.span_singleton_eq_bot] at h
    have := congrFun h 0
    simp at this
  · have : (![0, 1] : Fin 2 → k) ∈ Submodule.span k {(![1, 0] : Fin 2 → k)} := by
      rw [h]; trivial
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 this
    have := congrFun hc 1
    simp at this

theorem main (l : ℕ) [Fact (Nat.Prime l)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ)
    (S : Finset GlobalTheory.Ord2.Pl) (A : ValuationSubring Ω) (W : GlobalTheory.Ord2.R2 Ω l) (h : GlobalTheory.Ord2.Nf e S A W) :
    ∃ φ ∈ ⁅GlobalTheory.Ord2.H0g W, GlobalTheory.Ord2.H0g W⁆,
      Matrix.det (GlobalTheory.Ord2.mat W φ - (1 : Matrix (Fin 2) (Fin 2) (Formalism.ConjugateSelfDual.Qbar l))) ≠ (0 : Formalism.ConjugateSelfDual.Qbar l) := by
  refine exists_comm W (GlobalTheory.Ord2.H0g W) ?_ ?_
  · intro s hs
    have h1 : GlobalTheory.Ord2.dt W s = 1 := hs.2
    have h2 := congrArg Units.val h1
    exact h2
  · intro V hV
    exact h.irr.2.2 V le_top (fun g v hv => hV g g.2 v hv)

end GlobalTheory.CommutingExistence

end
