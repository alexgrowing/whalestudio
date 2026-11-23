import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.CuspRapid

theorem norm_sub_le_of_lieD_unipotent_segment (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (ψ : Sm E a) (g : GA E a) (n : Matrix (Fin a) (Fin a) (Cinf E)) (u : ℝ → GL (Fin a) (Cinf E)) (M : ℝ)
    (hn : n * n = 0) (hu : ∀ τ : ℝ, (u τ).val = 1 + τ • n)
    (hM : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖lieD (toL n) ψ.1 (g * infGL E a (u τ))‖ ≤ M) :
    ‖ψ.1 (g * infGL E a (u 1)) - ψ.1 g‖ ≤ M := by
  have h0 : u 0 = 1 := Units.ext (by rw [hu]; simp)
  have hadd : ∀ τ s : ℝ, u (τ + s) = u τ * u s := by
    intro τ s
    refine Units.ext ?_
    rw [Units.val_mul, hu, hu, hu]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hn, smul_zero, add_zero, add_smul]
    abel
  have hc : HasDerivAt (fun t => toL (u t).val) (toL n) 0 := by
    have e : (fun t : ℝ => toL (u t).val) = fun t : ℝ => oneL E a + t • toL n := by
      funext t; rw [hu]; rfl
    rw [e]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (toL n)).const_add (oneL E a)
  have hd : ∀ τ : ℝ, HasDerivAt (fun t => ψ.1 (g * infGL E a (u t)))
      (lieD (toL n) ψ.1 (g * infGL E a (u τ))) τ := by
    intro τ
    have h1 := hasDerivAt_curve ψ (g * infGL E a (u τ)) u (toL n) h0 hc
    have h2 : HasDerivAt (fun s => ψ.1 (g * infGL E a (u τ) * infGL E a (u s)))
        (lieD (toL n) ψ.1 (g * infGL E a (u τ))) (τ - τ) := by rwa [sub_self]
    have h3 := h2.comp_sub_const τ τ
    have e : (fun t => ψ.1 (g * infGL E a (u τ) * infGL E a (u (t - τ)))) =
        fun t => ψ.1 (g * infGL E a (u t)) := by
      funext t
      rw [mul_assoc, ← map_mul, ← hadd, add_sub_cancel]
    rwa [e] at h3
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := fun t => ψ.1 (g * infGL E a (u t)))
    (fun τ _ => (hd τ).hasDerivWithinAt) (fun τ hτ => hM τ (Set.Ico_subset_Icc_self hτ))
  simpa [h0] using h

end GlobalTheory.CuspRapid
