import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SchwartzBruhatMixedFamilies
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SobolevBoundedThetaFormMatrixCoeffSmooth
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsInfFamAndStdChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum NumberField
open GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ContDiff Topology

namespace GlobalTheory.HeisSmooth

open GlobalTheory.OrientedHeis GlobalTheory.FockCompare GlobalTheory.Unf.MatCoef

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} {S T : HSp D}

theorem differentiableAt_phase (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {M : ℝ →+ WO S T} (hM : Continuous M)
    (hMf : ∀ s, (M s).map (finPart D) = 0) (w : WO S T) :
    DifferentiableAt ℝ (fun s : ℝ => ψ (symplOH S T w (M s))) 0 := by
  have hlin : ∀ s : ℝ, piW θ T S (M s) = s • piW θ T S (M 1) := fun s => by
    have := map_real_smul ((piW θ T S).comp M) ((continuous_pi' h.inf T S).comp hM) s 1
    simpa using this
  have e : (fun s : ℝ => ψ (symplOH S T w (M s))) = fun s : ℝ =>
      Complex.exp (-(Real.pi * Complex.I) * ((s * omO S T (piW θ T S w) (piW θ T S (M 1)) : ℝ) : ℂ)) := by
    funext s
    rw [← h.iota_pi (hMf s), psi_symplOH h hψ, hlin, LinearMap.map_smul, smul_eq_mul]
  rw [e]
  exact ((((hasDerivAt_id (0 : ℝ)).mul_const (omO S T (piW θ T S w) (piW θ T S (M 1)))).ofReal_comp).const_mul
      (-(Real.pi * Complex.I))).cexp.differentiableAt

theorem hasDerivAt_line (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {M : ℝ →+ WO S T} (hM : Continuous M)
    (hMf : ∀ s, (M s).map (finPart D) = 0) {f : WO S T → ℂ} {w : WO S T} {c : ℂ}
    (hd : HasDerivAt (fun s : ℝ => heisO ψ S T (M s) f w) c 0) :
    HasDerivAt (fun s : ℝ => f (w + M s)) (c + -deriv (fun s : ℝ => ψ (symplOH S T w (M s))) 0 * f w) 0 := by
  have hp := (differentiableAt_phase h hψ hM hMf w).hasDerivAt
  have hne : ∀ s, ψ (symplOH S T w (M s)) ≠ 0 := fun s h0 => by
    have := AddChar.map_add_eq_mul ψ (symplOH S T w (M s)) (-(symplOH S T w (M s)))
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h0, zero_mul] at this
    exact one_ne_zero this
  have h0 : symplOH S T w (M 0) = 0 := by
    rw [map_zero]
    simp [symplOH, symplO, hO]
  have e : (fun s : ℝ => f (w + M s)) = fun s => heisO ψ S T (M s) f w / ψ (symplOH S T w (M s)) := by
    funext s
    rw [heisO, mul_div_cancel_left₀ _ (hne s)]
  rw [e]
  refine (hd.div hp (hne 0)).congr_deriv ?_
  have h1 : heisO ψ S T (M 0) f w = f w := by
    rw [heisO, h0, AddChar.map_zero_eq_one, one_mul, map_zero, add_zero]
  rw [h1, h0, AddChar.map_zero_eq_one]
  ring

theorem contDiff_of_heis_closed : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (V : Set (WO S T → ℂ)), (∀ f ∈ V, Continuous f) →
    (∀ f ∈ V, ∀ M : ℝ →+ WO S T, Continuous M → (∀ t, (M t).map (finPart D) = 0) →
      ∃ f' ∈ V, ∀ w, HasDerivAt (fun t : ℝ => heisO ψ S T (M t) f w) (f' w) 0) →
    ∀ f ∈ V, ∀ (k : ℕ) (L : (Fin k → ℝ) →+ WO S T), Continuous L → (∀ t, (L t).map (finPart D) = 0) →
      ∀ w, ContDiff ℝ ∞ fun t => f (w + L t) := by
  intro D ψ hψ S T V hc hd f hf k L hL hLf u
  obtain ⟨⟨θ, hθ⟩, -⟩ := GlobalTheory.Ker.exists_infFam_and_stdChar D
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  haveI : IsTopologicalAddGroup (Formalism.L2.Theta.AE D) := IsTopologicalRing.to_topologicalAddGroup
  haveI : IsTopologicalAddGroup (WO S T) := Pi.topologicalAddGroup
  haveI : ContinuousAdd (WO S T) := inferInstance
  let P : ((Fin k → ℝ) → ℂ) → Prop := fun F => ∃ f ∈ V, F = fun t => f (u + L t)
  refine contDiff_of_partials P ?_ ?_ _ ⟨f, hf, rfl⟩
  · rintro _ ⟨f, hf, rfl⟩
    exact (hc f hf).comp (continuous_const.add hL)
  · rintro _ ⟨f, hf, rfl⟩ i
    let E : ℝ →ₗ[ℝ] (Fin k → ℝ) := LinearMap.toSpanSingleton ℝ (Fin k → ℝ) (Pi.single i 1)
    let M : ℝ →+ WO S T := L.comp E.toAddMonoidHom
    have hM : Continuous M := hL.comp E.continuous_of_finiteDimensional
    have hMf : ∀ s, (M s).map (finPart D) = 0 := fun s => hLf _
    obtain ⟨f', hf', hD⟩ := hd f hf M hM hMf
    refine ⟨2, ![fun _ => 1, fun t => -deriv (fun s : ℝ => ψ (symplOH S T (u + L t) (M s))) 0],
      ![fun t => f' (u + L t), fun t => f (u + L t)], fun j => ?_, fun j => ?_, fun t => ?_⟩
    · fin_cases j
      · exact contDiff_const
      · exact contDiff_phase h hψ hL hM hMf u
    · fin_cases j
      · exact ⟨f', hf', rfl⟩
      · exact ⟨f, hf, rfl⟩
    · have e : (fun s : ℝ => f (u + L (t + s • Pi.single i 1))) = fun s => f ((u + L t) + M s) := by
        funext s
        have : E s = s • Pi.single i 1 := rfl
        rw [map_add, add_assoc, ← this]
        rfl
      rw [e]
      convert hasDerivAt_line h hψ hM hMf (hD (u + L t)) using 1
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_mul]

end GlobalTheory.HeisSmooth
