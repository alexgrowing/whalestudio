import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrthonormalPlaceBasis
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompletedTensorDiscreteSeriesIrreducibleFormalDe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsClosedEmbeddingEntriesInf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothAverageEqOfMemLowKSub
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDerivAtCompletedTensorOrbitSmoothAverage

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.StepAverage

theorem exists_smooth_average_of_isKTypeOf : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → ∀ P : ℕ, ∀ u ∈ VP B P, ∃ F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ u = ∫ g, F (fun v i j => uMat (g v) i j) • B.σs g (B.tens B.w) ∂(muInf B.I) := by
  intro B d hD hK P u hu
  have hσ : IsURep B.σs := (tensorRep B d hD).1
  have hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v) := fun v => by
    obtain ⟨_, hds, _, _⟩ := hD v
    obtain ⟨_, _, h, _⟩ := hds
    exact h
  have hw : ∀ v, B.w v ∈ Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v) ∧ B.w v ≠ 0 := fun v => by
    obtain ⟨_, _, ⟨h1, h2⟩, _⟩ := hD v
    refine ⟨h2, fun h0 => ?_⟩
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1

  let A : Set B.Hs := {y | ∃ F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧
    HasCompactSupport F ∧ y = ∫ g, F (fun v i j => uMat (g v) i j) • B.σs g (B.tens B.w) ∂(muInf B.I)}
  have hint : ∀ F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F → HasCompactSupport F →
      Integrable (fun g : B.I.Ginf => F (fun v i j => uMat (g v) i j) • B.σs g (B.tens B.w)) (muInf B.I) :=
    fun F hF hc => integrable_inf B hσ (B.tens B.w) hF.continuous hc
  have hzero : (0 : B.Hs) ∈ A := ⟨0, contDiff_const, HasCompactSupport.zero, by simp⟩
  have hadd : ∀ x y, x ∈ A → y ∈ A → x + y ∈ A := by
    rintro x y ⟨F, hF, hFc, rfl⟩ ⟨G, hG, hGc, rfl⟩
    refine ⟨F + G, hF.add hG, hFc.add hGc, ?_⟩
    rw [← integral_add (hint F hF hFc) (hint G hG hGc)]
    congr 1
    funext g
    simp [add_smul]
  have hsmul : ∀ (c : ℂ) x, x ∈ A → c • x ∈ A := by
    rintro c x ⟨F, hF, hFc, rfl⟩
    refine ⟨fun z => c * F z, contDiff_const.mul hF, hFc.mul_left (f := fun _ => c), ?_⟩
    rw [← integral_smul]
    congr 1
    funext g
    rw [mul_smul]

  have htens : ∀ u' : ∀ v, B.H v, (∀ v, u' v ∈ Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v)) → B.tens u' ∈ A := by
    intro u' hu'
    have hloc := fun v => GlobalTheory.exists_smooth_average_eq_of_mem_lowKSub B.I.n (B.I.ε v) (B.H v) (B.σ v) (B.lam v)
      (B.w v) (hU v) (hK v) (hw v).1 (hw v).2 (u' v) (hu' v)
    choose F hF hFc hFe using hloc
    obtain ⟨G, hG, hGc, hGe⟩ := tens_average B hU hσ B.w F hF hFc
    refine ⟨G, hG, hGc, ?_⟩
    rw [← hGe]
    congr 1
    funext v
    exact hFe v

  have hword : ∀ (l : List (Σ v : InfinitePlace B.I.F, gLie (B.I.ε v))) (y : B.Hs), y ∈ A → wordAct B l y ∈ A := by
    intro l
    induction l with
    | nil => intro y hy; exact hy
    | cons X l ih =>
      intro y hy
      obtain ⟨F, hF, hFc, hFe⟩ := ih y hy
      obtain ⟨F', hF', hF'c, hd⟩ := GlobalTheory.AverageDeriv.hasDerivAt_orbit_average B F (atPlace B X.1 X.2) (B.tens B.w)
        hσ hF hFc
      refine ⟨F', hF', hF'c, ?_⟩
      show dAct B (atPlace B X.1 X.2) (wordAct B l y) = _
      rw [hFe]
      exact hd.deriv

  let S : Submodule ℂ B.Hs :=
    { carrier := A
      add_mem' := fun hx hy => hadd _ _ hx hy
      zero_mem' := hzero
      smul_mem' := fun c x hx => hsmul c x hx }
  have hle : VP B P ≤ S := by
    refine Submodule.span_le.mpr ?_
    rintro y ⟨l, u', -, hu', rfl⟩
    exact hword l _ (htens u' hu')
  exact hle hu

end GlobalTheory.StepAverage
