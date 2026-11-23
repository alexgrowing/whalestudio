import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBiThetaIffJoin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContDiffCompactAverageOfClosedPartialsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaAvgSmooth

open GlobalTheory.WeilVacMove

theorem key {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {lam : AF D.host.F →+ ℂ} (hl : Continuous lam)
    (hlam : ∀ a, sndA D.host.F a = 0 → ψ a = Complex.exp (lam a)) {n : ℕ} (L : (Fin n → ℝ) →+ WO S T)
    (hL : Continuous L) (hL0 : ∀ t, (L t).map (finPart D) = 0) (w : WO S T) (f : WO S T → ℂ)
    (hf : IsThetaFunO ψ S T f) (t : Fin n → ℝ) (i : Fin n) :
    fderiv ℝ (fun t => f (w + L t)) t (Pi.single i 1) =
      dLine ψ S T (L.comp (AddMonoidHom.single (fun _ : Fin n => ℝ) i)) f (w + L t) +
        -phase lam S T (L.comp (AddMonoidHom.single (fun _ : Fin n => ℝ) i) 1) (w + L t) * f (w + L t) := by
  set M := L.comp (AddMonoidHom.single (fun _ : Fin n => ℝ) i) with hMdef
  have hs : Continuous (AddMonoidHom.single (fun _ : Fin n => ℝ) i) := by
    refine continuous_pi fun j => ?_
    by_cases h : j = i
    · subst h; simp; exact continuous_id'
    · simpa [h] using continuous_const
  have hM : Continuous M := hL.comp hs
  have hM0 : ∀ s, (M s).map (finPart D) = 0 := fun s => hL0 _
  set x := w + L t with hx
  set c := phase lam S T (M 1) x with hc
  obtain ⟨hd, -⟩ := hasDerivAt_zero_and_isTheta hψ hM hM0 hf
  have hexp : HasDerivAt (fun s : ℝ => Complex.exp (-((s : ℂ) * c))) (-c) 0 := by
    have := ((HasDerivAt.ofReal_comp (hasDerivAt_id (0 : ℝ))).mul_const c).neg.cexp
    simpa using this
  have h1 := hexp.mul (hd x)
  have hsm : ∀ s : ℝ, s • (Pi.single i (1 : ℝ) : Fin n → ℝ) = Pi.single i s := by
    intro s
    ext j
    by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  have e1 : ∀ s : ℝ, Complex.exp (-((s : ℂ) * c)) * heisO ψ S T (M s) f x =
      f (w + L (t + s • Pi.single i 1)) := by
    intro s
    rw [heisO, psi_sympl_line hl hlam hM hM0, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero,
      one_mul, hsm, map_add, hx, add_assoc]
    rfl
  have hg : DifferentiableAt ℝ (fun t => f (w + L t)) (t + (0 : ℝ) • Pi.single i 1) :=
    ((hf.smooth n L hL hL0 w).differentiable (by simp)).differentiableAt
  have hl' : HasDerivAt (fun s : ℝ => t + s • (Pi.single i (1 : ℝ) : Fin n → ℝ)) (Pi.single i 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i (1 : ℝ) : Fin n → ℝ)).const_add t
  have h2 := hg.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl'
  rw [zero_smul, add_zero] at h2
  have h3 : HasDerivAt (fun s : ℝ => f (w + L (t + s • Pi.single i 1)))
      (-c * heisO ψ S T (M 0) f x + Complex.exp (-(((0 : ℝ) : ℂ) * c)) * dLine ψ S T M f x) 0 := by
    have e : (fun s : ℝ => f (w + L (t + s • Pi.single i 1))) =
        fun s : ℝ => Complex.exp (-((s : ℂ) * c)) * heisO ψ S T (M s) f x := funext fun s => (e1 s).symm
    rw [e]
    exact h1
  have := h2.unique h3
  rw [this, map_zero, GlobalTheory.WeilVacMove.heisO_zero]
  simp only [Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, one_mul]
  ring

theorem avg_smooth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (K : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (𝒢 : Set (K → WO S T → ℂ)), (∀ F ∈ 𝒢, Continuous fun p : K × WO S T => F p.1 p.2) → (∀ F ∈ 𝒢, ∀ k, IsThetaFunO ψ S T (F k)) → (∀ F ∈ 𝒢, ∀ M : ℝ →+ WO S T, Continuous M → (∀ s, (M s).map (finPart D) = 0) → (fun k => GlobalTheory.WeilVacMove.dLine ψ S T M (F k)) ∈ 𝒢) → ∀ F ∈ 𝒢, ∀ (n : ℕ) (L : (Fin n → ℝ) →+ WO S T), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ∞ fun t => ∫ k, F k (w + L t) ∂μ := by
  intro D ψ hψ S T K _ _ _ _ μ _ 𝒢 hc hth hcl F hF n L hL hL0 w
  obtain ⟨lam, hl, hlam⟩ := exists_log hψ
  have hs : ∀ i, Continuous (AddMonoidHom.single (fun _ : Fin n => ℝ) i) := by
    intro i
    refine continuous_pi fun j => ?_
    by_cases h : j = i
    · subst h; simp; exact continuous_id'
    · simpa [h] using continuous_const
  let M : Fin n → ℝ →+ WO S T := fun i => L.comp (AddMonoidHom.single (fun _ : Fin n => ℝ) i)
  have hM : ∀ i, Continuous (M i) := fun i => hL.comp (hs i)
  have hM0 : ∀ i s, (M i s).map (finPart D) = 0 := fun i s => hL0 _
  let φ : Fin n → (Fin n → ℝ) → ℂ := fun i t => -phase lam S T (M i 1) (w + L t)
  let 𝒢' : Set (K → (Fin n → ℝ) → ℂ) := {G | ∃ F ∈ 𝒢, G = fun k t => F k (w + L t)}
  have hφ : ∀ i, ContDiff ℝ ∞ (φ i) := by
    intro i
    have hc' : Continuous ((phase lam S T (M i 1)).comp L) :=
      hl.comp (continuous_symplOH S T hL continuous_const)
    have e : φ i = fun t => -(phase lam S T (M i 1) w + ((phase lam S T (M i 1)).comp L) t) := by
      funext t
      simp only [φ, map_add, AddMonoidHom.comp_apply]
    rw [e]
    exact (contDiff_const.add (contDiff_additive _ hc')).neg
  have hmem : (fun k t => F k (w + L t)) ∈ 𝒢' := ⟨F, hF, rfl⟩
  refine GlobalTheory.T.contDiff_compactAverage_of_closed_partials K μ n φ hφ 𝒢' ?_ ?_ ?_ _ hmem
  · rintro G ⟨F, hF, rfl⟩
    exact (hc F hF).comp (continuous_fst.prodMk (continuous_const.add (hL.comp continuous_snd)))
  · rintro G ⟨F, hF, rfl⟩ k
    exact ((hth F hF k).smooth n L hL hL0 w).differentiable (by simp)
  · rintro G ⟨F, hF, rfl⟩ i
    refine ⟨fun k t => GlobalTheory.WeilVacMove.dLine ψ S T (M i) (F k) (w + L t), ⟨_, hcl F hF (M i) (hM i) (hM0 i), rfl⟩,
      fun k t => ?_⟩
    exact GlobalTheory.ThetaAvgSmooth.key hψ hl hlam L hL hL0 w (F k) (hth F hF k) t i

end GlobalTheory.ThetaAvgSmooth
