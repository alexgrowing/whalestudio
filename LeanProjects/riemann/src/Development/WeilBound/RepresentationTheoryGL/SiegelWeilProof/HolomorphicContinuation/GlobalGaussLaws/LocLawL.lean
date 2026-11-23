import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocInstSt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtAndIsTheta
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanParametersAddCharUnique

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocLawH

set_option synthInstance.maxHeartbeats 400000 in
theorem exists_realPar_ne (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (θ : InfFam D)
    (hθ : IsInfFam θ) : ∃ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l ∧ ∀ τ, l τ ≠ 0 := by
  obtain ⟨ψ₀, h₀, a, ha0, ha⟩ := GlobalTheory.ThetaAllChar.exists_std hψ
  set y : D.host.E := algebraMap D.host.F D.host.E a with hy_def
  have hyc : IsCMField.complexConj D.host.E y = y :=
    (IsCMField.complexConj_eq_self_iff D.host.E y).2 a.2
  have hreal : ∀ τ, (tauE D τ y).im = 0 := by
    intro τ
    have h := IsCMField.complexEmbedding_complexConj D.host.E (tauE D τ) y
    rw [hyc] at h
    have := congrArg Complex.im h
    rw [Complex.conj_im] at this
    linarith
  have hy0 : y ≠ 0 := by
    rw [hy_def]
    exact (map_ne_zero_iff _ (algebraMap D.host.F D.host.E).injective).2 ha0
  refine ⟨fun τ => -(tauE D τ y).re, ?_, fun τ => ?_⟩
  · intro x
    have e1 : psiInf D.host.F ψ x = psiInf D.host.F ψ₀ (algebraMap D.host.F (Ainf D.host.F) a * x) := by
      simp only [psiInf]
      rw [ha]
      congr 1
      show (algebraMap D.host.F (Ainf D.host.F) a * x, algebraMap D.host.F (Af D.host.F) a * 0) = _
      rw [mul_zero]; rfl
    rw [e1, h₀.2.2 θ hθ]
    congr 1
    have e2 : ∀ ρ, θ ρ ((algebraMap D.host.F (Ainf D.host.F) a * x) ⊗ₜ[D.host.F] (1 : D.host.E)) =
        θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)) * tauE D ρ y := by
      intro ρ
      have e3 : (algebraMap D.host.F (Ainf D.host.F) a * x) ⊗ₜ[D.host.F] (1 : D.host.E) =
          (x ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : Ainf D.host.F) ⊗ₜ[D.host.F] y) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← Algebra.smul_def, ← TensorProduct.smul_tmul',
          ← TensorProduct.tmul_smul, Algebra.smul_def, mul_one]
      rw [e3, map_mul, (hθ ρ).1]
    simp only [e2]
    have e4 : ∀ ρ, (((-(tauE D ρ y).re : ℝ)) : ℂ) = -tauE D ρ y := by
      intro ρ
      apply Complex.ext <;> simp [hreal ρ]
    simp only [e4, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun ρ _ => ?_
    ring
  · intro h
    have h1 : tauE D τ y ≠ 0 := (map_ne_zero_iff _ (tauE D τ).injective).2 hy0
    apply h1
    apply Complex.ext
    · simp only [Complex.zero_re]; linarith
    · simp [hreal τ]

theorem cx_lne {D : D7} {n : ℕ} {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → NNReal}
    {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)} {τ : D.what₂.Tau}
    {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ι : PositivityTheory.Rg.Sw.GR n →* G D n}
    (hC : Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι) : ∀ τ', l τ' ≠ 0 := by
  obtain ⟨l', hl', hne⟩ := exists_realPar_ne D ψ hC.hψ θ hC.hθ
  rw [GlobalTheory.StdUnn.RealPar.realPar_unique D ψ θ hC.hθ l l' hC.hl hl']
  exact hne

end PositivityTheory.Rg.Sw.Glob.LocLawH

namespace PositivityTheory.Rg.Sw.Glob

open LocLawH in
theorem lIl : LIl := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC
  obtain ⟨l', hl', hne⟩ := exists_realPar_ne D ψ hC.hψ θ hC.hθ
  rw [GlobalTheory.StdUnn.RealPar.realPar_unique D ψ θ hC.hθ l l' hC.hl hl']
  exact hne τ

end PositivityTheory.Rg.Sw.Glob
