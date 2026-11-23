import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.MatrixEqFrameConjugate
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.BddOfPer

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KSing

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem fourierStep (hCE : CoefEx) (hFZ : FourierZero) (hAux : AuxiliaryPrimeFunction) (d : SD σ) (R : RD d) (w : InfinitePlace F)
    (f : d.G → ℂ) (hf : Continuous f) (hinv : ∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g)
    (hL : ∀ L ∈ d.lamSet, L f = 0) (ψ₀ : (Fin d.n → Fin d.n → ℝ) → ℂ) (hψ : IsSingTest ψ₀)
    (nr : (Fin d.n → Fin d.n → ℝ) → GR d.n) (hnr : ∀ x, mR (nr x) = nU (herm x)) :
    ∀ z, ∫ x, f (R.ι w (nr x) * z) * ψ₀ x = 0 := by
  obtain ⟨-, -, hG, hLC, -, hSC⟩ := hAux F E σ d
  haveI := hG
  haveI := hLC
  haveI := hSC
  obtain ⟨nb, lam, 𝓖, hCD⟩ := hCE F E σ d
  obtain ⟨β, hβc, hβ⟩ := nbw d R w hCD.1 nr hnr
  have hnrc := cont_nr nr hnr
  have hφc : Continuous fun y : d.G => ∫ x, f (R.ι w (nr x) * y) * ψ₀ x := by
    have hc : Continuous (Function.uncurry fun (y : d.G) (x : Fin d.n → Fin d.n → ℝ) => f (R.ι w (nr x) * y) * ψ₀ x) :=
      (hf.comp (((R.cont w).comp (hnrc.comp continuous_snd)).mul continuous_fst)).mul (hψ.1.comp continuous_snd)
    have h1 := continuous_parametric_integral_of_continuous (μ := (volume : Measure (Fin d.n → Fin d.n → ℝ))) hc
      hψ.2.1.isCompact
    refine h1.congr fun y => ?_
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have hφinv : ∀ β₀ ∈ nF σ d.Y d.b, ∀ g, (fun y : d.G => ∫ x, f (R.ι w (nr x) * y) * ψ₀ x) (nb β₀ * g) =
      (fun y : d.G => ∫ x, f (R.ι w (nr x) * y) * ψ₀ x) g := by
    intro β₀ hβ₀ g
    simp only
    congr 1
    funext x
    rw [hβ x, ← mul_assoc, ← nb_add d hCD.1, add_comm, nb_add d hCD.1, mul_assoc, hinv _ (nb_rat d hCD.1 hβ₀)]
  have hφco : ∀ T g, fc d.B.ψ d.b nb lam 𝓖 (fun y : d.G => ∫ x, f (R.ι w (nr x) * y) * ψ₀ x) T g = 0 := by
    intro T g
    rw [fc_avg d R w hG hCD f hf hinv ψ₀ hψ.1 hψ.2.1 nr hnr β hβc hβ T g]
    by_cases hT : T.1.1.det = 0
    · obtain ⟨β', hβ'h, hβ'd, hβ'e⟩ := charW d R w hCD.1 nr hnr β hβ T
      simp_rw [hβ'e]
      rw [hψ.2.2 β' hβ'h (hβ'd hT), mul_zero]
    · have h0 := hL (fun f => fc d.B.ψ d.b nb lam 𝓖 f T g) ⟨nb, lam, 𝓖, T, g, hCD, hT, rfl⟩
      rw [show fc d.B.ψ d.b nb lam 𝓖 f T g = 0 from h0, zero_mul]
  intro z
  exact congrFun (hFZ F E σ d nb lam 𝓖 hCD _ hφc hφinv hφco) z

end PositivityTheory.SiegelWeilFormula.KSing

end
