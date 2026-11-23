import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ReTraceEq
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.PlanchLoc

noncomputable section

open MeasureTheory FourierTransform

namespace PositivityTheory.Rg.Sw.Glob.PlanchH

open PositivityTheory.Rg.Sw.Glob.FTD

variable {m n : ℕ}

theorem haar_linR (A : (Fin m → Fin n → ℂ) ≃L[ℝ] V m n) : ∃ c : ℝ, 0 < c ∧ ∀ F : V m n → ℝ, Continuous F →
    ∫ y : Fin m → Fin n → ℂ, F (A y) = c * ∫ w, F w := by
  have : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  set μ' : Measure (V m n) := (volume : Measure (Fin m → Fin n → ℂ)).map A with hμ'
  have : μ'.IsAddHaarMeasure := A.isAddHaarMeasure_map volume
  have h := Measure.isAddLeftInvariant_eq_smul μ' volume
  refine ⟨Measure.addHaarScalarFactor μ' volume, by
    exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ' volume, fun F hF => ?_⟩
  have h' : ∫ y, F y ∂μ' = ∫ y, F y ∂(Measure.addHaarScalarFactor μ' volume • volume) :=
    congrArg (fun ν => ∫ y, F y ∂ν) h
  rw [← integral_map A.continuous.aemeasurable hF.aestronglyMeasurable, ← hμ', h', integral_smul_nnreal_measure]
  simp [NNReal.smul_def]

end PositivityTheory.Rg.Sw.Glob.PlanchH

namespace PositivityTheory.Rg.Sw.Glob

open PositivityTheory.Rg.Sw.Glob.FTD PositivityTheory.Rg.Sw.Glob.PlanchH

theorem planchLoc : PlanchLoc := by
  intro m n ε t ht
  obtain ⟨c1, hc1, hft⟩ := ftLoc_eq (m := m) (n := n) ε t ht
  obtain ⟨kM, hkM, hM⟩ := haar_linR (Mt (m := m) (n := n) ε t ht)
  obtain ⟨kL, hkL, hL⟩ := haar_linR (Lc (m := m) (n := n))
  refine ⟨c1 ^ 2 * kM / kL, by positivity, fun f hf => ?_⟩
  obtain ⟨S, rfl⟩ := hf
  set g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (Lc (m := m) (n := n)).symm S with hg
  have e1 : ∀ u, ‖ftLoc ε t (⇑S) u‖ ^ 2 = c1 ^ 2 * ‖(𝓕 g) (Mt ε t ht u)‖ ^ 2 := by
    intro u
    rw [hft S u, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg hc1.le]
  have e2 : ∀ u, ‖S u‖ ^ 2 = ‖g (Lc u)‖ ^ 2 := by
    intro u
    simp [hg]
  simp_rw [e1, e2]
  have h1 := hM (fun w => ‖(𝓕 g) w‖ ^ 2) ((SchwartzMap.continuous _).norm.pow 2)
  have h2 := hL (fun w => ‖g w‖ ^ 2) ((SchwartzMap.continuous _).norm.pow 2)
  rw [integral_const_mul, h1, h2, SchwartzMap.integral_norm_sq_fourier g]
  field_simp

end PositivityTheory.Rg.Sw.Glob
