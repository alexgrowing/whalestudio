import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.WhitKOfSteps

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem om_mem_sch (d : SD σ) (x : d.G) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) : d.om x Φ ∈ d.sch :=
  d.ok.dbl.weil.2.1.pres x Φ hΦ

theorem T_zero (d : SD σ) {Φ : d.Fn} (_hΦ : Φ ∈ d.sch) : d.T Φ 0 = d.l Φ := by
  unfold SD.T
  rw [Matrix.zero_mul]
  congr 1
  funext y
  simp [Darboux.rho, schr]

theorem gram_zero_left (d : SD σ) (Z : Mx F E d.m d.n) : d.gram 0 Z = 0 := by
  simp [SD.gram]

theorem cellFormula : CellFormula := by
  intro hT F E _ _ _ _ _ σ d ν hν ε w hw Φ hΦ g x β hg
  have hΨ : d.om x Φ ∈ d.sch := om_mem_sch d x hΦ
  have hΨ' : d.om g (d.om x Φ) ∈ d.sch := om_mem_sch d g hΨ
  have hW := hT.2.2.1 F E σ d ν hν ε w hw _ hΨ' 0
  have hP := (hT.2.1 F E σ d _ hΨ).1 g β hg
  calc d.sec0 Φ (w * g * x) = d.l (d.om w (d.om g (d.om x Φ))) := by
        show d.l (d.om (w * g * x) Φ) = _
        rw [map_mul, map_mul]
        rfl
    _ = d.T (d.om w (d.om g (d.om x Φ))) 0 := (T_zero d (om_mem_sch d w hΨ')).symm
    _ = ∫ Z, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram 0 Z)) * d.T (d.om g (d.om x Φ)) Z ∂ν := hW
    _ = _ := by
        congr 1
        funext Z
        rw [gram_zero_left d Z, hP Z]
        simp [SD.tt]

end PositivityTheory.SiegelWeilFormula.KWhit

end
