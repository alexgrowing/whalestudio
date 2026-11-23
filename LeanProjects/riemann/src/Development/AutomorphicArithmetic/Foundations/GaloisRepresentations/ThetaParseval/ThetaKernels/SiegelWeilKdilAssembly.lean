import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.Assembly
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKdilSteps

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Kdil
theorem gIdil_of_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hAux : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hLE : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hTP : _root_.PositivityTheory.SiegelWeilFormula.Kdil.ThetaPt_k) (hFP : FPSw) (hMC : MatCount)
    (hSD : _root_.PositivityTheory.SiegelWeilFormula.Kdil.SplitDom_k) (hTB : _root_.PositivityTheory.SiegelWeilFormula.Kdil.ThetaBdd_k) (hLF : _root_.PositivityTheory.SiegelWeilFormula.Kdil.LocFamG_k) (hBD : BigDense) (hHM : HolMean)
    (hDC : DerCont) (hSO : StripOK) : _root_.PositivityTheory.SiegelWeilFormula.GIdil_k := by
  intro F E _ _ _ _ _ σ d R w Ψ hΨ φ hφ g X a ha
  obtain ⟨-, -, -, -, hTA⟩ := hT
  obtain ⟨hμ0, hμT, hTA'⟩ := hTA F E σ d
  obtain ⟨-, -, hGtop, -, -, -⟩ := hAux F E σ d
  obtain ⟨L, hL⟩ := hLE F E σ d R w
  obtain ⟨y₀, Ψ', hrep, hmaj⟩ := hSD F E σ d R w L hL Ψ hΨ g
  obtain ⟨Gf, hreal, hhol, hcont, hbd, hder⟩ := hLF F E σ d R w L hL X a ha
  obtain ⟨hUo, hUR, hUb⟩ := hSO d.n X
  have hcount := hMC E d.m d.n
  set U := strip X with hU
  have h0U : (0 : ℂ) ∈ U := by simpa using hUR 0
  set Fm : GR d.n → ℂ → UA σ d.A.J → Matrix (Fin d.m) (Fin d.n) E → ℂ := fun y z h Xr =>
    Gf (y₀ * y) z (R.loc w (mat h⁻¹ * incM F Xr)) * Ψ' (mat h⁻¹ * incM F Xr) with hFm
  set ν : Measure (UA σ d.A.J) := (d.μ.restrict d.D Set.univ)⁻¹ • d.μ.restrict d.D with hν
  have hav : ∀ f : UA σ d.A.J → ℂ, (⨍ h in d.D, f h ∂d.μ) = ∫ h, f h ∂ν := fun f => rfl
  have hc : (d.μ.restrict d.D Set.univ)⁻¹ ≠ ⊤ := by
    rw [ENNReal.inv_ne_top, Measure.restrict_apply_univ]; exact hμ0
  haveI : IsFiniteMeasure (d.μ.restrict d.D) := isFiniteMeasure_restrict.mpr hμT
  have hI : ∀ Φ ∈ d.sch, ∀ x, d.I Φ x =
      ∫ h, ∑' Xr : Matrix (Fin d.m) (Fin d.n) E, d.T (d.om x Φ) (mat h⁻¹ * incM F Xr) ∂ν := by
    intro Φ hΦ x
    rw [← hav]
    show (⨍ h in d.D, thetaSum F (d.om x (d.S h Φ)) ∂d.μ) = _
    simp_rw [hTP F E σ d Φ hΦ x]
  have hT1 : ∀ P y', d.T (d.om (g * R.ι w y') (φ P)) = R.tens w (L (y₀ * y') (fP P)) Ψ' := fun P y' =>
    hrep (φ P) (hφ P).1 (fP P) (hFP _ _ P) (hφ P).2 y'
  obtain ⟨hHc, hHd, hHr⟩ := hHM (GR d.n) (UA σ d.A.J) (Matrix (Fin d.m) (Fin d.n) E) ν U hUo hUb Fm
    (fun p h Xr => (hhol (y₀ * p) _).mul_const _)
    (fun h Xr => ((hcont (R.loc w (mat h⁻¹ * incM F Xr))).comp (f := fun q : GR d.n × ℂ => (y₀ * q.1, q.2))
      (by fun_prop) (fun q hq => ⟨trivial, hq.2⟩)).mul continuousOn_const)
    (by
      intro p t _
      have e : (fun h => ∑' k, Fm p t h k) = fun h => thetaSum F (d.om (g * R.ι w (p * a t)) (d.S h (φ 1))) := by
        funext h
        rw [hTP F E σ d (φ 1) (hφ 1).1, hT1 1 (p * a t)]
        simp only [hFm, _root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hreal, mul_assoc]
      rw [e]
      exact ((hTA' (φ 1) (hφ 1).1).1 _).aestronglyMeasurable.smul_measure _)
    (by
      rintro ⟨p, z⟩ ⟨-, hz⟩
      obtain ⟨N, hN, C, δ, hδ, hCb⟩ := hbd (y₀ * p, z) ⟨trivial, hz⟩
      obtain ⟨K, hK⟩ := hTB F E σ d _ (hmaj δ hδ)
      refine ⟨(fun q : GR d.n × ℂ => (y₀ * q.1, q.2)) ⁻¹' N,
        (Continuous.continuousAt (by fun_prop)).preimage_mem_nhds hN,
        fun h Xr => |C| * ‖R.tens w (fun u => (Real.exp (-δ * sq u) : ℂ)) Ψ' (mat h⁻¹ * incM F Xr)‖,
        fun _ => |C| * K, fun h => (hK h).1.mul_left _, (integrable_const _).smul_measure hc, ?_, ?_⟩
      · intro h
        rw [tsum_mul_left]
        exact mul_le_mul_of_nonneg_left (hK h).2 (abs_nonneg C)
      · intro q' hq' hq'U h Xr
        have hb1 := hCb (y₀ * q'.1, q'.2) hq' hq'U (R.loc w (mat h⁻¹ * incM F Xr))
        have he : 0 ≤ Real.exp (-δ * sq (R.loc w (mat h⁻¹ * incM F Xr))) := (Real.exp_pos _).le
        simp only [hFm, _root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg he]
        calc ‖Gf (y₀ * q'.1) q'.2 (R.loc w (mat h⁻¹ * incM F Xr))‖ * ‖Ψ' (mat h⁻¹ * incM F Xr)‖
            ≤ (C * Real.exp (-δ * sq (R.loc w (mat h⁻¹ * incM F Xr)))) * ‖Ψ' (mat h⁻¹ * incM F Xr)‖ :=
              mul_le_mul_of_nonneg_right hb1 (norm_nonneg _)
          _ ≤ (|C| * Real.exp (-δ * sq (R.loc w (mat h⁻¹ * incM F Xr)))) * ‖Ψ' (mat h⁻¹ * incM F Xr)‖ := by
              gcongr; exact le_abs_self C
          _ = _ := by ring)
  clear_value Fm
  refine ⟨U, fun y z => ∫ h, ∑' k, Fm y z h k ∂ν, hUo, hUR, hHc, fun y => ⟨hHd y, ?_, ?_⟩⟩
  · intro t
    beta_reduce
    rw [hI (φ 1) (hφ 1).1, hT1 1 (y * a t)]
    congr 1
    funext h
    congr 1
    funext Xr
    simp only [hFm, _root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hreal, mul_assoc]
  · intro r
    have key : ∀ y', ((mR (y₀ * y')).toBlocks₂₂).det ≠ 0 →
        iteratedDeriv r (fun z => ∫ h, ∑' k, Fm y' z h k ∂ν) 0 =
          d.I (φ ((dil (2 * Real.pi) X ^ r) 1)) (g * R.ι w y') := by
      intro y' hy'
      rw [hHr y' 0 h0U r, hI _ (hφ _).1, hT1]
      congr 1
      funext h
      congr 1
      funext Xr
      simp only [hFm, _root_.PositivityTheory.SiegelWeilFormula.RD_k.tens]
      rw [iteratedDeriv_mul_const' (fun z => Gf (y₀ * y') z (R.loc w (mat h⁻¹ * incM F Xr))) _ r]
      beta_reduce
      rw [hder (y₀ * y') hy' r]
    have hDC' := hDC (GR d.n) U hUo (fun y' z => ∫ h, ∑' k, Fm y' z h k ∂ν) hHc hHd r
    have hpair : Continuous fun y' : GR d.n => (y', (0 : ℂ)) := by fun_prop
    have hcL : Continuous fun y' => iteratedDeriv r (fun z => ∫ h, ∑' k, Fm y' z h k ∂ν) 0 :=
      hDC'.comp_continuous hpair (fun _ => ⟨trivial, h0U⟩)
    have hcR : Continuous fun y' => d.I (φ ((dil (2 * Real.pi) X ^ r) 1)) (g * R.ι w y') :=
      (hTA' _ (hφ _).1).2.1.comp (continuous_const.mul (R.cont w))
    have hden : Dense {y' : GR d.n | ((mR (y₀ * y')).toBlocks₂₂).det ≠ 0} :=
      (hBD d.n).preimage (isOpenMap_mul_left y₀)
    exact congrFun (hcL.ext_on hden hcR key) y
end PositivityTheory.SiegelWeilFormula.Kdil
end
end
