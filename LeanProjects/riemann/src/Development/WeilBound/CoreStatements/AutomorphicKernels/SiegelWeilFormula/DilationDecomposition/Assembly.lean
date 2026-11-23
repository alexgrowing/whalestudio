import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.FirstCountableGR

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Kdil

theorem iteratedDeriv_mul_const' (f : ℂ → ℂ) (c : ℂ) :
    ∀ r : ℕ, iteratedDeriv r (fun z => f z * c) = fun z => iteratedDeriv r f z * c := by
  intro r
  induction r with
  | zero => simp
  | succ r ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    funext z
    exact deriv_mul_const_field _

set_option maxHeartbeats 400000 in

theorem gIdil_of (hT : TAll) (hAux : AuxiliaryPrimeFunction) (hLE : LocOpEx) (hTP : ThetaPt) (hFP : FPSw) (hMC : MatCount)
    (hSD : SplitDom) (hTB : ThetaBdd) (hLF : LocFamG) (hBD : BigDense) (hHM : HolMean)
    (hDC : DerCont) (hSO : StripOK) : GIdil := by
  intro F E _ _ _ _ _ σ d R w Ψ hΨ φ hφ g X a ha
  unfold TAll at hT
  have hTA : ThetaAuto := hT.2.2.2.2
  obtain ⟨hμ0, hμT, hTA'⟩ := hTA F E σ d
  haveI : IsTopologicalGroup d.G := (hAux F E σ d).2.2.1
  haveI : Countable (Matrix (Fin d.m) (Fin d.n) E) := hMC E d.m d.n
  obtain ⟨L, hL⟩ := hLE F E σ d R w
  obtain ⟨y₀, Ψ', hsplit, hgauss⟩ := hSD F E σ d R w L hL Ψ hΨ g
  obtain ⟨Gf, hGt, hGd, hGc, hGb, hGr⟩ := hLF F E σ d R w L hL X a ha
  obtain ⟨hUo, hUt, hUb⟩ := hSO d.n X
  set ν : Measure (UA σ d.A.J) := ((d.μ.restrict d.D) Set.univ)⁻¹ • d.μ.restrict d.D with hν
  have hνu : ν Set.univ = 1 := by
    rw [hν, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hμ0 hμT
  haveI : IsFiniteMeasure ν := ⟨by rw [hνu]; exact ENNReal.one_lt_top⟩
  let Mt : UA σ d.A.J → Matrix (Fin d.m) (Fin d.n) E → Mx F E d.m d.n := fun h k => mat h⁻¹ * incM F k
  let Fk : GR d.n → ℂ → UA σ d.A.J → Matrix (Fin d.m) (Fin d.n) E → ℂ :=
    fun p z h k => Gf (y₀ * p) z (R.loc w (Mt h k)) * Ψ' (Mt h k)
  have hsum : ∀ (P : PX d.m d.n) (y : GR d.n) (h : UA σ d.A.J),
      thetaSum F ((d.om (g * R.ι w y)) ((d.S h) (φ P))) =
        ∑' k, L (y₀ * y) (fP P) (R.loc w (Mt h k)) * Ψ' (Mt h k) := by
    intro P y h
    rw [hTP F E σ d (φ P) (hφ P).1 (g * R.ι w y) h,
      hsplit (φ P) (hφ P).1 (fP P) (hFP d.m d.n P) (hφ P).2 y]
    rfl
  have hid : ∀ (p : GR d.n) (t : ℝ) (h : UA σ d.A.J),
      ∑' k, Fk p t h k = thetaSum F ((d.om (g * R.ι w (p * a t))) ((d.S h) (φ 1))) := by
    intro p t h
    rw [hsum 1 (p * a t) h]
    refine tsum_congr fun k => ?_
    show Gf (y₀ * p) (t : ℂ) (R.loc w (Mt h k)) * Ψ' (Mt h k) = _
    rw [hGt, mul_assoc y₀ p (a t)]
  have hshift : Continuous fun q : GR d.n × ℂ => (y₀ * q.1, q.2) :=
    (continuous_const.mul continuous_fst).prodMk continuous_snd
  have hdiff : ∀ p h k, DifferentiableOn ℂ (fun z => Fk p z h k) (strip X) :=
    fun p h k => (hGd (y₀ * p) _).mul_const _
  have hcont : ∀ h k, ContinuousOn (fun q : GR d.n × ℂ => Fk q.1 q.2 h k) (Set.univ ×ˢ strip X) := by
    intro h k
    have hmap : Set.MapsTo (fun q : GR d.n × ℂ => (y₀ * q.1, q.2)) (Set.univ ×ˢ strip X)
        (Set.univ ×ˢ strip X) := fun q hq => ⟨Set.mem_univ _, hq.2⟩
    exact ((hGc (R.loc w (Mt h k))).comp hshift.continuousOn hmap).mul continuousOn_const
  have hmeas : ∀ (p : GR d.n) (t : ℝ), (t : ℂ) ∈ strip X →
      AEStronglyMeasurable (fun h => ∑' k, Fk p t h k) ν := by
    intro p t _
    have hI := (hTA' (φ 1) (hφ 1).1).1 (g * R.ι w (p * a t))
    have he : (fun h => ∑' k, Fk p t h k) =
        fun h => thetaSum F ((d.om (g * R.ι w (p * a t))) ((d.S h) (φ 1))) :=
      funext fun h => hid p t h
    rw [he]
    exact hI.aestronglyMeasurable.smul_measure _
  have hdom : ∀ q ∈ Set.univ ×ˢ strip X, ∃ N ∈ 𝓝 q,
      ∃ (M : UA σ d.A.J → Matrix (Fin d.m) (Fin d.n) E → ℝ) (b : UA σ d.A.J → ℝ),
        (∀ h, Summable (M h)) ∧ Integrable b ν ∧ (∀ h, ∑' k, M h k ≤ b h) ∧
          ∀ q' ∈ N, q'.2 ∈ strip X → ∀ h k, ‖Fk q'.1 q'.2 h k‖ ≤ M h k := by
    intro q hq
    obtain ⟨N, hN, C, δ, hδ, hb⟩ := hGb (y₀ * q.1, q.2) ⟨Set.mem_univ _, hq.2⟩
    obtain ⟨K, hK⟩ := hTB F E σ d _ (hgauss δ hδ)
    refine ⟨(fun q : GR d.n × ℂ => (y₀ * q.1, q.2)) ⁻¹' N, hshift.continuousAt.preimage_mem_nhds hN,
      fun h k => max C 0 * ‖R.tens w (fun u => ((Real.exp (-δ * sq u) : ℝ) : ℂ)) Ψ' (Mt h k)‖,
      fun _ => max C 0 * K, fun h => (hK h).1.mul_left _, integrable_const _, fun h => ?_, ?_⟩
    · rw [tsum_mul_left]
      exact mul_le_mul_of_nonneg_left (hK h).2 (le_max_right _ _)
    · intro q' hq' hq'U h k
      have hb' := hb (y₀ * q'.1, q'.2) hq' hq'U (R.loc w (Mt h k))
      show ‖Gf (y₀ * q'.1) q'.2 (R.loc w (Mt h k)) * Ψ' (Mt h k)‖ ≤
        max C 0 * ‖((Real.exp (-δ * sq (R.loc w (Mt h k))) : ℝ) : ℂ) * Ψ' (Mt h k)‖
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (hb'.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)) (norm_nonneg _)
  obtain ⟨hHc, hHd, hHr⟩ := hHM (GR d.n) (UA σ d.A.J) (Matrix (Fin d.m) (Fin d.n) E) ν (strip X)
    hUo hUb Fk hdiff hcont hmeas hdom
  have h0 : (0 : ℂ) ∈ strip X := by simpa using hUt 0
  refine ⟨strip X, fun y z => ∫ h, ∑' k, Fk y z h k ∂ν, hUo, hUt, hHc,
    fun y => ⟨hHd y, fun t => ?_, fun r => ?_⟩⟩
  · show ∫ h, ∑' k, Fk y t h k ∂ν = ∫ h, thetaSum F ((d.om (g * R.ι w (y * a t))) ((d.S h) (φ 1))) ∂ν
    exact integral_congr_ae (ae_of_all _ fun h => hid y t h)
  · have hDC' : ContinuousOn
        (fun q : GR d.n × ℂ => iteratedDeriv r (fun z => ∫ h, ∑' k, Fk q.1 z h k ∂ν) q.2)
        (Set.univ ×ˢ strip X) :=
      hDC (GR d.n) (strip X) hUo (fun y z => ∫ h, ∑' k, Fk y z h k ∂ν) hHc hHd r
    have hcL : Continuous fun y : GR d.n => iteratedDeriv r (fun z => ∫ h, ∑' k, Fk y z h k ∂ν) 0 :=
      hDC'.comp_continuous (f := fun y : GR d.n => (y, (0 : ℂ)))
        (continuous_id.prodMk continuous_const) (fun y => ⟨Set.mem_univ _, h0⟩)
    have hcR : Continuous fun y : GR d.n => d.I (φ ((dil (2 * Real.pi) X ^ r) 1)) (g * R.ι w y) :=
      (hTA' _ (hφ _).1).2.1.comp (continuous_const.mul (R.cont w))
    have hdense : Dense {y : GR d.n | (Matrix.toBlocks₂₂ (mR (y₀ * y))).det ≠ 0} :=
      (hBD d.n).preimage (isOpenMap_mul_left y₀)
    have heq := Continuous.ext_on hdense hcL hcR (fun y hy => by
      show iteratedDeriv r (fun z => ∫ h, ∑' k, Fk y z h k ∂ν) 0 =
        ∫ h, thetaSum F ((d.om (g * R.ι w y)) ((d.S h) (φ ((dil (2 * Real.pi) X ^ r) 1)))) ∂ν
      rw [hHr y 0 h0 r]
      refine integral_congr_ae (ae_of_all _ fun h => ?_)
      show ∑' k, iteratedDeriv r (fun z => Fk y z h k) 0 =
        thetaSum F ((d.om (g * R.ι w y)) ((d.S h) (φ ((dil (2 * Real.pi) X ^ r) 1))))
      rw [hsum _ y h]
      refine tsum_congr fun k => ?_
      show iteratedDeriv r (fun z => Gf (y₀ * y) z (R.loc w (Mt h k)) * Ψ' (Mt h k)) 0 = _
      rw [iteratedDeriv_mul_const' (fun z => Gf (y₀ * y) z (R.loc w (Mt h k))) (Ψ' (Mt h k)) r]
      show iteratedDeriv r (fun z => Gf (y₀ * y) z (R.loc w (Mt h k))) 0 * Ψ' (Mt h k) = _
      rw [hGr (y₀ * y) hy r])
    exact congrFun heq y

end PositivityTheory.SiegelWeilFormula.Kdil

end
