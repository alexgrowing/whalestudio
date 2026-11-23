import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.MemLpSchM
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.ExpAlg
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.RotVac
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FiniteLineActions.GeoLine

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ}

theorem line_data (hT : TAll) (hU : TUnit) (hH : THeis) (hA : AuxiliaryPrimeFunction) (hF : FockMem) (hLO : LocOpEx) (hLI : LocInst)
    (R : RD d) :
    ∃ (k : d.G) (ω χ C : ℂ) (c : ℝ) (ν : Measure (Mx F E d.m d.n)) (νf : Measure (Yf d))
      (vv : Vw d → ℂ → Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)),
      k ∈ d.K ∧ ‖ω‖ = 1 ∧ (∀ j : ℕ, 0 < j → ω ^ j ≠ 1) ∧ χ ≠ 0 ∧ C ≠ 0 ∧ ν.IsAddHaarMeasure ∧
      νf.IsAddHaarMeasure ∧
      (∀ g ∈ SB (Yf d), ∀ Ω ∈ d.sch, d.T Ω = vac R g → d.om k Ω = χ • Ω) ∧
      (∀ ξ z, actB (cA σ) k (vv ξ z) = vv ξ (ω * z)) ∧
      ∀ g ∈ SB (Yf d), ∀ Ω ∈ d.sch, d.T Ω = vac R g → ∀ Φ ∈ d.sch, ∀ ξ z,
        B ν Φ (d.dd.rho d.B.ψ (vv ξ z) Ω) = C * Real.exp (-(c * ‖z‖ ^ 2 * ‖ξ‖ ^ 2)) *
          (Complex.exp (-(z ^ 2 * ‖ξ‖ ^ 2 / (16 * Real.pi))) *
            ∫ u, hg R νf (d.T Φ) g u * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2)) * Complex.exp (z * ⟪ξ, u⟫_ℝ)) := by
  obtain ⟨C, c, s, ν, νf, hC, hs, hν, hνf, hB⟩ := B_vline hT hU hH hA hF R
  obtain ⟨χ, hχ, heig⟩ := om_rot_vac' hT hLO hLI R 1
  let W : Vw d → Mx F E d.m d.n := fun ξ => jn R (s⁻¹ • ξ) 0
  have hW : ∀ ξ, finOne F • W ξ = 0 := fun ξ => (fin_eq_zero_iff _).1 (fin_jn R _ _)
  have hsW : ∀ ξ, s • arc R (W ξ) = ξ := fun ξ => by
    simp only [W, arc_jn, smul_smul, mul_inv_cancel₀ hs, one_smul]
  refine ⟨rot R 1, Complex.exp (-((1 : ℝ) * Complex.I)), χ, C, c, ν, νf, fun ξ z => vline R (W ξ) z, rot_mem R 1,
    ?_, ?_, hχ, hC, hν, hνf, heig, fun ξ z => actB_rot_vline' R 1 (hW ξ) z, fun g hg Ω hΩ hTΩ Φ hΦ ξ z => ?_⟩
  · rw [Complex.norm_exp]
    simp
  · intro j hj h
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff] at h
    obtain ⟨k, hk⟩ := h
    have h3 : -(j : ℝ) = 2 * Real.pi * k := by
      have := congrArg Complex.im hk
      simp at this
      linarith
    have hk0 : (k : ℝ) ≠ 0 := by
      intro h0
      rw [h0, mul_zero, neg_eq_zero] at h3
      exact (Nat.cast_pos.2 hj).ne' h3
    refine irrational_pi ⟨-(j : ℚ) / (2 * k), ?_⟩
    push_cast
    field_simp
    linarith
  · have := hB g hg Ω hΩ hTΩ Φ hΦ (W ξ) (hW ξ) z
    rwa [hsW] at this

theorem B_rel (hT : TAll) (hU : TUnit) {ν : Measure (Mx F E d.m d.n)} (hν : ν.IsAddHaarMeasure) {k : d.G} {χ : ℂ}
    (hχ : χ ≠ 0) {Ω : d.Fn} (hΩ : Ω ∈ d.sch) (hk : d.om k Ω = χ • Ω) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (q : Polynomial ℂ)
    (hq : ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • d.om (k ^ i) Φ = 0)
    (v : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    ∑ i ∈ Finset.range (q.natDegree + 1),
      q.coeff i * (star χ)⁻¹ ^ i * B ν Φ (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω) = 0 := by
  exact B_rel' hT hU hν hχ hΩ hk hΦ q hq v

end PositivityTheory.SiegelWeilFormula.KFP

end
