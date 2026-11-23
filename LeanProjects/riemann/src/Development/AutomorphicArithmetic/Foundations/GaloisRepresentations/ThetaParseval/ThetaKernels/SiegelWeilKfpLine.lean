import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.LineData
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.THeisK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpRel
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpGeo
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpLineB
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpRotVac
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKKfpGeoLine

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem line_data_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.TUnit_k) (hH : _root_.PositivityTheory.SiegelWeilFormula.THeis_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hLO : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hLI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k)
    (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) :
    ∃ (k : d.G) (ω χ C : ℂ) (c : ℝ) (ν : Measure (Mx F E d.m d.n)) (νf : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d))
      (vv : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d → ℂ → Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)),
      k ∈ d.K ∧ ‖ω‖ = 1 ∧ (∀ j : ℕ, 0 < j → ω ^ j ≠ 1) ∧ χ ≠ 0 ∧ C ≠ 0 ∧ ν.IsAddHaarMeasure ∧
      νf.IsAddHaarMeasure ∧
      (∀ g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d), ∀ Ω ∈ d.sch, d.T Ω = _root_.PositivityTheory.SiegelWeilFormula.KFP.vac_k R g → d.om k Ω = χ • Ω) ∧
      (∀ ξ z, actB (cA σ) k (vv ξ z) = vv ξ (ω * z)) ∧
      ∀ g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d), ∀ Ω ∈ d.sch, d.T Ω = _root_.PositivityTheory.SiegelWeilFormula.KFP.vac_k R g → ∀ Φ ∈ d.sch, ∀ ξ z,
        _root_.PositivityTheory.SiegelWeilFormula.KFP.B_k ν Φ (d.dd.rho d.B.ψ (vv ξ z) Ω) = C * Real.exp (-(c * ‖z‖ ^ 2 * ‖ξ‖ ^ 2)) *
          (Complex.exp (-(z ^ 2 * ‖ξ‖ ^ 2 / (16 * Real.pi))) *
            ∫ u, _root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf (d.T Φ) g u * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2)) * Complex.exp (z * ⟪ξ, u⟫_ℝ)) := by
  obtain ⟨C, c, s, ν, νf, hC, hs, hν, hνf, hB⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFP.B_vline_k hT hU hH hA hF R
  obtain ⟨χ, hχ, heig⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFP.om_rot_vac'_k hT hLO hLI R 1
  let W : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d → Mx F E d.m d.n := fun ξ => _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R (s⁻¹ • ξ) 0
  have hW : ∀ ξ, finOne F • W ξ = 0 := fun ξ => (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_eq_zero_iff_k _).1 (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_jn_k R _ _)
  have hsW : ∀ ξ, s • _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R (W ξ) = ξ := fun ξ => by
    simp only [W, _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_jn_k, smul_smul, mul_inv_cancel₀ hs, one_smul]
  refine ⟨_root_.PositivityTheory.SiegelWeilFormula.KFP.rot_k R 1, Complex.exp (-((1 : ℝ) * Complex.I)), χ, C, c, ν, νf, fun ξ z => _root_.PositivityTheory.SiegelWeilFormula.KFP.vline_k R (W ξ) z, _root_.PositivityTheory.SiegelWeilFormula.KFP.rot_mem_k R 1,
    ?_, ?_, hχ, hC, hν, hνf, heig, fun ξ z => _root_.PositivityTheory.SiegelWeilFormula.KFP.actB_rot_vline'_k R 1 (hW ξ) z, fun g hg Ω hΩ hTΩ Φ hΦ ξ z => ?_⟩
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
theorem B_rel_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.TUnit_k) {ν : Measure (Mx F E d.m d.n)} (hν : ν.IsAddHaarMeasure) {k : d.G} {χ : ℂ}
    (hχ : χ ≠ 0) {Ω : d.Fn} (hΩ : Ω ∈ d.sch) (hk : d.om k Ω = χ • Ω) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (q : Polynomial ℂ)
    (hq : ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • d.om (k ^ i) Φ = 0)
    (v : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    ∑ i ∈ Finset.range (q.natDegree + 1),
      q.coeff i * (star χ)⁻¹ ^ i * _root_.PositivityTheory.SiegelWeilFormula.KFP.B_k ν Φ (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω) = 0 := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KFP.B_rel'_k hT hU hν hχ hΩ hk hΦ q hq v
end PositivityTheory.SiegelWeilFormula.KFP
end
end
