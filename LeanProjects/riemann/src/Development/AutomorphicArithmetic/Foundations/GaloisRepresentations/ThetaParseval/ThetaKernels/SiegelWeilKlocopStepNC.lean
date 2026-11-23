import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.StepNC
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopRelPf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdPlace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdRDIota
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopCore
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopAway
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopStepNB

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.frame_nU (y : GR d.n) (b : Matrix (Fin d.n) (Fin d.n) ℂ) (hy : mR y = nU b) :
    inFrame d.b (R.ι w y) = Matrix.fromBlocks 1 (inFrame d.b (R.ι w y)).toBlocks₁₂ 0 1 ∧
    d.cw w (inFrame d.b (R.ι w y)).toBlocks₁₂ = R.ζ • b ∧
    (∀ w', w' ≠ w → d.cw w' (inFrame d.b (R.ι w y)).toBlocks₁₂ = 0) ∧ finOne F • (inFrame d.b (R.ι w y)).toBlocks₁₂ = 0 := by
  have hζ0 : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  set M := inFrame d.b (R.ι w y) with hM
  have hw : d.cw w M = nU (R.ζ • b) := by rw [hM, R.cw_iota_pf w y, hy, dZ_conj_nU hζ0]
  have ho : ∀ w', w' ≠ w → d.cw w' M = 1 := fun w' h => R.off_w w w' y h
  have hf : finOne F • M = finOne F • 1 := R.off_f w y
  have o1 := one_blocks (n := d.n) (1 : ℂ)
  have of := one_blocks (n := d.n) (finOne F • (1 : AE F E))
  simp only [one_smul] at o1
  have hf' : finOne F • M = (finOne F • (1 : AE F E)) • (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) := by
    rw [hf, smul_one_smul]
  have e11 : M.toBlocks₁₁ = 1 := by
    apply _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d
    · intro w'
      rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_one_k d]
      show (d.cw w' M).toBlocks₁₁ = 1
      by_cases h : w' = w
      · rw [h, hw]; simp [nU]
      · rw [ho w' h]; exact o1.1
    · show (finOne F • M).toBlocks₁₁ = _
      rw [hf', of.1, smul_one_smul]
  have e21 : M.toBlocks₂₁ = 0 := by
    apply _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d
    · intro w'
      rw [show d.cw w' (0 : Matrix (Fin d.n) (Fin d.n) (AE F E)) = 0 from Matrix.map_zero _ (map_zero _)]
      show (d.cw w' M).toBlocks₂₁ = 0
      by_cases h : w' = w
      · rw [h, hw]; simp [nU]
      · rw [ho w' h]; exact o1.2.2.1
    · show (finOne F • M).toBlocks₂₁ = _
      rw [hf', of.2.2.1, smul_zero]
  have e22 : M.toBlocks₂₂ = 1 := by
    apply _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d
    · intro w'
      rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_one_k d]
      show (d.cw w' M).toBlocks₂₂ = 1
      by_cases h : w' = w
      · rw [h, hw]; simp [nU]
      · rw [ho w' h]; exact o1.2.2.2
    · show (finOne F • M).toBlocks₂₂ = _
      rw [hf', of.2.2.2, smul_one_smul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
    rw [e11, e21, e22]
  · show (d.cw w M).toBlocks₁₂ = _
    rw [hw]; simp [nU]
  · intro w' h
    show (d.cw w' M).toBlocks₁₂ = _
    rw [ho w' h]; exact o1.2.1
  · show (finOne F • M).toBlocks₁₂ = _
    rw [hf', of.2.1]
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.stepN_pf (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) : ∀ (y : GR d.n) (b : Matrix (Fin d.n) (Fin d.n) ℂ), bᴴ = b → mR y = nU b →
    R.StepOK w (R.ι w y) (fun f u => Complex.exp (2 * Real.pi * Complex.I * ((R.sg w : ℤ) : ℂ) *
      Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))) * f u) id := by
  intro y b hb hy
  obtain ⟨hM, hβw, hβo, hβf⟩ := R.frame_nU w y b hy
  refine ⟨fun f hf => ?_, fun Ψ hΨ => ⟨hΨ, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · obtain ⟨φ, rfl⟩ := hf
    obtain ⟨ψ, hψ⟩ := GlobalTheory.T.schwartz_quadratic_phase_multiplication d.m d.n (((R.sg w : ℤ) : ℝ)) b hb φ
    refine ⟨ψ, ?_⟩
    rw [hψ]
    funext u
    push_cast
    rfl
  · funext X
    rw [(hT.2.1 F E σ d Φ hΦ).1 (R.ι w y) _ hM X, R.psi_nU w b hb _ hβw hβo hβf X, hTΦ]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, id]
    ring
end RD
end PositivityTheory.SiegelWeilFormula
end
end
