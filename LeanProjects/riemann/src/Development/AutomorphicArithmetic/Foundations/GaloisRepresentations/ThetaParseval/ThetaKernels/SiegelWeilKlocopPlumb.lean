import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.OmSch
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopPlace

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace SD
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.om_sch : ∀ (x : d.G), ∀ Φ ∈ d.sch, d.om x Φ ∈ d.sch := fun x Φ hΦ =>
  d.ok.dbl.weil.2.1.pres x Φ hΦ
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.T_zero : d.T 0 = 0 := by
  funext X
  have h : ∀ p : (d.κ → AF F) × (d.κ → AF F), schr d.B.ψ p (0 : d.Fn) = 0 := fun p => by
    funext x
    simp [schr]
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, Darboux.rho, h, map_zero, Pi.zero_apply]
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.T_inj (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) : ∀ Φ ∈ d.sch, d.T Φ = 0 → Φ = 0 := fun Φ hΦ h => (hT.1 F E σ d).2.2 Φ hΦ h
end SD
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc_surj (w : InfinitePlace F) : ∀ (X : Mx F E d.m d.n) (u : Fin d.m → Fin d.n → ℂ), ∃ Z : Mx F E d.m d.n,
    (∀ w', w' ≠ w → d.cw w' Z = 0) ∧ finOne F • Z = 0 ∧ R.loc w (X + Z) = u := by
  intro X u
  obtain ⟨ins, h1, h2, h3⟩ := d.exists_insW w
  set M : Matrix (Fin d.m) (Fin d.n) ℂ := (R.fr w).1 * (Matrix.of u).map star - d.cw w X with hM
  refine ⟨M.map ins, fun w' hw' => ?_, ?_, ?_⟩
  · ext i j
    simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, h2 w' hw']
  · ext i j
    simp [h3]
  · have hc : d.cw w (X + M.map ins) = (R.fr w).1 * (Matrix.of u).map star := by
      have : d.cw w (M.map ins) = M := by
        ext i j
        simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, h1]
      rw [show d.cw w (X + M.map ins) = d.cw w X + d.cw w (M.map ins) from by
        ext i j; simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw], this, hM]
      abel
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.loc, hc, ← Matrix.mul_assoc]
    rw [show ((R.fr w)⁻¹).1 * (R.fr w).1 = 1 from by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one], Matrix.one_mul]
    ext i j
    simp
end RD
end PositivityTheory.SiegelWeilFormula
end
end
