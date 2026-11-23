import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalHermitianMeasures.ExistsNeZeroOfMap
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourNA

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw SiegelEisensteinSeries.Grp
namespace PositivityTheory.SiegelWeilFormula.MeasD
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit PositivityTheory.SiegelWeilFormula.kfour
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem eta_sign_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (herm : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) {ε : ℤˣ}
    (hb : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    σ η = -(((ε : ℤ) : E)) * η := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
  · have he := frame_sign hσ d.ok.hn d.Y.J (-1) (fun i j => by rw [hY, neg_one_mul]) d.b ε hb
    obtain ⟨i, j, hij⟩ := exists_ne_zero_of_map d.A.J (d.B.emb w).1 1
      (by rw [one_smul]; exact ne_zero_of_sig d.ok.hm _ (hA.sig w))
    have h := herm i j
    rw [map_mul, hA.herm] at h
    rw [he, neg_neg, one_mul]
    exact mul_right_cancel₀ hij h
  · have he := frame_sign hσ d.ok.hn d.Y.J 1 (fun i j => by rw [hY, one_mul]) d.b ε hb
    obtain ⟨i, j, hij⟩ := exists_ne_zero_of_map d.A.J (d.B.emb w).1 Complex.I (ne_zero_of_sig d.ok.hm _ (hA.sig w))
    have h := herm i j
    rw [map_mul, hA.skew] at h
    rw [he, neg_one_mul]
    apply mul_right_cancel₀ hij
    linear_combination -h
end PositivityTheory.SiegelWeilFormula.MeasD
end
end
