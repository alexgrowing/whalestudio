import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.RatVCocompact
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourNA

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace COneB
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
def Nu_k (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) := ∑ j, Matrix.single L.i₀ (L.em j) (u j)
theorem em_ne_k (j : Fin L.n) : L.em j ≠ L.i₀ := (L.rng (L.em j)).2 ⟨j, rfl⟩
theorem Nu_mul_k (u v : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u * _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L v = 0 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
  apply Matrix.single_mul_single_of_ne
  exact _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.em_ne_k L _
theorem Nu_add_k (u v : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L (u + v) = _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u + _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L v := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k, Pi.add_apply, Matrix.single_add, Finset.sum_add_distrib]
theorem Nu_cont_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L) := by
  have e : _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L = fun u => ∑ j, u j • Matrix.single L.i₀ (L.em j) (1 : AE F E) := by
    funext u; simp only [_root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [e]
  exact continuous_finsetSum _ fun j _ => (continuous_apply j).smul continuous_const
omit L in
theorem unit_frame_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : d.G) : ∃ e : AE F E,
    (inFrame d.b x)ᵀ * Matrix.fromBlocks 0 1 (e • 1) 0 * (inFrame d.b x).map (cA σ) = Matrix.fromBlocks 0 1 (e • 1) 0 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  refine ⟨((ε : ℤ) : AE F E), ?_⟩
  have hF := kfour.frameEq_adelic (F := F) (Y := d.Y) hε
  have hU : (mat2 x)ᵀ * dbl (incM F d.Y.J) * (mat2 x).map (cA σ) = dbl (incM F d.Y.J) := x.2
  rw [SiegelEisensteinSeries.Grp.matrix_eq_frame_conjugate d.b x] at hU
  have h1 : (incM F d.b.1)ᵀ * (incM F (d.b⁻¹).1)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, SiegelEisensteinSeries.Grp.incM_inv_mul, Matrix.transpose_one]
  have h2 : (incM F (d.b⁻¹).1).map (cA σ) * (incM F d.b.1).map (cA σ) = 1 := by
    rw [← SiegelEisensteinSeries.Grp.map_cA_mul, SiegelEisensteinSeries.Grp.incM_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [← hF]
  conv_rhs => rw [← hU]
  rw [SiegelEisensteinSeries.Grp.map_cA_mul, SiegelEisensteinSeries.Grp.map_cA_mul, Matrix.transpose_mul, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [h2, Matrix.mul_one, ← Matrix.mul_assoc (incM F d.b.1)ᵀ (incM F (d.b⁻¹).1)ᵀ, h1, Matrix.one_mul]
omit L in
theorem blk_unit_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : d.G) (a a' : Matrix (Fin d.n) (Fin d.n) (AE F E))
    (hx : inFrame d.b x = Matrix.fromBlocks a 0 0 a') : aᵀ * a'.map (cA σ) = 1 := by
  obtain ⟨e, he⟩ := _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.unit_frame_k d x
  rw [hx] at he
  simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_zero,
    Matrix.map_zero _ (map_zero _), Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.mul_one] at he
  have := (Matrix.fromBlocks_inj.1 he).2.1
  exact this
omit L in
theorem cA_cA_mat_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {p q : Type} (M : Matrix p q (AE F E)) : (M.map (cA σ)).map (cA σ) = M := by
  have hσ : ∀ a, σ (σ a) = a := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  ext i j; simp [kfour.cA_cA' σ hσ]
theorem uM_frame_k {uM ν 𝓤} (hu : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) :
    inFrame d.b (uM u) = Matrix.fromBlocks (1 + _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u) 0 0 (((1 - _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u)ᵀ).map (cA σ)) := by
  obtain ⟨a', ha'⟩ := hu.1 u
  have ha : inFrame d.b (uM u) = Matrix.fromBlocks (1 + _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u) 0 0 a' := ha'
  rw [ha]
  have h1 := _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.blk_unit_k d _ _ _ ha
  have h2 : (1 - _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u)ᵀ * (1 + _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_mul_k, sub_zero,
      sub_add_cancel, Matrix.transpose_one]
  have h3 : a'.map (cA σ) = (1 - _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u)ᵀ := by
    calc a'.map (cA σ) = ((1 - _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u)ᵀ * (1 + _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u)ᵀ) * a'.map (cA σ) := by rw [h2, Matrix.one_mul]
      _ = (1 - _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u)ᵀ * ((1 + _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u)ᵀ * a'.map (cA σ)) := by rw [Matrix.mul_assoc]
      _ = (1 - _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u)ᵀ := by rw [h1, Matrix.mul_one]
  have h4 : a' = ((1 - _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u)ᵀ).map (cA σ) := by rw [← h3, _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.cA_cA_mat_k d]
  rw [h4]
theorem uM_add_k {uM ν 𝓤} (hu : L.UData uM ν 𝓤) (u v : Fin L.n → AE F E) : uM (u + v) = uM u * uM v := by
  apply kfour.inFrame_injective d.b
  rw [SiegelEisensteinSeries.Grp.inFrame_mul, _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.uM_frame_k L hu, _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.uM_frame_k L hu, _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.uM_frame_k L hu, Matrix.fromBlocks_multiply]
  have e1 : (1 + _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u) * (1 + _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L v) = 1 + _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L (u + v) := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_add_k, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_mul_k, add_zero]
    abel
  have e2 : ((1 - _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u)ᵀ).map (cA σ) * ((1 - _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L v)ᵀ).map (cA σ) = ((1 - _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L (u + v))ᵀ).map (cA σ) := by
    have hm := Matrix.map_mul (L := (1 - _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u)ᵀ) (M := (1 - _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L v)ᵀ) (f := (cA σ).toRingHom)
    erw [← hm]
    rw [← Matrix.transpose_mul, _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_add_k, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_mul_k,
      sub_zero]
    congr 2
    abel
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, e1, e2]
theorem uM_zero_k {uM ν 𝓤} (hu : L.UData uM ν 𝓤) : uM 0 = 1 := by
  have h := _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.uM_add_k L hu 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)
theorem uM_neg_k {uM ν 𝓤} (hu : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) : (uM u)⁻¹ = uM (-u) := by
  have h := _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.uM_add_k L hu (-u) u
  rw [neg_add_cancel, _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.uM_zero_k L hu] at h
  exact (eq_inv_of_mul_eq_one_left h.symm).symm
theorem uM_cont_k {uM ν 𝓤} (hu : L.UData uM ν 𝓤) : Continuous uM := by
  have hcA : Continuous (cA σ : AE F E → AE F E) :=
    IsModuleTopology.continuous_of_linearMap (R := AF F) (cA σ).toLinearMap
  have hmat : Continuous fun u => mat2 (uM u) := by
    have e : (fun u => mat2 (uM u)) = fun u => incM F d.b.1 * Matrix.fromBlocks (1 + _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u) 0 0
        (((1 - _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_k L u)ᵀ).map (cA σ)) * incM F (d.b⁻¹).1 := by
      funext u; rw [SiegelEisensteinSeries.Grp.matrix_eq_frame_conjugate d.b, _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.uM_frame_k L hu]
    rw [e]
    refine (continuous_const.matrix_mul (Continuous.matrix_fromBlocks (continuous_const.add (_root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_cont_k L))
      continuous_const continuous_const ?_)).matrix_mul continuous_const
    exact ((continuous_const.sub (_root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.Nu_cont_k L)).matrix_transpose).matrix_map hcA
  have hinv : Continuous fun u => mat2 (uM u)⁻¹ := by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.uM_neg_k L hu]
    exact hmat.comp continuous_neg
  refine Topology.IsInducing.subtypeVal.continuous_iff.2 ?_
  exact Units.continuous_iff.2 ⟨hmat, hinv⟩
theorem ratV_cocompact_k : ∃ K : Set (Fin L.n → AE F E), IsCompact K ∧ ∀ u, ∃ r ∈ L.ratV, r + u ∈ K := by
  obtain ⟨C, hC, hCx⟩ := kfour.exists_compact_AE (F := F) (E := E)
  refine ⟨Set.univ.pi (fun _ => C), isCompact_univ_pi (fun _ => hC), fun u => ?_⟩
  choose x hx using fun j => hCx (u j)
  refine ⟨GlobalTheory.ThK.incV F x, AddSubgroup.subset_closure ⟨x, rfl⟩, fun j _ => ?_⟩
  simpa [GlobalTheory.ThK.incV] using hx j
end COneB
end PositivityTheory.SiegelWeilFormula.AStep
end
end
