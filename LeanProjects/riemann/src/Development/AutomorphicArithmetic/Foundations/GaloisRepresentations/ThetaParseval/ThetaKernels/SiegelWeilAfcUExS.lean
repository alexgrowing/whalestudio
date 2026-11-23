import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.ProjectedBlockUpperSum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdPlace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourNA
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdRDIota

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Afc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section Alg
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
def uN_k (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) := ∑ j, Matrix.single L.i₀ (L.em j) (u j)
theorem em_ne_k (j : Fin L.n) : L.em j ≠ L.i₀ := (L.rng (L.em j)).2 ⟨j, rfl⟩
theorem uN_mul_k (u v : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k L u * _root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k L v = 0 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => by simp [_root_.PositivityTheory.SiegelWeilFormula.Afc.em_ne_k L]
theorem uN_add_k (u v : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k L (u + v) = _root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k L u + _root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k L v := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k, Pi.add_apply, Matrix.single_add, Finset.sum_add_distrib]
theorem uN_zero_k : _root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k L 0 = 0 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k]
def uD_k (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) := 1 - ((_root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k L u).map (cA σ))ᵀ
def uZ_k (u : Fin L.n → AE F E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks (1 + _root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k L u) 0 0 (_root_.PositivityTheory.SiegelWeilFormula.Afc.uD_k L u)
theorem uZ_mul_k (u v : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Afc.uZ_k L u * _root_.PositivityTheory.SiegelWeilFormula.Afc.uZ_k L v = _root_.PositivityTheory.SiegelWeilFormula.Afc.uZ_k L (u + v) := by
  have h1 : (1 + _root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k L u) * (1 + _root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k L v) = 1 + _root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k L (u + v) := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.uN_add_k, add_mul, mul_add, mul_add, _root_.PositivityTheory.SiegelWeilFormula.Afc.uN_mul_k]
    simp only [one_mul, mul_one, add_zero]
    abel
  have h2 : _root_.PositivityTheory.SiegelWeilFormula.Afc.uD_k (σ := σ) L u * _root_.PositivityTheory.SiegelWeilFormula.Afc.uD_k L v = _root_.PositivityTheory.SiegelWeilFormula.Afc.uD_k L (u + v) := by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Afc.uD_k, _root_.PositivityTheory.SiegelWeilFormula.Afc.uN_add_k, mapc_add, Matrix.transpose_add]
    have : ((_root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k L u).map (cA σ))ᵀ * ((_root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k L v).map (cA σ))ᵀ = 0 := by
      rw [← Matrix.transpose_mul, ← mapc_mulU, _root_.PositivityTheory.SiegelWeilFormula.Afc.uN_mul_k, Matrix.map_zero _ (map_zero _), Matrix.transpose_zero]
    rw [sub_mul, mul_sub, mul_sub, this]
    simp only [one_mul, mul_one, sub_zero]
    abel
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Afc.uZ_k, Matrix.fromBlocks_multiply, h1, h2, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
theorem uZ_zero_k : _root_.PositivityTheory.SiegelWeilFormula.Afc.uZ_k (σ := σ) L 0 = 1 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Afc.uZ_k, _root_.PositivityTheory.SiegelWeilFormula.Afc.uD_k, _root_.PositivityTheory.SiegelWeilFormula.Afc.uN_zero_k, Matrix.fromBlocks_one]
def Qa_k (ε : ℤˣ) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks 0 1 (inclR (F := F) (E := E) (AF F) ((ε : ℤ) : E) • 1) 0
theorem uZ_unitary_k (ε : ℤˣ) (u : Fin L.n → AE F E) : (_root_.PositivityTheory.SiegelWeilFormula.Afc.uZ_k L u)ᵀ * _root_.PositivityTheory.SiegelWeilFormula.Afc.Qa_k (d := d) ε * (_root_.PositivityTheory.SiegelWeilFormula.Afc.uZ_k L u).map (cA σ) = _root_.PositivityTheory.SiegelWeilFormula.Afc.Qa_k ε := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  have hcc := GlobalTheory.EisBL.DoubledUnipotentRadical.cA_cA σ hσ
  have hD : (_root_.PositivityTheory.SiegelWeilFormula.Afc.uD_k (σ := σ) L u).map (cA σ) = 1 - (_root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k L u)ᵀ := by
    ext i j
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Afc.uD_k, Matrix.map_apply, Matrix.sub_apply, Matrix.transpose_apply, map_sub, hcc, Matrix.one_apply]
    split_ifs <;> simp
  have k1 : (1 + _root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k L u)ᵀ * (1 - (_root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k L u)ᵀ) = 1 := by
    rw [Matrix.transpose_add, Matrix.transpose_one, add_mul, one_mul, mul_sub, mul_one,
      ← Matrix.transpose_mul, _root_.PositivityTheory.SiegelWeilFormula.Afc.uN_mul_k, Matrix.transpose_zero, sub_zero]
    abel
  have k2 : (_root_.PositivityTheory.SiegelWeilFormula.Afc.uD_k (σ := σ) L u)ᵀ * (1 + _root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k L u).map (cA σ) = 1 := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.uD_k, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_transpose, mapc_add, mapc_one, sub_mul,
      one_mul, mul_add, mul_one, ← mapc_mulU, _root_.PositivityTheory.SiegelWeilFormula.Afc.uN_mul_k, Matrix.map_zero _ (map_zero _), add_zero]
    abel
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Afc.uZ_k, _root_.PositivityTheory.SiegelWeilFormula.Afc.Qa_k, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_map, hD,
    Matrix.transpose_zero, Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, k1]
  congr 1
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, k2]
end Alg
section Pts
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
theorem conj_mem_k {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (Z : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (hZ : Zᵀ * _root_.PositivityTheory.SiegelWeilFormula.Afc.Qa_k (d := d) ε * Z.map (cA σ) = _root_.PositivityTheory.SiegelWeilFormula.Afc.Qa_k ε) :
    (incM F d.b.1 * Z * incM F (d.b⁻¹).1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1 * Z * incM F (d.b⁻¹).1).map (cA σ) =
      dbl (incM F d.Y.J) := by
  have hF := SiegelEisensteinSeries.Grp.frame_adelic (F := F) hε
  have hZ' : Zᵀ * Matrix.fromBlocks 0 1 (inclR (F := F) (E := E) (AF F) ((ε : ℤ) : E) • 1) 0 * Z.map (cA σ) =
      Matrix.fromBlocks 0 1 (inclR (F := F) (E := E) (AF F) ((ε : ℤ) : E) • 1) 0 := hZ
  have h1 : (incM F (d.b⁻¹).1)ᵀ * (incM F d.b.1)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, SiegelEisensteinSeries.Grp.incM_mul_inv, Matrix.transpose_one]
  have h2 : (incM F d.b.1).map (cA σ) * (incM F (d.b⁻¹).1).map (cA σ) = 1 := by
    rw [← SiegelEisensteinSeries.Grp.map_cA_mul, SiegelEisensteinSeries.Grp.incM_mul_inv, mapc_one]
  rw [SiegelEisensteinSeries.Grp.map_cA_mul, SiegelEisensteinSeries.Grp.map_cA_mul, Matrix.transpose_mul, Matrix.transpose_mul]
  calc (incM F (d.b⁻¹).1)ᵀ * (Zᵀ * (incM F d.b.1)ᵀ) * dbl (incM F d.Y.J) *
        ((incM F d.b.1).map (cA σ) * Z.map (cA σ) * (incM F (d.b⁻¹).1).map (cA σ))
      = (incM F (d.b⁻¹).1)ᵀ * (Zᵀ * ((incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ)) *
          Z.map (cA σ)) * (incM F (d.b⁻¹).1).map (cA σ) := by simp only [Matrix.mul_assoc]
    _ = (incM F (d.b⁻¹).1)ᵀ * ((incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ)) *
          (incM F (d.b⁻¹).1).map (cA σ) := by rw [hF, hZ']
    _ = ((incM F (d.b⁻¹).1)ᵀ * (incM F d.b.1)ᵀ) * dbl (incM F d.Y.J) *
          ((incM F d.b.1).map (cA σ) * (incM F (d.b⁻¹).1).map (cA σ)) := by simp only [Matrix.mul_assoc]
    _ = dbl (incM F d.Y.J) := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
theorem unitary_of_mem_k {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (x : d.G) : (inFrame d.b x)ᵀ * _root_.PositivityTheory.SiegelWeilFormula.Afc.Qa_k (d := d) ε * (inFrame d.b x).map (cA σ) = _root_.PositivityTheory.SiegelWeilFormula.Afc.Qa_k ε := by
  have hF := SiegelEisensteinSeries.Grp.frame_adelic (F := F) hε
  have hU : (mat2 x)ᵀ * dbl (incM F d.Y.J) * (mat2 x).map (cA σ) = dbl (incM F d.Y.J) := x.2
  rw [SiegelEisensteinSeries.Grp.matrix_eq_frame_conjugate d.b x] at hU
  have h1 : (incM F d.b.1)ᵀ * (incM F (d.b⁻¹).1)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, SiegelEisensteinSeries.Grp.incM_inv_mul, Matrix.transpose_one]
  have h2 : (incM F (d.b⁻¹).1).map (cA σ) * (incM F d.b.1).map (cA σ) = 1 := by
    rw [← SiegelEisensteinSeries.Grp.map_cA_mul, SiegelEisensteinSeries.Grp.incM_inv_mul, mapc_one]
  unfold _root_.PositivityTheory.SiegelWeilFormula.Afc.Qa_k
  rw [← hF]
  conv_rhs => rw [← hU]
  rw [SiegelEisensteinSeries.Grp.map_cA_mul, SiegelEisensteinSeries.Grp.map_cA_mul, Matrix.transpose_mul, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [h2, Matrix.mul_one, ← Matrix.mul_assoc (incM F d.b.1)ᵀ (incM F (d.b⁻¹).1)ᵀ, h1, Matrix.one_mul]
def uU_k (u : Fin L.n → AE F E) : GL (Fin d.n ⊕ Fin d.n) (AE F E) where
  val := incM F d.b.1 * _root_.PositivityTheory.SiegelWeilFormula.Afc.uZ_k L u * incM F (d.b⁻¹).1
  inv := incM F d.b.1 * _root_.PositivityTheory.SiegelWeilFormula.Afc.uZ_k L (-u) * incM F (d.b⁻¹).1
  val_inv := (SiegelEisensteinSeries.Grp.conj_mul_conj d.b _ _).trans (by
    rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.uZ_mul_k, add_neg_cancel, _root_.PositivityTheory.SiegelWeilFormula.Afc.uZ_zero_k, Matrix.mul_one, SiegelEisensteinSeries.Grp.incM_mul_inv])
  inv_val := (SiegelEisensteinSeries.Grp.conj_mul_conj d.b _ _).trans (by
    rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.uZ_mul_k, neg_add_cancel, _root_.PositivityTheory.SiegelWeilFormula.Afc.uZ_zero_k, Matrix.mul_one, SiegelEisensteinSeries.Grp.incM_mul_inv])
theorem uU_mem_k (u : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Afc.uU_k L u ∈ UG (cA σ) (dbl (incM F d.Y.J)) := by
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  exact _root_.PositivityTheory.SiegelWeilFormula.Afc.conj_mem_k hε _ (_root_.PositivityTheory.SiegelWeilFormula.Afc.uZ_unitary_k L ε u)
def unipotentOfVector (u : Fin L.n → AE F E) : d.G := ⟨_root_.PositivityTheory.SiegelWeilFormula.Afc.uU_k L u, _root_.PositivityTheory.SiegelWeilFormula.Afc.uU_mem_k L u⟩
theorem inFrame_unipotentOfVector (u : Fin L.n → AE F E) : inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Afc.unipotentOfVector L u) = _root_.PositivityTheory.SiegelWeilFormula.Afc.uZ_k L u := by
  show incM F (d.b⁻¹).1 * (incM F d.b.1 * _root_.PositivityTheory.SiegelWeilFormula.Afc.uZ_k L u * incM F (d.b⁻¹).1) * incM F d.b.1 = _root_.PositivityTheory.SiegelWeilFormula.Afc.uZ_k L u
  simp only [Matrix.mul_assoc]
  rw [SiegelEisensteinSeries.Grp.incM_inv_mul, Matrix.mul_one, ← Matrix.mul_assoc, SiegelEisensteinSeries.Grp.incM_inv_mul, Matrix.one_mul]
theorem unipotentOfVector_add (u v : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Afc.unipotentOfVector L (u + v) = _root_.PositivityTheory.SiegelWeilFormula.Afc.unipotentOfVector L u * _root_.PositivityTheory.SiegelWeilFormula.Afc.unipotentOfVector L v := by
  refine kfour.inFrame_injective d.b ?_
  rw [SiegelEisensteinSeries.Grp.inFrame_mul, _root_.PositivityTheory.SiegelWeilFormula.Afc.inFrame_unipotentOfVector, _root_.PositivityTheory.SiegelWeilFormula.Afc.inFrame_unipotentOfVector, _root_.PositivityTheory.SiegelWeilFormula.Afc.inFrame_unipotentOfVector, _root_.PositivityTheory.SiegelWeilFormula.Afc.uZ_mul_k]
theorem unipotentOfVector_zero : _root_.PositivityTheory.SiegelWeilFormula.Afc.unipotentOfVector L 0 = 1 := by
  refine kfour.inFrame_injective d.b ?_
  rw [SiegelEisensteinSeries.Grp.inFrame_one, _root_.PositivityTheory.SiegelWeilFormula.Afc.inFrame_unipotentOfVector, _root_.PositivityTheory.SiegelWeilFormula.Afc.uZ_zero_k]
theorem uN_eq_sum_k (u : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k L u = ∑ j, u j • Matrix.single L.i₀ (L.em j) (1 : AE F E) := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k, Matrix.smul_single, smul_eq_mul, mul_one]
theorem continuous_uN_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k L) := by
  rw [show _root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k L = fun u => ∑ j, u j • Matrix.single L.i₀ (L.em j) (1 : AE F E) from funext (_root_.PositivityTheory.SiegelWeilFormula.Afc.uN_eq_sum_k L)]
  exact continuous_finsetSum _ fun j _ => (continuous_apply j).smul continuous_const
theorem continuous_uZ_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Afc.uZ_k (σ := σ) L) := by
  have hD : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Afc.uD_k (σ := σ) L) :=
    continuous_const.sub (((_root_.PositivityTheory.SiegelWeilFormula.Afc.continuous_uN_k L).matrix_map (GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ)).matrix_transpose)
  exact (continuous_const.add (_root_.PositivityTheory.SiegelWeilFormula.Afc.continuous_uN_k L)).matrix_fromBlocks continuous_const continuous_const hD
theorem continuous_unipotentOfVector : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Afc.unipotentOfVector (σ := σ) L) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact (continuous_const.matrix_mul (_root_.PositivityTheory.SiegelWeilFormula.Afc.continuous_uZ_k L)).matrix_mul continuous_const
  · exact (continuous_const.matrix_mul ((_root_.PositivityTheory.SiegelWeilFormula.Afc.continuous_uZ_k L).comp continuous_neg)).matrix_mul continuous_const
theorem blockDiagonal_preserves_form_iff {ε : ℤˣ} (A D : Matrix (Fin d.n) (Fin d.n) (AE F E))
    (h : (Matrix.fromBlocks A 0 0 D)ᵀ * _root_.PositivityTheory.SiegelWeilFormula.Afc.Qa_k (d := d) ε * (Matrix.fromBlocks A 0 0 D).map (cA σ) = _root_.PositivityTheory.SiegelWeilFormula.Afc.Qa_k ε) :
    Aᵀ * D.map (cA σ) = 1 := by
  have h' := congrArg Matrix.toBlocks₁₂ h
  simpa [_root_.PositivityTheory.SiegelWeilFormula.Afc.Qa_k, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_map,
    Matrix.map_zero _ (map_zero _)] using h'
theorem uM_eq_k {uM : (Fin L.n → AE F E) → d.G} {ν 𝓤} (h : L.UData uM ν 𝓤) : uM = _root_.PositivityTheory.SiegelWeilFormula.Afc.unipotentOfVector L := by
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  have hcc := GlobalTheory.EisBL.DoubledUnipotentRadical.cA_cA σ hσ
  funext u
  obtain ⟨a', ha'⟩ := h.1 u
  refine kfour.inFrame_injective d.b ?_
  rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.inFrame_unipotentOfVector, ha']
  have e1 := _root_.PositivityTheory.SiegelWeilFormula.Afc.blockDiagonal_preserves_form_iff _ _ (ha' ▸ _root_.PositivityTheory.SiegelWeilFormula.Afc.unitary_of_mem_k hε (uM u))
  have e2 := _root_.PositivityTheory.SiegelWeilFormula.Afc.blockDiagonal_preserves_form_iff _ _ (_root_.PositivityTheory.SiegelWeilFormula.Afc.uZ_unitary_k L ε u)
  have e3 : a'.map (cA σ) = (_root_.PositivityTheory.SiegelWeilFormula.Afc.uD_k L u).map (cA σ) := by
    have e1' : a'.map (cA σ) * (1 + _root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k L u)ᵀ = 1 := mul_eq_one_comm.1 e1
    calc a'.map (cA σ) = a'.map (cA σ) * ((1 + _root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k L u)ᵀ * (_root_.PositivityTheory.SiegelWeilFormula.Afc.uD_k L u).map (cA σ)) := by rw [e2, Matrix.mul_one]
      _ = (_root_.PositivityTheory.SiegelWeilFormula.Afc.uD_k L u).map (cA σ) := by rw [← Matrix.mul_assoc, e1', Matrix.one_mul]
  have e4 : a' = _root_.PositivityTheory.SiegelWeilFormula.Afc.uD_k L u := by
    ext i j
    have := congrArg (cA σ) (congrFun (congrFun e3 i) j)
    simpa [hcc] using this
  rw [e4]
  rfl
end Pts
section Meas
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
theorem mem_ratV_k (v : Fin L.n → AE F E) : v ∈ L.ratV ↔ ∃ e, GlobalTheory.ThK.incV F e = v := by
  constructor
  · intro h
    induction h using AddSubgroup.closure_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, funext fun i => by rw [incV_apply]; simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨X, rfl⟩ := hx
      obtain ⟨Z, rfl⟩ := hy
      exact ⟨X + Z, funext fun i => by simp [incV_apply, map_add]⟩
    | neg x _ hx =>
      obtain ⟨X, rfl⟩ := hx
      exact ⟨-X, funext fun i => by simp [incV_apply, map_neg]⟩
  · rintro ⟨X, rfl⟩
    exact AddSubgroup.subset_closure ⟨X, rfl⟩
theorem ratV_discrete_k : DiscreteTopology L.ratV := by
  obtain ⟨V, hV, hV0⟩ := kfour.exists_nhds_inclR (F := F) (E := E)
  have hW : (⋂ i, (fun M : Fin L.n → AE F E => M i) ⁻¹' V) ∈ 𝓝 (0 : Fin L.n → AE F E) := by
    refine Filter.iInter_mem.2 fun i => ?_
    exact (continuous_apply i).continuousAt.preimage_mem_nhds (by simpa using hV)
  obtain ⟨O, hOW, hO, h0⟩ := mem_nhds_iff.1 hW
  refine discreteTopology_of_isOpen_singleton_zero ?_
  convert hO.preimage (continuous_subtype_val (p := fun x => x ∈ L.ratV)) using 1
  ext ⟨x, hx⟩
  constructor
  · intro h
    have h1 : x = 0 := congrArg Subtype.val (Set.mem_singleton_iff.1 h)
    subst h1
    exact h0
  · intro h
    obtain ⟨X, rfl⟩ := (_root_.PositivityTheory.SiegelWeilFormula.Afc.mem_ratV_k L _).1 hx
    have h2 : X = 0 := by
      funext i
      exact hV0 _ (Set.mem_iInter.1 (hOW h) i)
    subst h2
    exact Set.mem_singleton_iff.2 (Subtype.ext (funext fun i => show inclR (F := F) (AF F) ((0 : Fin L.n → E) i) = 0 by simp))
theorem ratV_cocompact_k : ∃ K : Set (Fin L.n → AE F E), IsCompact K ∧ ∀ x, ∃ γ ∈ L.ratV, γ + x ∈ K := by
  obtain ⟨C, hC, hCx⟩ := kfour.exists_compact_AE (F := F) (E := E)
  refine ⟨Set.univ.pi fun _ => C, isCompact_univ_pi fun _ => hC, fun x => ?_⟩
  choose e he using fun i => hCx (x i)
  exact ⟨GlobalTheory.ThK.incV F e, (_root_.PositivityTheory.SiegelWeilFormula.Afc.mem_ratV_k L _).2 ⟨e, rfl⟩, fun i _ => he i⟩
theorem exists_udata_k : ∃ uM ν 𝓤, L.UData uM ν 𝓤 := by
  haveI := _root_.PositivityTheory.SiegelWeilFormula.Afc.ratV_discrete_k L
  obtain ⟨K, hK, hc⟩ := _root_.PositivityTheory.SiegelWeilFormula.Afc.ratV_cocompact_k L
  obtain ⟨ν, 𝓤, hν, h𝓤, h1⟩ :=
    (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (Fin L.n → AE F E) L.ratV K hK hc).1
  exact ⟨_root_.PositivityTheory.SiegelWeilFormula.Afc.unipotentOfVector L, ν, 𝓤, fun u => ⟨_root_.PositivityTheory.SiegelWeilFormula.Afc.uD_k L u, _root_.PositivityTheory.SiegelWeilFormula.Afc.inFrame_unipotentOfVector L u⟩, hν, h𝓤, h1⟩
end Meas
section Dens
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
def Sw_k (w : InfinitePlace F) : Set (AE F E) := {z | (∀ w', w' ≠ w → piInf (d.B.emb w') z = 0) ∧ finOne F • z = 0}
theorem sum_mem_Sw_k (w : InfinitePlace F) (s : Fin (Module.finrank F E) → AF F) (hs : ∀ k, (s k).2 = 0 ∧ ∀ w', w' ≠ w → (s k).1 w' = 0) :
    ∑ k, s k • kfour.bsA F E k ∈ _root_.PositivityTheory.SiegelWeilFormula.Afc.Sw_k d w := by
  refine ⟨fun w' hw' => ?_, ?_⟩
  · rw [map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [St.piInf_smul, (hs k).2 w' hw', map_zero, zero_mul]
  · rw [Finset.smul_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [smul_smul, finOne_mul (hs k).1, zero_smul]
theorem dense_Sw_k (w : InfinitePlace F) : Dense {z : AE F E | ∃ e : E, ∃ s ∈ _root_.PositivityTheory.SiegelWeilFormula.Afc.Sw_k d w, inclR (F := F) (AF F) e + s = z} := by
  have hA := GlobalTheory.T.dense_rationals_plus_single_place_adeles F w
  let Φ : (Fin (Module.finrank F E) → AF F) → AE F E := fun a => ∑ k, a k • kfour.bsA F E k
  have hΦc : Continuous Φ := continuous_finsetSum _ fun k _ => (continuous_apply k).smul continuous_const
  have hΦs : Function.Surjective Φ := fun z => ⟨fun k => (kfour.bsA F E).repr z k, (kfour.bsA F E).sum_repr z⟩
  have hd : Dense (Set.univ.pi fun _ : Fin (Module.finrank F E) =>
      (Set.range (algebraMap F (AF F)) + {a : AF F | a.2 = 0 ∧ ∀ w', w' ≠ w → a.1 w' = 0})) :=
    dense_pi _ fun k _ => hA
  refine (hΦs.denseRange.dense_image hΦc hd).mono ?_
  rintro _ ⟨a, ha, rfl⟩
  choose x hx s hs hxs using fun k => Set.mem_add.1 (ha k (Set.mem_univ k))
  choose q hq using hx
  refine ⟨∑ k, q k • kfour.bsE F E k, ∑ k, s k • kfour.bsA F E k, _root_.PositivityTheory.SiegelWeilFormula.Afc.sum_mem_Sw_k d w s hs, ?_⟩
  have h1 : inclR (F := F) (AF F) (∑ k, q k • kfour.bsE F E k) = ∑ k, algebraMap F (AF F) (q k) • kfour.bsA F E k := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.TensorProduct.basis_apply, algebraMap_smul, kfour.inclR_eq, TensorProduct.tmul_smul]
  rw [h1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← add_smul, hq, hxs]
theorem dense_vec_k (k : ℕ) (w : InfinitePlace F) :
    Dense {v : Fin k → AE F E | ∃ e : Fin k → E, ∃ s : Fin k → AE F E, (∀ j, s j ∈ _root_.PositivityTheory.SiegelWeilFormula.Afc.Sw_k d w) ∧ GlobalTheory.ThK.incV F e + s = v} := by
  refine (dense_pi Set.univ fun j _ => _root_.PositivityTheory.SiegelWeilFormula.Afc.dense_Sw_k d w).mono ?_
  intro v hv
  choose e s hs hes using fun j => hv j (Set.mem_univ j)
  exact ⟨e, s, hs, funext fun j => hes j⟩
end Dens
section Real
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
theorem cw_uN_k (w' : InfinitePlace F) (u : Fin L.n → AE F E) :
    d.cw w' (_root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k L u) = ∑ j, Matrix.single L.i₀ (L.em j) (piInf (d.B.emb w') (u j)) := by
  ext a b
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, _root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k, Matrix.map_apply, Matrix.sum_apply, map_sum, Matrix.single_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp
theorem fin_uN_k (u : Fin L.n → AE F E) : finOne F • _root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k L u = ∑ j, Matrix.single L.i₀ (L.em j) (finOne F • u j) := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k, Finset.smul_sum, Matrix.smul_single]
theorem cw_uZ_k (w' : InfinitePlace F) (u : Fin L.n → AE F E) :
    d.cw w' (_root_.PositivityTheory.SiegelWeilFormula.Afc.uZ_k L u) = Matrix.fromBlocks (1 + d.cw w' (_root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k L u)) 0 0 (1 - ((d.cw w' (_root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k L u)).map star)ᵀ) := by
  have e1 : d.cw w' (1 + _root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k L u) = 1 + d.cw w' (_root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k L u) := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
  have e2 : d.cw w' (_root_.PositivityTheory.SiegelWeilFormula.Afc.uD_k L u) = 1 - ((d.cw w' (_root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k L u)).map star)ᵀ := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, _root_.PositivityTheory.SiegelWeilFormula.Afc.uD_k, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), ← Matrix.transpose_map,
      Place.map_cA d.cm]
    rfl
  rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.uZ_k, ← e1, ← e2]
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _)]
theorem fin_uZ_k (u : Fin L.n → AE F E) :
    finOne F • _root_.PositivityTheory.SiegelWeilFormula.Afc.uZ_k L u = Matrix.fromBlocks (finOne F • 1 + finOne F • _root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k L u) 0 0
      (finOne F • 1 - ((finOne F • _root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k L u).map (cA σ))ᵀ) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.uZ_k, _root_.PositivityTheory.SiegelWeilFormula.Afc.uD_k, Matrix.fromBlocks_smul, smul_zero, smul_add, smul_sub, Krd.map_cA_smul, Matrix.transpose_smul]
end Real
theorem exists_iota_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (w : InfinitePlace F) (u : Fin L.n → AE F E) (hu : ∀ j, u j ∈ _root_.PositivityTheory.SiegelWeilFormula.Afc.Sw_k d w) :
    ∃ y, _root_.PositivityTheory.SiegelWeilFormula.Afc.unipotentOfVector L u = R.ι w y := by
  have h0 := Krd.zeta_ne R.hζ
  set Z := d.cw w (_root_.PositivityTheory.SiegelWeilFormula.Afc.uZ_k L u) with hZdef
  set Z' := d.cw w (_root_.PositivityTheory.SiegelWeilFormula.Afc.uZ_k L (-u)) with hZ'def
  have hZZ : Z * Z' = 1 := by rw [hZdef, hZ'def, ← _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Afc.uZ_mul_k, add_neg_cancel, _root_.PositivityTheory.SiegelWeilFormula.Afc.uZ_zero_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_one_k]
  have hZZ' : Z' * Z = 1 := by rw [hZdef, hZ'def, ← _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Afc.uZ_mul_k, neg_add_cancel, _root_.PositivityTheory.SiegelWeilFormula.Afc.uZ_zero_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_one_k]
  have hq : d.cw w (_root_.PositivityTheory.SiegelWeilFormula.Afc.Qa_k (d := d) R.ε) = Krd.Qc d.n R.ε := by
    ext (i | i) (j | j) <;> simp [_root_.PositivityTheory.SiegelWeilFormula.Afc.Qa_k, Krd.Qc, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.one_apply] <;> split_ifs <;> simp
  have hQ : Zᵀ * Krd.Qc d.n R.ε * Z.map star = Krd.Qc d.n R.ε := by
    have h := congrArg (d.cw w) (_root_.PositivityTheory.SiegelWeilFormula.Afc.uZ_unitary_k L R.ε u)
    rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_transpose_k, _root_.PositivityTheory.SiegelWeilFormula.Place.cw_cA_k, hq] at h
    exact h
  let y : GR d.n := ⟨⟨dZ d.n R.ζ * Z * dZ d.n R.ζ⁻¹, dZ d.n R.ζ * Z' * dZ d.n R.ζ⁻¹, by
      rw [show dZ d.n R.ζ * Z * dZ d.n R.ζ⁻¹ * (dZ d.n R.ζ * Z' * dZ d.n R.ζ⁻¹) =
        dZ d.n R.ζ * Z * (dZ d.n R.ζ⁻¹ * dZ d.n R.ζ) * Z' * dZ d.n R.ζ⁻¹ by simp only [Matrix.mul_assoc],
        Krd.dZ_inv_mul h0, Matrix.mul_one, Matrix.mul_assoc (dZ d.n R.ζ), hZZ, Matrix.mul_one, Krd.dZ_mul_inv h0], by
      rw [show dZ d.n R.ζ * Z' * dZ d.n R.ζ⁻¹ * (dZ d.n R.ζ * Z * dZ d.n R.ζ⁻¹) =
        dZ d.n R.ζ * Z' * (dZ d.n R.ζ⁻¹ * dZ d.n R.ζ) * Z * dZ d.n R.ζ⁻¹ by simp only [Matrix.mul_assoc],
        Krd.dZ_inv_mul h0, Matrix.mul_one, Matrix.mul_assoc (dZ d.n R.ζ), hZZ', Matrix.mul_one, Krd.dZ_mul_inv h0]⟩,
    Krd.inG_conj R.hζ Z hQ⟩
  refine ⟨y, kfour.inFrame_injective d.b ?_⟩
  rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.inFrame_unipotentOfVector]
  refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w' => ?_) ?_
  · by_cases hw' : w' = w
    · subst hw'
      have h1 := R.at_w w' y
      have h2 : dZ d.n R.ζ * d.cw w' (inFrame d.b (R.ι w' y)) = dZ d.n R.ζ * Z := by
        rw [h1]
        show dZ d.n R.ζ * Z * dZ d.n R.ζ⁻¹ * dZ d.n R.ζ = dZ d.n R.ζ * Z
        rw [Matrix.mul_assoc, Krd.dZ_inv_mul h0, Matrix.mul_one]
      have h3 := congrArg (fun M => dZ d.n R.ζ⁻¹ * M) h2
      simp only [← Matrix.mul_assoc, Krd.dZ_inv_mul h0, Matrix.one_mul] at h3
      exact h3.symm
    · have hN : d.cw w' (_root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k L u) = 0 := by
        rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.cw_uN_k]
        exact Finset.sum_eq_zero fun j _ => by rw [(hu j).1 w' hw', Matrix.single_zero]
      rw [R.off_w w w' y hw', _root_.PositivityTheory.SiegelWeilFormula.Afc.cw_uZ_k, hN]
      simp [Matrix.fromBlocks_one]
  · have hN : finOne F • _root_.PositivityTheory.SiegelWeilFormula.Afc.uN_k L u = 0 := by
      rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.fin_uN_k]
      exact Finset.sum_eq_zero fun j _ => by rw [(hu j).2, Matrix.single_zero]
    rw [R.off_f w y, _root_.PositivityTheory.SiegelWeilFormula.Afc.fin_uZ_k, hN]
    simp only [Matrix.map_zero _ (map_zero _), Matrix.transpose_zero, sub_zero, add_zero]
    conv_rhs => rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero]
theorem uEx_k : _root_.PositivityTheory.SiegelWeilFormula.UEx_k := by
  intro F E _ _ _ _ _ σ d R L
  refine ⟨_root_.PositivityTheory.SiegelWeilFormula.Afc.exists_udata_k L, ?_⟩
  intro uM ν 𝓤 hU w φ hφ hrat hw u x
  have he := _root_.PositivityTheory.SiegelWeilFormula.Afc.uM_eq_k L hU
  subst he
  haveI := (kfour.doubled_group_topological_properties σ d.Y).1
  let S : AddSubgroup (Fin L.n → AE F E) :=
    { carrier := {u | ∀ x, φ (_root_.PositivityTheory.SiegelWeilFormula.Afc.unipotentOfVector L u * x) = φ x}
      add_mem' := fun {a b} ha hb x => by
        show φ (_root_.PositivityTheory.SiegelWeilFormula.Afc.unipotentOfVector L (a + b) * x) = φ x
        rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.unipotentOfVector_add, mul_assoc, ha, hb]
      zero_mem' := fun x => by
        show φ (_root_.PositivityTheory.SiegelWeilFormula.Afc.unipotentOfVector L 0 * x) = φ x
        rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.unipotentOfVector_zero, one_mul]
      neg_mem' := fun {a} ha x => by
        show φ (_root_.PositivityTheory.SiegelWeilFormula.Afc.unipotentOfVector L (-a) * x) = φ x
        have := ha (_root_.PositivityTheory.SiegelWeilFormula.Afc.unipotentOfVector L (-a) * x)
        rw [← mul_assoc, ← _root_.PositivityTheory.SiegelWeilFormula.Afc.unipotentOfVector_add, add_neg_cancel, _root_.PositivityTheory.SiegelWeilFormula.Afc.unipotentOfVector_zero, one_mul] at this
        exact this.symm }
  have hS : IsClosed (S : Set (Fin L.n → AE F E)) := by
    have : (S : Set (Fin L.n → AE F E)) = ⋂ x, {u | φ (_root_.PositivityTheory.SiegelWeilFormula.Afc.unipotentOfVector L u * x) = φ x} := by
      ext u
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      rfl
    rw [this]
    exact isClosed_iInter fun x => isClosed_eq (hφ.comp ((_root_.PositivityTheory.SiegelWeilFormula.Afc.continuous_unipotentOfVector L).mul continuous_const)) continuous_const
  have hT : {v : Fin L.n → AE F E | ∃ e : Fin L.n → E, ∃ s : Fin L.n → AE F E, (∀ j, s j ∈ _root_.PositivityTheory.SiegelWeilFormula.Afc.Sw_k d w) ∧
      GlobalTheory.ThK.incV F e + s = v} ⊆ S := by
    rintro _ ⟨e, s, hs, rfl⟩
    refine S.add_mem (fun x => hrat _ ((_root_.PositivityTheory.SiegelWeilFormula.Afc.mem_ratV_k L _).2 ⟨e, rfl⟩) x) ?_
    obtain ⟨y, hy⟩ := _root_.PositivityTheory.SiegelWeilFormula.Afc.exists_iota_k R L w s hs
    exact fun x => hw s y hy x
  have hu : u ∈ S := by
    have h1 := closure_minimal hT hS
    rw [(_root_.PositivityTheory.SiegelWeilFormula.Afc.dense_vec_k d L.n w).closure_eq] at h1
    exact h1 (Set.mem_univ u)
  exact hu x
end PositivityTheory.SiegelWeilFormula.Afc
end
end
