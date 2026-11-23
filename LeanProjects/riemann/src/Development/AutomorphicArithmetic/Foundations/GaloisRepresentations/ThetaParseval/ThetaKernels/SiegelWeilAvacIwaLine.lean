import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.IwaLine
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitIwa
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacIwaA
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacIwaB

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Avac
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace LineFix
theorem good_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : (PositivityTheory.RgEis.adCM σ d.χ).Good :=
  PositivityTheory.RgEis.Hd.cmGood_of PositivityTheory.RgEis.Hd.stdGood PositivityTheory.RgEis.Hd.dict PositivityTheory.RgEis.Hd.dictInf F E σ d.χ d.m
    d.ok.good.cm d.ok.good.unram d.ok.hecke d.ok.res
theorem cc_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : AE F E) : cA σ (cA σ x) = x := (_root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.good_k d).σσ x
theorem frame_eps_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∃ ε : ℤˣ, (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ) =
    Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E))) 0 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  refine ⟨ε, ?_⟩
  have e1 : (incM F d.b.1).map (cA σ) = incM F (d.b.1.map σ) := by
    ext i j
    simp [incM, cA, inclR, Algebra.TensorProduct.map_tmul]
  have e2 : dbl (incM F d.Y.J) = incM F (dbl d.Y.J) := by
    simp [dbl, incM, Matrix.fromBlocks_map, Matrix.map_neg]
  have key : incM F (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ) =
      (incM F d.b.1)ᵀ * incM F (dbl d.Y.J) * incM F (d.b.1.map σ) := by
    simp only [incM, Matrix.map_mul, Matrix.transpose_map]
  rw [e1, e2, ← key, hε]
  ext (i|i) (j|j) <;> simp [incM, Matrix.fromBlocks_map, Matrix.one_apply] <;> split_ifs <;> simp
variable {n : ℕ}
section Unit
variable {ι : Type} [Fintype ι] [DecidableEq ι]
end Unit
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem mL_mem_k (κ : GL (Fin d.n) (AE F E)) :
    (incM F d.b.1 * Nk (σ := σ) κ * incM F (d.b⁻¹).1)ᵀ * dbl (incM F d.Y.J) *
      (incM F d.b.1 * Nk (σ := σ) κ * incM F (d.b⁻¹).1).map (cA σ) = dbl (incM F d.Y.J) := by
  obtain ⟨ε, hε⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.frame_eps_k d
  have hN := Nk_form (σ := σ) (_root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.cc_k d) ((ε : ℤ) : AE F E) κ
  rw [← hε] at hN
  exact KWhit.form_conj_out (cA σ).toRingHom (_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d) hN
theorem mL_mul_k (κ : GL (Fin d.n) (AE F E)) :
    (incM F d.b.1 * Nk (σ := σ) κ * incM F (d.b⁻¹).1) * (incM F d.b.1 * Nk (σ := σ) κ⁻¹ * incM F (d.b⁻¹).1) = 1 := by
  calc _ = incM F d.b.1 * Nk (σ := σ) κ * (incM F (d.b⁻¹).1 * incM F d.b.1) * Nk (σ := σ) κ⁻¹ * incM F (d.b⁻¹).1 := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.mul_one, Matrix.mul_assoc (incM F d.b.1), Nk_mul_inv, Matrix.mul_one,
          _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d]
def mL_k (κ : GL (Fin d.n) (AE F E)) : d.G :=
  ⟨⟨incM F d.b.1 * Nk (σ := σ) κ * incM F (d.b⁻¹).1, incM F d.b.1 * Nk (σ := σ) κ⁻¹ * incM F (d.b⁻¹).1, _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.mL_mul_k d κ,
    by simpa using _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.mL_mul_k d κ⁻¹⟩, by
    show (incM F d.b.1 * Nk (σ := σ) κ * incM F (d.b⁻¹).1)ᵀ * dbl (incM F d.Y.J) *
      (incM F d.b.1 * Nk (σ := σ) κ * incM F (d.b⁻¹).1).map (cA σ) = dbl (incM F d.Y.J)
    exact _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.mL_mem_k d κ⟩
theorem inFrame_mL_k (κ : GL (Fin d.n) (AE F E)) : inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.mL_k d κ) = Nk (σ := σ) κ := by
  show incM F (d.b⁻¹).1 * (incM F d.b.1 * Nk (σ := σ) κ * incM F (d.b⁻¹).1) * incM F d.b.1 = Nk (σ := σ) κ
  simp only [← Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.one_mul]
  rw [Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.mul_one]
theorem mL_inv_k (κ : GL (Fin d.n) (AE F E)) : _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.mL_k d κ⁻¹ = (_root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.mL_k d κ)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  apply _root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_injective_k d
  rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.inFrame_mL_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.inFrame_mL_k, Nk_mul_inv, _root_.PositivityTheory.SiegelWeilFormula.Avac.inFrame_one_k]
theorem O_int_k {z : AE F E} (hz : z ∈ (PositivityTheory.RgEis.adCM σ d.χ).O) : finOne F • z ∈ intHat F E :=
  ((PositivityTheory.RgEis.Hd.dict F E).2.2.2.1 z).1 hz
theorem Nk_int_k {κ : GL (Fin d.n) (AE F E)} (hκ : κ ∈ (PositivityTheory.RgEis.adCM σ d.χ).kGL (Fin d.n)) (i j : Fin d.n ⊕ Fin d.n) :
    finOne F • Nk (σ := σ) κ i j ∈ intHat F E := by
  have hκ' := hκ.1
  rcases i with i | i <;> rcases j with j | j
  · exact _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.O_int_k d (hκ' i j).1
  · simp [Nk, (intHat F E).zero_mem]
  · simp [Nk, (intHat F E).zero_mem]
  · exact _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.O_int_k d ((_root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.good_k d).σO _ (hκ' j i).2)
theorem Nk_unit_k {κ : GL (Fin d.n) (AE F E)} (hκ : κ ∈ (PositivityTheory.RgEis.adCM σ d.χ).kGL (Fin d.n)) (w : InfinitePlace F) :
    (Nk (σ := σ) κ).map (piInf (d.B.emb w)) * ((Nk (σ := σ) κ).map (piInf (d.B.emb w)))ᴴ = 1 := by
  obtain ⟨w', hw'⟩ := ((PositivityTheory.RgEis.Hd.dictInf F E σ d.ok.good.cm).2 d.B.emb).1 w
  set g := (PositivityTheory.RgEis.adCM σ d.χ).φ w' with hg
  have hU : (κ : Matrix (Fin d.n) (Fin d.n) (AE F E)).map g ∈ Matrix.unitaryGroup (Fin d.n) ℂ := hκ.2 w'
  have hV : ((κ⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E)).map g ∈
      Matrix.unitaryGroup (Fin d.n) ℂ := (inv_mem hκ).2 w'
  have hσφ : ∀ z, g (cA σ z) = (starRingEnd ℂ) (g z) := fun z => (_root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.good_k d).σφ w' z
  rcases hw' with hf | hf
  · have hf' : ∀ z, piInf (d.B.emb w) z = g z := hf
    have e : (Nk (σ := σ) κ).map (piInf (d.B.emb w)) = Matrix.fromBlocks ((κ : Matrix (Fin d.n) (Fin d.n) (AE F E)).map g) 0 0
        (star (((κ⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E)).map g)) := by
      ext (i | i) (j | j) <;> simp [Nk, Dk, hf', hσφ, Matrix.star_apply]
    rw [e]
    exact blk_unit hU (Unitary.star_mem hV)
  · have hf' : ∀ z, piInf (d.B.emb w) z = (starRingEnd ℂ) (g z) := hf
    have e : (Nk (σ := σ) κ).map (piInf (d.B.emb w)) = Matrix.fromBlocks (star ((κ : Matrix (Fin d.n) (Fin d.n) (AE F E)).map g))ᵀ 0 0
        ((((κ⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E)).map g))ᵀ := by
      ext (i | i) (j | j) <;> simp [Nk, Dk, hf', hσφ, Matrix.star_apply]
    rw [e]
    exact blk_unit (transpose_mem_unitaryGroup_vacuum_iwasawa (Unitary.star_mem hU)) (transpose_mem_unitaryGroup_vacuum_iwasawa hV)
theorem mL_mem_K_k {κ : GL (Fin d.n) (AE F E)} (hκ : κ ∈ (PositivityTheory.RgEis.adCM σ d.χ).kGL (Fin d.n)) : _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.mL_k d κ ∈ d.K := by
  refine (d.ok.stdK _).2 ⟨fun w => ?_, fun k' hk' i j => ?_⟩
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.inFrame_mL_k]; exact _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.Nk_unit_k d hκ w
  · rcases hk' with rfl | hk'
    · rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.inFrame_mL_k]; exact _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.Nk_int_k d hκ i j
    · rw [Set.mem_singleton_iff] at hk'
      subst hk'
      rw [← _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.mL_inv_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.inFrame_mL_k]
      exact _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.Nk_int_k d (inv_mem hκ) i j
end LineFix
theorem line_fix'_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (i₀ : Fin d.n) (x : d.G) : ∃ (p k : d.G) (lam : (AE F E)ˣ), k ∈ d.K ∧ x = p * k ∧
    ∀ a, inFrame d.b p a (Sum.inl i₀) = if a = Sum.inl i₀ then (lam : AE F E) else 0 := by
  obtain ⟨p0, t, hp, k1, hk1, rfl⟩ := d.ok.hgt.iwa x
  have h21 := _root_.PositivityTheory.SiegelWeilFormula.KWhit.parabolic_lowerLeft_block_zero d p0 t hp
  obtain ⟨-, -, A, -, -, -, hA, -, -⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.par_frame_k d p0 h21
  obtain ⟨a1, ha1, κ, hκ, hAe⟩ := (_root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.good_k d).iwa (Fin d.n) {i₀} A
  have hs : ∀ r, r ≠ i₀ → (a1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) r i₀ = 0 ∧
      ((a1⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E)) r i₀ = 0 :=
    fun r hr => ha1 r (by simpa using hr) i₀ rfl
  have hunit : (a1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) i₀ i₀ *
      ((a1⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E)) i₀ i₀ = 1 := by
    have := congrFun (congrFun (LineFix.val_mul_inv a1) i₀) i₀
    rw [Matrix.mul_apply, Finset.sum_eq_single i₀ (fun r _ hr => by rw [(hs r hr).2, mul_zero]) (by simp),
      Matrix.one_apply_eq] at this
    exact this
  refine ⟨p0 * (_root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.mL_k d κ)⁻¹, _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.mL_k d κ * k1, Units.mkOfMulEqOne _ _ hunit,
    d.K.mul_mem (_root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.mL_mem_K_k d hκ) hk1, by group, fun a => ?_⟩
  have hMb : inFrame d.b p0 = Matrix.fromBlocks (A : Matrix (Fin d.n) (Fin d.n) (AE F E)) (inFrame d.b p0).toBlocks₁₂ 0
      (inFrame d.b p0).toBlocks₂₂ := by
    rw [hA, ← h21, Matrix.fromBlocks_toBlocks]
  have hAk : (A : Matrix (Fin d.n) (Fin d.n) (AE F E)) * ((κ⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E)) =
      a1 := by
    rw [hAe, Units.val_mul, Matrix.mul_assoc, LineFix.val_mul_inv, Matrix.mul_one]
  rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k, ← _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.mL_inv_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.inFrame_mL_k, hMb]
  rcases a with r | r
  · simp only [LineFix.Nk, Matrix.fromBlocks_multiply, Matrix.mul_zero, add_zero, Matrix.fromBlocks_apply₁₁, hAk]
    by_cases hr : r = i₀
    · subst hr; simp
    · rw [(hs r hr).1]; simp [hr]
  · simp [LineFix.Nk, Matrix.fromBlocks_multiply]
end PositivityTheory.SiegelWeilFormula.Avac
end
end
