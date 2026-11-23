import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ProjectedBlockUpperSum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.BMatK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.UnipotentNilpotentMulEqZero
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourNA
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisensteinSecondTerm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayDecG

set_option synthInstance.maxHeartbeats 200000

section
set_option linter.unusedSectionVars false
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem nilpotentMap_add (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (a : E) : σ (σ a) = a := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good a
theorem cc_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (z : AE F E) : cA σ (cA σ z) = z := kfour.cA_cA' σ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.nilpotentMap_add d) z
theorem idx_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (i : Fin d.n) : i = L.i₀ ∨ ∃ k, i = L.em k := by
  by_cases h : i = L.i₀
  · exact Or.inl h
  · obtain ⟨k, hk⟩ := (L.rng i).1 h
    exact Or.inr ⟨k, hk.symm⟩
theorem sum_split_k {M : Type} [AddCommMonoid M] (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (f : Fin d.n → M) :
    ∑ i, f i = f L.i₀ + ∑ k, f (L.em k) := by
  have himg : Finset.univ.image L.em = Finset.univ.erase L.i₀ := by
    ext i
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    rw [L.rng i]
    rfl
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ L.i₀), ← himg, Finset.sum_image (fun a _ b _ h => L.inj h)]
theorem uA_mul_neg_k (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (u : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L u * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-u) = 1 := by
  have e : ∀ v, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L v = 1 + _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L v := fun v => rfl
  have hs : _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u + _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L (-u) = 0 := by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart, ← Finset.sum_add_distrib, Pi.neg_apply, ← Matrix.single_add, add_neg_cancel, neg_add_cancel,
      Matrix.single_zero, Finset.sum_const_zero]
  rw [e, e]
  calc (1 + _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u) * (1 + _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L (-u)) = 1 + (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u + _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L (-u)) + _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u * _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L (-u) := by
        noncomm_ring
    _ = 1 := by rw [hs, _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotent_nilpotent_mul_eq_zero]; simp
theorem blockDiagonal_preserves_form_iff (x : d.G) (h21 : (inFrame d.b x).toBlocks₂₁ = 0) :
    ((inFrame d.b x).toBlocks₁₁)ᵀ * ((inFrame d.b x).toBlocks₂₂).map (cA σ) = 1 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  have hf := kunf.frame_eq hε x
  set M := inFrame d.b x with hMdef
  have hM : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    rw [← h21]; exact (Matrix.fromBlocks_toBlocks M).symm
  rw [hM] at hf
  have h12 := congrArg Matrix.toBlocks₁₂ hf
  simp only [kunf.jw, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
    Matrix.transpose_zero, Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, Matrix.toBlocks_fromBlocks₁₂] at h12
  exact h12
theorem lr_of_k {x : d.G} {a β D ainv : Matrix (Fin d.n) (Fin d.n) (AE F E)}
    (h : inFrame d.b x = Matrix.fromBlocks a β 0 D) (ha : a * ainv = 1) : D = ainvᵀ.map (cA σ) := by
  have hx := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.blockDiagonal_preserves_form_iff x (by rw [h]; rfl)
  rw [h] at hx
  simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₂₂] at hx
  have e2 : D.map (cA σ) = ainvᵀ := by
    calc D.map (cA σ) = (ainvᵀ * aᵀ) * D.map (cA σ) := by
          rw [← Matrix.transpose_mul, ha, Matrix.transpose_one, Matrix.one_mul]
      _ = ainvᵀ := by rw [Matrix.mul_assoc, hx, Matrix.mul_one]
  rw [← e2]
  ext i j
  simp [Matrix.map_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cc_k d]
theorem eq_of_upper_k {x y : d.G} (hx : (inFrame d.b x).toBlocks₂₁ = 0) (hy : (inFrame d.b y).toBlocks₂₁ = 0)
    (h11 : (inFrame d.b x).toBlocks₁₁ = (inFrame d.b y).toBlocks₁₁)
    (h12 : (inFrame d.b x).toBlocks₁₂ = (inFrame d.b y).toBlocks₁₂) : x = y := by
  have ex := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.blockDiagonal_preserves_form_iff x hx
  have ey := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.blockDiagonal_preserves_form_iff y hy
  rw [h11] at ex
  have ey' : ((inFrame d.b y).toBlocks₂₂).map (cA σ) * ((inFrame d.b y).toBlocks₁₁)ᵀ = 1 := mul_eq_one_comm.1 ey
  have hD : ((inFrame d.b x).toBlocks₂₂).map (cA σ) = ((inFrame d.b y).toBlocks₂₂).map (cA σ) := by
    calc _ = (((inFrame d.b y).toBlocks₂₂).map (cA σ) * ((inFrame d.b y).toBlocks₁₁)ᵀ) *
          ((inFrame d.b x).toBlocks₂₂).map (cA σ) := by rw [ey', Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, ex, Matrix.mul_one]
  have hD' : (inFrame d.b x).toBlocks₂₂ = (inFrame d.b y).toBlocks₂₂ := by
    ext i j
    have := congrArg (cA σ) (congrFun (congrFun hD i) j)
    simpa only [Matrix.map_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cc_k d] using this
  exact _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inj_k d (Matrix.ext_iff_blocks.2 ⟨h11, h12, hx.trans hy.symm, hD'⟩)
variable {R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
theorem inFrame_cM_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (c : (Fin L.n → AE F E) × AF F) :
    inFrame d.b (cM c) = Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L c.1) (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ c.2) 0 ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k L (-c.1))ᵀ.map (cA σ)) := by
  obtain ⟨A', hA⟩ := h.cf c
  rw [hA, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.lr_of_k hA (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_mul_neg_k L c.1)]
theorem eps_mul_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : ((R.ε : ℤ) : AE F E) * ((R.ε : ℤ) : AE F E) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
theorem eps_mulE_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : ((R.ε : ℤ) : E) * ((R.ε : ℤ) : E) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
theorem eA_eq_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eA_k R = ((R.ε : ℤ) : AE F E) := map_intCast _ _
theorem cA_eA_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : cA σ (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.eA_k R) = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eA_k R := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.eA_eq_k]; exact map_intCast _ _
theorem sB_i0i0_k (b : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L b L.i₀ L.i₀ = 0 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k, Matrix.sum_apply, Matrix.add_apply, Matrix.single_apply, fun j => (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L j), fun j => (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L j).symm]
theorem sB_i0em_k (b : Fin L.n → AE F E) (l : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L b L.i₀ (L.em l) = b l := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k, Matrix.sum_apply, Matrix.add_apply, Matrix.single_apply, fun j => (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L j), fun j => (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L j).symm,
    L.inj.eq_iff]
theorem section_entry_embedded_row (b : Fin L.n → AE F E) (k : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L b (L.em k) L.i₀ = -(_root_.PositivityTheory.SiegelWeilFormula.Act.C5.eA_k R * cA σ (b k)) := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k, Matrix.sum_apply, Matrix.add_apply, Matrix.single_apply, fun j => (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L j), fun j => (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L j).symm,
    L.inj.eq_iff]
theorem sB_emem_k (b : Fin L.n → AE F E) (k l : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L b (L.em k) (L.em l) = 0 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k, Matrix.sum_apply, Matrix.add_apply, Matrix.single_apply, fun j => (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L j), fun j => (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.em_ne_k L j).symm]
theorem sB_cond_k (b : Fin L.n → AE F E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L b ∈ kfour.nCond σ d.n R.ε := by
  show (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L b)ᵀ = -((((R.ε : ℤ) : AE F E)) • (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L b).map (cA σ))
  have e2 := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eps_mul_k R
  ext i j
  rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C5.idx_k L i with rfl | ⟨k, rfl⟩ <;> rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C5.idx_k L j with rfl | ⟨l, rfl⟩ <;>
    simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_i0i0_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_i0em_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.section_entry_embedded_row,
      _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_emem_k, map_zero, smul_zero, neg_zero, smul_eq_mul, map_neg, map_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cA_eA_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.cc_k d, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eA_eq_k]
  all_goals (try simp only [map_intCast])
  all_goals first | (simp; done) | (simp only [mul_neg, neg_neg, neg_mul]; rw [← mul_assoc, e2, one_mul])
theorem continuous_sB_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L) := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k
  refine continuous_finset_sum _ fun j _ => Continuous.add ?_ ?_
  · have e : (fun b : Fin L.n → AE F E => Matrix.single L.i₀ (L.em j) (b j)) =
        fun b => b j • Matrix.single L.i₀ (L.em j) (1 : AE F E) := by
      funext b; rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [e]; exact (continuous_apply j).smul continuous_const
  · have e : (fun b : Fin L.n → AE F E => Matrix.single (L.em j) L.i₀ (-(_root_.PositivityTheory.SiegelWeilFormula.Act.C5.eA_k R * cA σ (b j)))) =
        fun b => (-(_root_.PositivityTheory.SiegelWeilFormula.Act.C5.eA_k R * cA σ (b j))) • Matrix.single (L.em j) L.i₀ (1 : AE F E) := by
      funext b; rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [e]
    exact ((continuous_const.mul ((GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ).comp (continuous_apply j))).neg).smul continuous_const
theorem inFrame_sM'_k (b : Fin L.n → AE F E) : inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b) = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.bMat_k (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L b) := by
  have hex : ∃ x : d.G, inFrame d.b x = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.bMat_k (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L b) :=
    ⟨⟨kfour.nU d.b (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L b), kfour.nU_mem (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.nilpotentMap_add d) R.hε (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_cond_k b)⟩, kfour.inFrame_nU _ _⟩
  unfold _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k _root_.PositivityTheory.SiegelWeilFormula.Act.C5.elt_k
  rw [dif_pos hex]
  exact hex.choose_spec
theorem sig_delta_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) : σ δ = -(((R.ε : ℤ) : E)) * δ := by
  have hx : inFrame d.b (cM (0, 1)) = kfour.nM (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k L δ 1) := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_cM_k h]
    simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.uA_k, kfour.nM, Matrix.transpose_one]
  have hc := kfour.cond_of_inFrame R.hε (cM (0, 1)) _ hx
  have e := congrFun (congrFun hc L.i₀) L.i₀
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.aB_k, Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.single_apply_same,
    one_smul, smul_eq_mul, GlobalTheory.EisBL.DoubledUnipotentRadical.cA_inclR] at e
  have e' : inclR (F := F) (AF F) δ = inclR (F := F) (AF F) (-(((R.ε : ℤ) : E) * σ δ)) := by
    rw [e, map_neg, map_mul, map_intCast]
  have hδ := Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F) e'
  have e2 := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eps_mulE_k R
  linear_combination (((R.ε : ℤ) : E)) * hδ - σ δ * e2
theorem eig_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (y : AE F E) (hy : cA σ y = -(((R.ε : ℤ) : AE F E)) * y) :
    ellA δ y • inclR (F := F) (AF F) δ = y := by
  have hcm : IsCMExt F E σ := d.ok.good.cm
  have hδ0 := h.δ0
  have hδ : σ δ = -(((R.ε : ℤ) : E)) * δ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sig_delta_k h
  have hℓ := ellSpec (F := F) hδ0
  set ℓ := Classical.epsilon fun ℓ : E →ₗ[F] F => δ ≠ 0 → ℓ δ = 1 with hℓdef
  have hline : ∀ e : E, σ e = -(((R.ε : ℤ) : E)) * e → ℓ e • δ = e := by
    intro e he
    obtain ⟨c, rfl⟩ := eigLine hcm R.ε hδ0 hδ he
    rw [map_smul, hℓ, smul_eq_mul, mul_one]
  have hε2 : ((R.ε : ℤ) : E) * ((R.ε : ℤ) : E) = 1 := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eps_mulE_k R
  have hψ : ∀ z : AE F E, ellA δ (z - ((R.ε : ℤ) : AE F E) * cA σ z) • inclR (F := F) (AF F) δ =
      z - ((R.ε : ℤ) : AE F E) * cA σ z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      have hc : cA σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := by
        simp [cA, Algebra.TensorProduct.map_tmul]
      have hm : ((R.ε : ℤ) : AE F E) * (a ⊗ₜ[F] σ e) = a ⊗ₜ[F] (((R.ε : ℤ) : E) * σ e) := by
        rw [← zsmul_eq_mul, ← zsmul_eq_mul, TensorProduct.tmul_smul]
      rw [hc, hm, ← TensorProduct.tmul_sub]
      have he' : σ (e - ((R.ε : ℤ) : E) * σ e) = -(((R.ε : ℤ) : E)) * (e - ((R.ε : ℤ) : E) * σ e) := by
        rw [map_sub, map_mul, map_intCast, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.nilpotentMap_add d]
        linear_combination (-(σ e)) * hε2
      have hl := hline _ he'
      simp only [ellA, LinearMap.coe_comp, Function.comp_apply, LinearMap.baseChange_tmul, AlgEquiv.toLinearMap_apply,
        Algebra.TensorProduct.rid_tmul, inclR, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
      rw [show (Algebra.TensorProduct.includeRight.toRingHom δ : AE F E) = (1 : AF F) ⊗ₜ[F] δ from rfl,
        TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.smul_tmul]
      exact congrArg (a ⊗ₜ[F] ·) hl
    | add x z hx hz =>
      rw [map_add, mul_add, add_sub_add_comm, map_add, add_smul, hx, hz]
  have key := hψ y
  rw [hy, neg_mul, mul_neg, ← mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eps_mul_k R, one_mul, sub_neg_eq_add, map_add, add_smul] at key
  have h2 : (2 : F) • (ellA δ y • inclR (F := F) (AF F) δ) = (2 : F) • y := by
    rw [two_smul, two_smul]; exact key
  exact smul_right_injective (AE F E) (two_ne_zero) h2
theorem ellA_inclR_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) (e : E) : ellA δ (inclR (F := F) (AF F) e) ∈ (algebraMap F (AF F)).range := by
  refine ⟨(Classical.epsilon fun ℓ : E →ₗ[F] F => δ ≠ 0 → ℓ δ = 1) e, ?_⟩
  simp [ellA, inclR, LinearMap.baseChange_tmul, Algebra.TensorProduct.rid_tmul, Algebra.algebraMap_eq_smul_one]
theorem continuous_sM'_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L) := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.nilpotentMap_add d
  have hb := d.ok.frame
  have hnb := kfour.isNMap_nbE hσ hb
  have hmem : ∀ b, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L b ∈ nA σ d.Y d.b := fun b => (kfour.mem_nA_iff hσ R.hε _).2 (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_cond_k b)
  have e : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L = fun b => kfour.nbE σ d.Y d.b ⟨_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sB_k R L b, hmem b⟩ := by
    funext b
    apply _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inj_k d
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.inFrame_sM'_k, hnb]
    rfl
  rw [e]
  exact (kfour.nb_continuous hσ hb hnb).comp (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.continuous_sB_k.subtype_mk _)
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
