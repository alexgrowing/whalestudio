import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoOfSqueeze
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeExistsPosUnique
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAlgebrasMaxCompactAndLeviInterStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeWholeGroupStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeMeasureMatrixAlgebraSubgroupLocalAsymptoticStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeVolumeUnitaryGroupEqStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.VolMaxK

open Formalism.REAL hiding volU
open GlobalTheory.GaugeProd

variable {n p q : ℕ}

def blk (e : Fin p ⊕ Fin q ≃ Fin n) (g : Matrix (Fin p) (Fin p) ℂ) (h : Matrix (Fin q) (Fin q) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := (fromBlocks g 0 0 h).submatrix e.symm e.symm

theorem blk_mul (e : Fin p ⊕ Fin q ≃ Fin n) (g g' : Matrix (Fin p) (Fin p) ℂ) (h h' : Matrix (Fin q) (Fin q) ℂ) :
    blk e g h * blk e g' h' = blk e (g * g') (h * h') := by
  unfold blk
  rw [Matrix.submatrix_mul_equiv, fromBlocks_multiply]
  simp

theorem blk_one (e : Fin p ⊕ Fin q ≃ Fin n) : blk e 1 1 = 1 := by
  simp [blk, fromBlocks_one, submatrix_one_equiv]

theorem blk_ct (e : Fin p ⊕ Fin q ≃ Fin n) (g : Matrix (Fin p) (Fin p) ℂ) (h : Matrix (Fin q) (Fin q) ℂ) :
    (blk e g h)ᴴ = blk e gᴴ hᴴ := by
  simp [blk, conjTranspose_submatrix, fromBlocks_conjTranspose]

theorem blk_inj (e : Fin p ⊕ Fin q ≃ Fin n) {g g' : Matrix (Fin p) (Fin p) ℂ} {h h' : Matrix (Fin q) (Fin q) ℂ}
    (H : blk e g h = blk e g' h') : g = g' ∧ h = h' := by
  have H' := congrArg (fun M => M.submatrix e e) H
  simp only [blk, submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id] at H'
  rw [fromBlocks_inj] at H'
  exact ⟨H'.1, H'.2.2.2⟩

theorem hs_blk (e : Fin p ⊕ Fin q ≃ Fin n) (g : Matrix (Fin p) (Fin p) ℂ) (h : Matrix (Fin q) (Fin q) ℂ) :
    hs (blk e g h - 1) = hs (g - 1) + hs (h - 1) := by
  have h1 : blk e g h - 1 = blk e (g - 1) (h - 1) := by
    rw [← blk_one e]
    ext i j
    simp only [blk, Matrix.sub_apply, Matrix.submatrix_apply]
    generalize e.symm i = a
    generalize e.symm j = b
    rcases a with a | a <;> rcases b with b | b <;> simp
  have key : ∀ F : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ,
      hs (F.submatrix e.symm e.symm) = ∑ a, ∑ b, ‖F a b‖ ^ 2 := by
    intro F
    unfold hs
    refine Fintype.sum_equiv e.symm _ _ (fun i => ?_)
    exact Fintype.sum_equiv e.symm _ _ (fun j => rfl)
  rw [h1]
  unfold blk
  rw [key]
  simp [hs, Fintype.sum_sum_type]

theorem Jm_allPos (N : ℕ) : Jm (allPos N) = 1 := by
  simp [Jm, allPos]

theorem Jm_eq {ε : Fin n → Bool} (e : Fin p ⊕ Fin q ≃ Fin n) (h1 : ∀ i, ε (e (Sum.inl i)) = true)
    (h2 : ∀ i, ε (e (Sum.inr i)) = false) : Jm ε = blk e 1 (-1) := by
  ext i j
  obtain ⟨a, rfl⟩ := e.surjective i
  obtain ⟨b, rfl⟩ := e.surjective j
  simp only [Jm, blk, submatrix_apply, diagonal_apply, Equiv.symm_apply_apply,
    EmbeddingLike.apply_eq_iff_eq]
  rcases a with a | a <;> rcases b with b | b <;> simp [h1, h2, one_apply] <;> split_ifs <;> simp

theorem unit_allPos {N : ℕ} (g : UJ (allPos N)) : (uMat g)ᴴ * uMat g = 1 := by
  have h : inUJ (allPos N) (uMat g) := g.2
  unfold inUJ at h
  rwa [Jm_allPos, Matrix.mul_one] at h

def emb {ε : Fin n → Bool} (e : Fin p ⊕ Fin q ≃ Fin n) (hJ : Jm ε = blk e 1 (-1))
    (x : UJ (allPos p) × UJ (allPos q)) : UJ ε :=
  ⟨⟨blk e (uMat x.1) (uMat x.2), blk e (uMat x.1⁻¹) (uMat x.2⁻¹),
    by rw [blk_mul]; simp [uMat, blk_one], by rw [blk_mul]; simp [uMat, blk_one]⟩, by
    change inUJ _ _
    simp only [inUJ, hJ, blk_ct, blk_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, unit_allPos]⟩

theorem uMat_emb {ε : Fin n → Bool} (e : Fin p ⊕ Fin q ≃ Fin n) (hJ : Jm ε = blk e 1 (-1))
    (x : UJ (allPos p) × UJ (allPos q)) : uMat (emb e hJ x) = blk e (uMat x.1) (uMat x.2) := rfl

theorem emb_mul {ε : Fin n → Bool} (e : Fin p ⊕ Fin q ≃ Fin n) (hJ : Jm ε = blk e 1 (-1))
    (x y : UJ (allPos p) × UJ (allPos q)) : emb e hJ (x * y) = emb e hJ x * emb e hJ y := by
  apply Subtype.ext
  apply Units.ext
  show uMat (emb e hJ (x * y)) = uMat (emb e hJ x) * uMat (emb e hJ y)
  rw [uMat_emb, uMat_emb, uMat_emb, blk_mul]
  rfl

theorem continuous_uMat {ε : Fin n → Bool} : Continuous (uMat : UJ ε → Matrix (Fin n) (Fin n) ℂ) := Units.continuous_val.comp continuous_subtype_val

theorem continuous_emb {ε : Fin n → Bool} (e : Fin p ⊕ Fin q ≃ Fin n) (hJ : Jm ε = blk e 1 (-1)) :
    Continuous (emb e hJ) := by
  refine continuous_induced_rng.2 ?_
  rw [Units.continuous_iff]
  constructor
  · show Continuous fun x : UJ (allPos p) × UJ (allPos q) => blk e (uMat x.1) (uMat x.2)
    exact ((continuous_uMat.comp continuous_fst).matrix_fromBlocks continuous_const continuous_const
      (continuous_uMat.comp continuous_snd)).matrix_submatrix _ _
  · show Continuous fun x : UJ (allPos p) × UJ (allPos q) => blk e (uMat x.1⁻¹) (uMat x.2⁻¹)
    exact ((continuous_uMat.comp continuous_fst.inv).matrix_fromBlocks continuous_const continuous_const
      (continuous_uMat.comp continuous_snd.inv)).matrix_submatrix _ _

theorem emb_mem {ε : Fin n → Bool} (e : Fin p ⊕ Fin q ≃ Fin n) (hJ : Jm ε = blk e 1 (-1))
    (x : UJ (allPos p) × UJ (allPos q)) : emb e hJ x ∈ maxK ε := by
  show (uMat (emb e hJ x))ᴴ * uMat (emb e hJ x) = 1
  rw [uMat_emb, blk_ct, blk_mul, unit_allPos, unit_allPos, blk_one]

theorem exists_allPos {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (hg : gᴴ * g = 1) :
    ∃ x : UJ (allPos N), uMat x = g := by
  have hg' : g * gᴴ = 1 := mul_eq_one_comm.mp hg
  refine ⟨⟨⟨g, gᴴ, hg', hg⟩, ?_⟩, rfl⟩
  show inUJ (allPos N) g
  unfold inUJ
  rw [Jm_allPos, Matrix.mul_one, hg]

private theorem eq_of_submatrix_equiv_symm_eq (e : Fin p ⊕ Fin q ≃ Fin n) {X Y : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ}
    (h : X.submatrix e.symm e.symm = Y.submatrix e.symm e.symm) : X = Y := by
  have h' := congrArg (fun Z => Z.submatrix e e) h
  simpa [submatrix_submatrix] using h'

theorem emb_surj {ε : Fin n → Bool} (e : Fin p ⊕ Fin q ≃ Fin n) (hJ : Jm ε = blk e 1 (-1))
    (k : UJ ε) (hk : k ∈ maxK ε) : ∃ x, emb e hJ x = k := by
  have hu : (uMat k)ᴴ * uMat k = 1 := hk
  have hJk : (uMat k)ᴴ * Jm ε * uMat k = Jm ε := k.2
  have hu' : uMat k * (uMat k)ᴴ = 1 := mul_eq_one_comm.mp hu
  have hc : Jm ε * uMat k = uMat k * Jm ε := by
    calc Jm ε * uMat k = (uMat k * (uMat k)ᴴ) * Jm ε * uMat k := by rw [hu', Matrix.one_mul]
      _ = uMat k * ((uMat k)ᴴ * Jm ε * uMat k) := by simp only [Matrix.mul_assoc]
      _ = uMat k * Jm ε := by rw [hJk]
  set M := (uMat k).submatrix e e with hMdef
  have hK : uMat k = (fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂).submatrix e.symm e.symm := by
    rw [fromBlocks_toBlocks, hMdef, submatrix_submatrix]
    simp
  rw [hJ, hK] at hc
  unfold blk at hc
  rw [submatrix_mul_equiv, submatrix_mul_equiv] at hc
  have hc2 := eq_of_submatrix_equiv_symm_eq e hc
  rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at hc2
  obtain ⟨-, hB, hC, -⟩ := hc2
  have hB0 : M.toBlocks₁₂ = 0 := by
    ext i j
    have h := congrFun (congrFun hB i) j
    simp only [Matrix.one_mul, Matrix.zero_mul, add_zero, Matrix.mul_zero, zero_add, Matrix.mul_neg,
      Matrix.mul_one, Matrix.neg_apply] at h
    simp only [Matrix.zero_apply]
    linear_combination h / 2
  have hC0 : M.toBlocks₂₁ = 0 := by
    ext i j
    have h := congrFun (congrFun hC i) j
    simp only [Matrix.one_mul, Matrix.zero_mul, add_zero, Matrix.mul_zero, zero_add, Matrix.neg_mul,
      Matrix.mul_one, Matrix.neg_apply] at h
    simp only [Matrix.zero_apply]
    linear_combination -h / 2
  have hK' : uMat k = blk e M.toBlocks₁₁ M.toBlocks₂₂ := by
    rw [hK, hB0, hC0]
    rfl
  have hgh := hu
  rw [hK', blk_ct, blk_mul, ← blk_one e] at hgh
  obtain ⟨hg1, hh1⟩ := blk_inj e hgh
  obtain ⟨x1, hx1⟩ := exists_allPos _ hg1
  obtain ⟨x2, hx2⟩ := exists_allPos _ hh1
  refine ⟨(x1, x2), ?_⟩
  apply Subtype.ext
  apply Units.ext
  show uMat (emb e hJ (x1, x2)) = uMat k
  rw [uMat_emb, hK']
  simp only [hx1, hx2]

theorem exists_equiv (ε : Fin n → Bool) (hp : (univ.filter fun a => ε a = true).card = p)
    (hq : (univ.filter fun a => ε a = false).card = q) :
    ∃ e : Fin p ⊕ Fin q ≃ Fin n, Jm ε = blk e 1 (-1) := by
  classical
  have c1 : Fintype.card {a // ε a = true} = p := by
    rw [Fintype.card_subtype]
    convert hp
  have c2 : Fintype.card {a // ¬ ε a = true} = q := by
    rw [Fintype.card_subtype]
    convert hq using 3
    simp
  let e : Fin p ⊕ Fin q ≃ Fin n :=
    (Equiv.sumCongr (Fintype.equivFinOfCardEq c1).symm (Fintype.equivFinOfCardEq c2).symm).trans
      (Equiv.sumCompl fun a => ε a = true)
  refine ⟨e, Jm_eq e (fun i => ?_) (fun i => ?_)⟩
  · simp only [e, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
    exact ((Fintype.equivFinOfCardEq c1).symm i).2
  · simp only [e, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
    simpa using ((Fintype.equivFinOfCardEq c2).symm i).2

theorem continuous_hs {ε : Fin n → Bool} : Continuous fun g : UJ ε => hs (uMat g - 1) := by
  unfold hs
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (((continuous_uMat.sub continuous_const).matrix_elem i j).norm).pow 2

theorem hs_nonneg (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs g := by
  unfold hs
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity

theorem volU_pos (N : ℕ) : 0 < volU N := by
  unfold volU sphV
  positivity

theorem exists_gauge_allPos (N : ℕ) : ∃ ν : Measure (UJ (allPos N)), IsFiniteMeasure ν ∧ ν.IsMulLeftInvariant ∧
    Asym ν (fun g => hs (uMat g - 1)) (N ^ 2) ∧ ν Set.univ = ENNReal.ofReal (volU N) := by
  obtain ⟨c, hc0, hc, -⟩ := GlobalTheory.GaugeConst.gauge_exists_pos_unique N (allPos N)
  have hsub := ((GlobalTheory.T.riemannianHaarGauge_whole_group N (allPos N)).1 c hc).2
  have hvol := GlobalTheory.T.riemannianHaarGauge_volume_unitaryGroup_eq N c hc
  have hfin : Formalism.REAL.muG (allPos N) Set.univ ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top, mul_zero] at hvol
    exact (volU_pos N).ne hvol
  refine ⟨ENNReal.ofReal c • Formalism.REAL.muG (allPos N), ⟨?_⟩, ⟨fun g => hsub.2.1 g trivial⟩, hsub.2.2, ?_⟩
  · rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin.lt_top
  · rw [Measure.smul_apply, smul_eq_mul, ← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul hc0.le, hvol]

theorem volume_maxK : ∀ (n : ℕ) (ε : Fin n → Bool) (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → ∀ μ, IsGaugeSub (maxK ε) (p ^ 2 + q ^ 2) μ → μ Set.univ = ENNReal.ofReal (volU p * volU q) := by
  intro n ε p q hp hq μ hμ
  obtain ⟨e, hJ⟩ := exists_equiv ε hp hq
  obtain ⟨ν₁, hf₁, hi₁, ha₁, hv₁⟩ := exists_gauge_allPos p
  obtain ⟨ν₂, hf₂, hi₂, ha₂, hv₂⟩ := exists_gauge_allPos q
  have hflag : IsIsoFlag ε (fun _ : Fin 0 => (0 : ℕ)) (fun _ : Fin 1 => (⊥ : Submodule ℂ (Fin n → ℂ))) := by
    refine ⟨rfl, fun _ _ _ => le_rfl, fun i => i.elim0, ?_⟩
    intro x hx y _
    simp only [Submodule.mem_bot] at hx
    subst hx
    simp
  obtain ⟨A, E, hA, hE, hAE, hK⟩ := (GlobalTheory.T.exists_algebras_maxCompact_and_levi_inter n ε 0 _ _ hflag p q hp hq).1
  have hmeasEmb : Measurable (emb e hJ) := (continuous_emb e hJ).measurable
  have hclosedK : IsClosed (maxK ε) := by
    have hcont : Continuous fun g : Formalism.REAL.UJ ε => (uMat g)ᴴ * uMat g :=
      continuous_uMat.matrix_conjTranspose.matrix_mul continuous_uMat
    exact isClosed_eq hcont continuous_const
  have hμ' : IsGaugeSub (maxK ε) (p ^ 2 + q ^ 2) ((ν₁.prod ν₂).map (emb e hJ)) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [Measure.map_apply hmeasEmb hclosedK.measurableSet.compl]
      have hempty : emb e hJ ⁻¹' (maxK ε)ᶜ = ∅ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]
        exact emb_mem e hJ x
      rw [hempty, measure_empty]
    · intro s hs
      obtain ⟨x0, rfl⟩ := emb_surj e hJ s hs
      have hl1 : Measurable fun g : Formalism.REAL.UJ ε => emb e hJ x0 * g := (continuous_const.mul continuous_id).measurable
      have hl2 : Measurable fun x : Formalism.REAL.UJ (allPos p) × Formalism.REAL.UJ (allPos q) => x0 * x :=
        (continuous_const.mul continuous_id).measurable
      rw [Measure.map_map hl1 hmeasEmb]
      have hcomp : (fun g => emb e hJ x0 * g) ∘ emb e hJ = emb e hJ ∘ (fun x => x0 * x) := by
        funext x
        simp [emb_mul]
      rw [hcomp, ← Measure.map_map hmeasEmb hl2, map_mul_left_eq_self]
    · have hm1 : Measurable fun g : Formalism.REAL.UJ (allPos p) => hs (uMat g - 1) := continuous_hs.measurable
      have hm2 : Measurable fun g : Formalism.REAL.UJ (allPos q) => hs (uMat g - 1) := continuous_hs.measurable
      have hP := Asym.prod ha₁ ha₂ hm1 hm2 (fun _ => hs_nonneg _) (fun _ => hs_nonneg _)
      unfold Asym at hP
      refine hP.congr fun r => ?_
      congr 1
      have hmeas : MeasurableSet {g : Formalism.REAL.UJ ε | √(hs (uMat g - 1)) ≤ r} :=
        measurableSet_le (Real.continuous_sqrt.comp continuous_hs).measurable measurable_const
      rw [Measure.map_apply hmeasEmb hmeas]
      congr 1
      ext x
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, uMat_emb, hs_blk]
  rw [hK] at hμ hμ'
  have huniq := (GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε A _ E hA hE hAE μ hμ).2.2.1 _ hμ'
  rw [← huniq, Measure.map_apply hmeasEmb MeasurableSet.univ, Set.preimage_univ, ← Set.univ_prod_univ,
    Measure.prod_prod, hv₁, hv₂, ← ENNReal.ofReal_mul (volU_pos p).le]

end GlobalTheory.VolMaxK
