import Formalism.HermitianCurvature.HermitianCurvatureProofs.FubiniHeadLastPart
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerBlockPoint
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousInvUpper

open Matrix MeasureTheory Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBJ.Om

theorem muPi_eq (β : ℂ) (ι : Type) [Fintype ι] :
    G.muPi β ι = (Real.toNNReal (‖β‖ / (2 * Real.pi)) ^ Fintype.card ι) • (volume : Measure (ι → ℂ)) := by
  unfold G.muPi G.mu
  rw [Dx2.SL.pi_const_smul, volume_pi]

theorem hMat_apply {m : ℕ} (τ : Equiv.Perm (Fin m)) (e : Fin m → ℂ) (a b : Fin m) :
    U.hMat τ e a b = if τ a = b then e b else 0 := by
  simp [U.hMat, U.wP, Matrix.mul_diagonal]

theorem hMat_rev (m : ℕ) (z : ℂ) : U.hMat (Fin.revPerm : Equiv.Perm (Fin m)) (fun _ => z) = G.ptLong m z := by
  ext a b
  rw [hMat_apply]
  simp only [G.ptLong, G.wMat, Matrix.smul_apply, Matrix.of_apply, Fin.revPerm_apply, smul_eq_mul]
  by_cases h : a.rev = b
  · subst h; simp
  · rw [if_neg h, if_neg (fun h' => h h'.symm)]; simp

instance lw_rev_empty (m : ℕ) : IsEmpty (U.LW (Fin.revPerm : Equiv.Perm (Fin m))) :=
  ⟨fun q => by
    obtain ⟨⟨a, b⟩, h1, h2⟩ := q
    simp only [Fin.revPerm_symm, Fin.revPerm_apply] at h2
    exact absurd (Fin.rev_lt_rev.1 h2) (not_lt.2 h1.le)⟩

theorem lowW_of_empty {m : ℕ} (σ : Equiv.Perm (Fin m)) [IsEmpty (U.LW σ)] (v : U.LW σ → ℂ) : U.lowW σ v = 1 := by
  unfold U.lowW
  ext a b
  simp only [Matrix.add_apply, Matrix.of_apply]
  rw [dif_neg (fun h => IsEmpty.false (⟨(a, b), h⟩ : U.LW σ)), add_zero]

theorem probE {ι X : Type} [Fintype ι] [IsEmpty ι] [MeasureSpace X] : IsProbabilityMeasure (volume : Measure (ι → X)) := by
  rw [volume_pi, Measure.pi_of_empty]; infer_instance

def eU {m : ℕ} (σ : Equiv.Perm (Fin m)) [IsEmpty (U.LW σ)] : U.XiH m 0 σ ≃ᵐ (G.UT m → ℂ) :=
  (Dx2.SL.dropE ((Fin 0 → Fin m → ℂ) × (Fin m → Fin 0 → ℂ)) _).trans (Dx2.SL.dropE (U.LW σ → ℂ) _)

theorem eU_apply {m : ℕ} (σ : Equiv.Perm (Fin m)) [IsEmpty (U.LW σ)] (η : U.XiH m 0 σ) : eU σ η = η.2.2 := rfl

theorem eU_mp {m : ℕ} (σ : Equiv.Perm (Fin m)) [IsEmpty (U.LW σ)] :
    MeasurePreserving (eU σ) volume volume := by
  have hT := Dx2.SL.probT m
  have hL : IsProbabilityMeasure (volume : Measure (U.LW σ → ℂ)) := probE
  have s1 : SigmaFinite (volume : Measure (U.LW σ → ℂ)) := inferInstance
  have s2 : SigmaFinite (volume : Measure (G.UT m → ℂ)) := inferInstance
  have s3 : SFinite (volume : Measure ((U.LW σ → ℂ) × (G.UT m → ℂ))) := by
    rw [Measure.volume_eq_prod]; infer_instance
  have h1 := Dx2.SL.dropE_mp ((Fin 0 → Fin m → ℂ) × (Fin m → Fin 0 → ℂ)) ((U.LW σ → ℂ) × (G.UT m → ℂ))
    volume volume
  have h2 := Dx2.SL.dropE_mp (U.LW σ → ℂ) (G.UT m → ℂ) volume volume
  exact h2.comp h1

theorem omLong_eq (β : ℂ) (n : ℕ) (z : ℂ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (Φ : G.Mat (n + 1) → V) :
    G.OmLong β n Φ z = (((Real.toNNReal (‖β‖ / (2 * Real.pi)) ^ Fintype.card (G.UT (n + 1)) : NNReal) : ℝ) : ℂ) •
      U.PhiTop (p := n + 1) (s := 0) β (Fin.revPerm : Equiv.Perm (Fin (n + 1))) (fun _ => z) Φ
        (fun x => x.elim0) := by
  set σ : Equiv.Perm (Fin (n + 1)) := Fin.revPerm
  let g : (G.UT (n + 1) → ℂ) → V := fun u => G.psi β (G.superSum (G.upper u)) • Φ (G.ptLong (n + 1) z * G.upper u)
  have hfg : (fun η : U.XiH (n + 1) 0 σ => U.psiH β σ η • Φ (U.ZjH (p := n + 1) (s := 0) σ (fun _ => z) η (fun x => x.elim0))) =
      g ∘ eU σ := by
    funext η
    obtain ⟨⟨a0, b0⟩, v, u⟩ := η
    rw [Function.comp_apply, eU_apply]
    simp only [g, U.psiH, U.ZjH]
    rw [Dx2.SL.zj_zero]
    simp only [U.headH, lowW_of_empty σ v, Matrix.mul_one,
      Matrix.mul_nonsing_inv _ (Dx2.SL.isUnit_wP σ), Dx2.SL.subS_one, Dx2.SL.cornerA_zero, Dx2.SL.cornerB_zero,
      zero_add, add_zero, Dx2.SL.supS_superSum]
    congr 2
    rw [← hMat_rev (n + 1) z]
    rfl
  have hP : U.PhiTop (p := n + 1) (s := 0) β σ (fun _ => z) Φ (fun x => x.elim0) = ∫ u, g u := by
    unfold U.PhiTop
    rw [show U.muXiH (n + 1) 0 σ = volume from rfl, hfg]
    exact (eU_mp σ).integral_comp' g
  rw [hP]
  unfold G.OmLong
  rw [muPi_eq, integral_smul_nnreal_measure, NNReal.smul_def, ← Complex.coe_smul]

section block

abbrev σB (n : ℕ) : Equiv.Perm (Fin (n + 1)) := Fub.sigQ (Fin.revPerm : Equiv.Perm (Fin n)) (1 : Equiv.Perm (Fin 1))

def dB (n : ℕ) (t c : ℂ) : Fin (n + 1) → ℂ := Fub.dQ (fun _ : Fin n => t) (fun _ : Fin 1 => c)

theorem symmetricScalarBlockMatrix_one_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin 1) ℂ) (C : Matrix (Fin 1) (Fin n) ℂ)
    (D : Matrix (Fin 1) (Fin 1) ℂ) : U.blk2 A B C D = G.blk A (fun i => B i 0) (fun j => C 0 j) (D 0 0) := by
  unfold U.blk2 G.blk
  congr 1
  rw [Matrix.fromBlocks_inj]
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> ext i j
  · rw [Fin.fin_one_eq_zero j]; rfl
  · rw [Fin.fin_one_eq_zero i]; rfl
  · rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]; rfl

theorem hMat_one_one (c : ℂ) : U.hMat (1 : Equiv.Perm (Fin 1)) (fun _ => c) = Matrix.of fun _ _ => c := by
  ext i j
  rw [hMat_apply, Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
  simp

theorem hMat_block (n : ℕ) (t c : ℂ) : U.hMat (σB n) (dB n t c) = G.ptBlock n t c := by
  unfold σB dB
  rw [Fub.hMat_sigQ, hMat_rev, hMat_one_one, symmetricScalarBlockMatrix_one_zero]
  rfl

instance lw_one_empty : IsEmpty (U.LW (1 : Equiv.Perm (Fin 1))) :=
  ⟨fun q => by
    obtain ⟨⟨a, b⟩, h1, _⟩ := q
    rw [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b] at h1
    exact lt_irrefl _ h1⟩

instance ut_one_empty : IsEmpty (G.UT 1) :=
  ⟨fun q => by
    obtain ⟨⟨a, b⟩, h1⟩ := q
    rw [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b] at h1
    exact lt_irrefl _ h1⟩

instance uniqueRankOneTorus : Unique (U.XiH 1 0 (1 : Equiv.Perm (Fin 1))) := by
  haveI := Dx2.SL.uniqueT 1
  haveI : Unique (U.LW (1 : Equiv.Perm (Fin 1)) → ℂ) := Pi.uniqueOfIsEmpty _
  haveI : Unique (G.UT 1 → ℂ) := Pi.uniqueOfIsEmpty _
  unfold U.XiH; exact Unique.mk' _

theorem isProbabilityMeasure_rank_one_torus : IsProbabilityMeasure (volume : Measure (U.XiH 1 0 (1 : Equiv.Perm (Fin 1)))) := by
  have h1 := Dx2.SL.probT 1
  have h2 : IsProbabilityMeasure (volume : Measure (U.LW (1 : Equiv.Perm (Fin 1)) → ℂ)) := probE
  have h3 : IsProbabilityMeasure (volume : Measure (G.UT 1 → ℂ)) := probE
  have h4 : IsProbabilityMeasure (volume : Measure ((U.LW (1 : Equiv.Perm (Fin 1)) → ℂ) × (G.UT 1 → ℂ))) := by
    rw [Measure.volume_eq_prod]; infer_instance
  rw [Measure.volume_eq_prod]; infer_instance

theorem character_rank_one_eq_one (β : ℂ) (y : U.XiH 1 0 (1 : Equiv.Perm (Fin 1))) : U.psiH β (1 : Equiv.Perm (Fin 1)) y = 1 := by
  unfold U.psiH
  rw [Dx2.SL.cornerA_zero, Dx2.SL.cornerB_zero]
  have h1 : ∀ M : Matrix (Fin 1) (Fin 1) ℂ, U.subS M = 0 := fun M => by simp [U.subS]
  have h2 : ∀ M : Matrix (Fin 1) (Fin 1) ℂ, U.supS M = 0 := fun M => by simp [U.supS]
  rw [h1, h2]
  simp [G.psi]

theorem corner_matrix_rank_one_eq (c : ℂ) (y : U.XiH 1 0 (1 : Equiv.Perm (Fin 1))) :
    U.ZjH (p := 1) (s := 0) (1 : Equiv.Perm (Fin 1)) (fun _ => c) y (fun x => x.elim0) = Matrix.of fun _ _ => c := by
  unfold U.ZjH
  rw [Dx2.SL.zj_zero]
  unfold U.headH
  rw [lowW_of_empty, Matrix.mul_one]
  have hu : G.upper y.2.2 = 1 := by
    ext i j
    rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
    simp [G.upper, G.strictUpper]
  rw [hu, Matrix.mul_one]
  exact hMat_one_one c

theorem upper_mulVec_last {m : ℕ} (u : G.UT (m + 1) → ℂ) (x : Fin (m + 1) → ℂ) :
    (G.upper u *ᵥ x) (Fin.last m) = x (Fin.last m) := by
  simp only [Matrix.mulVec, dotProduct, G.upper, G.strictUpper, Matrix.add_apply, Matrix.one_apply,
    Matrix.of_apply]
  rw [Finset.sum_eq_single (Fin.last m)]
  · simp
  · intro j _ hj
    rw [if_neg (fun h => hj h.symm), dif_neg (not_lt.2 (Fin.le_last j))]
    simp
  · simp

theorem subSum_one {m : ℕ} : G.subSum (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) = 0 := by
  unfold G.subSum
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Matrix.one_apply_ne (ne_of_gt Fin.castSucc_lt_succ)]

theorem chars_block (β : ℂ) (n : ℕ) (a : Fin 1 → Fin n → ℂ) (b : Fin n → Fin 1 → ℂ) (u : G.UT n → ℂ) :
    G.psi β (U.supS (G.upper u) + U.cornerA a + U.cornerB b) =
      G.psi β (G.subSum (G.lowRow (a 0))) *
        G.psi β (G.superSum (G.blk (G.upper u) (G.upper u *ᵥ fun i => b i 0) 0 1)) := by
  rw [← Dx2.SL.psi_add]
  congr 1
  cases n with
  | zero => simp [U.supS, U.cornerA, U.cornerB, G.subSum, G.superSum]
  | succ m =>
    unfold G.lowRow
    rw [G4.subSum_blk, G4.superSum_blk, subSum_one, upper_mulVec_last, ← Dx2.SL.supS_superSum]
    have hA : U.cornerA a = a 0 (Fin.last m) := by
      unfold U.cornerA
      rw [dif_pos ⟨by norm_num, by omega⟩]
      congr 1
    have hB : U.cornerB b = b (Fin.last m) 0 := by
      unfold U.cornerB
      rw [dif_pos ⟨by norm_num, by omega⟩]
      congr 1
    rw [hA, hB]
    ring

theorem mat_block {n : ℕ} (a : Fin 1 → Fin n → ℂ) (b : Fin n → Fin 1 → ℂ) (u : G.UT n → ℂ) (t c : ℂ) :
    U.Zj a b (G.ptLong n t * G.upper u) (Matrix.of fun _ _ => c) =
      G.lowRow (a 0) * G.ptBlock n t c * G.blk (G.upper u) (G.upper u *ᵥ fun i => b i 0) 0 1 := by
  unfold U.Zj
  rw [symmetricScalarBlockMatrix_one_zero, symmetricScalarBlockMatrix_one_zero, symmetricScalarBlockMatrix_one_zero, Matrix.mul_assoc, Matrix.mul_assoc]
  unfold G.ptBlock G.lowRow
  refine congrArg₂ (· * ·) ?_ ?_
  · congr 1
  · rw [G4.blk_mul, G4.blk_mul]
    unfold G.ptLong
    congr 1
    all_goals first | rfl | (funext i; simp [Matrix.vecMulVec, Matrix.mulVec_mulVec]; done) |
      (simp [Matrix.vecMulVec, Matrix.mulVec_mulVec]; done)

def shearU (n : ℕ) : (G.UT n → ℂ) × (Fin n → ℂ) ≃ᵐ (G.UT n → ℂ) × (Fin n → ℂ) where
  toFun q := (q.1, G.upper q.1 *ᵥ q.2)
  invFun q := (q.1, (G.upper q.1)⁻¹ *ᵥ q.2)
  left_inv q := by
    simp only
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (Dx2.SL.isUnit_up q.1), Matrix.one_mulVec]
  right_inv q := by
    simp only
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Dx2.SL.isUnit_up q.1), Matrix.one_mulVec]
  measurable_toFun := (continuous_fst.prodMk ((Dx2.SL.cont_upper.comp continuous_fst).matrix_mulVec
    continuous_snd)).measurable
  measurable_invFun := (continuous_fst.prodMk (((G5.continuous_inv_upper n).comp continuous_fst).matrix_mulVec
    continuous_snd)).measurable

theorem shearU_mp (n : ℕ) : MeasurePreserving (shearU n) volume volume := by
  have hrow : ∀ u : G.UT n → ℂ, MeasurePreserving (fun x : Fin n → ℂ => G.upper u *ᵥ x) volume volume := by
    intro u
    have h := Dx2.SL.row_mp (G.upper u)ᵀ (by rw [Matrix.det_transpose, Ux3.det_upper]; simp)
    have e : (fun x : Fin n → ℂ => Matrix.vecMul x (G.upper u)ᵀ) = fun x => G.upper u *ᵥ x := by
      funext x; rw [Matrix.vecMul_transpose]
    rwa [e] at h
  have hm : Measurable (Function.uncurry fun (u : G.UT n → ℂ) (x : Fin n → ℂ) => G.upper u *ᵥ x) :=
    ((Dx2.SL.cont_upper.comp continuous_fst).matrix_mulVec continuous_snd).measurable
  have h := (MeasurePreserving.id (volume : Measure (G.UT n → ℂ))).skew_product (μc := volume) (μd := volume) hm
    (Filter.Eventually.of_forall fun u => (hrow u).map_eq)
  exact h

def eD (n : ℕ) : ((Fin 1 → Fin n → ℂ) × (Fin n → Fin 1 → ℂ)) × (G.UT n → ℂ) ≃ᵐ G.BlockCoord n :=
  (MeasurableEquiv.prodAssoc.trans (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) MeasurableEquiv.prodComm)).trans
    ((MeasurableEquiv.prodCongr (MeasurableEquiv.funUnique (Fin 1) (Fin n → ℂ))
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
        (MeasurableEquiv.piCongrRight fun _ => MeasurableEquiv.funUnique (Fin 1) ℂ))).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (shearU n)))

theorem eD_apply (n : ℕ) (q : ((Fin 1 → Fin n → ℂ) × (Fin n → Fin 1 → ℂ)) × (G.UT n → ℂ)) :
    eD n q = (q.1.1 0, q.2, G.upper q.2 *ᵥ fun i => q.1.2 i 0) := rfl

theorem eD_mp (n : ℕ) : MeasurePreserving (eD n) volume (volume.prod (volume.prod volume)) := by
  have s1 : SigmaFinite (volume : Measure (Fin 1 → Fin n → ℂ)) := inferInstance
  have s2 : SigmaFinite (volume : Measure (Fin n → Fin 1 → ℂ)) := inferInstance
  have s3 : SigmaFinite (volume : Measure (G.UT n → ℂ)) := inferInstance
  have h1 := Dx2.SL.assoc_mp (volume : Measure (Fin 1 → Fin n → ℂ)) (volume : Measure (Fin n → Fin 1 → ℂ))
    (volume : Measure (G.UT n → ℂ))
  have h2 : MeasurePreserving (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (Fin 1 → Fin n → ℂ))
      (MeasurableEquiv.prodComm : (Fin n → Fin 1 → ℂ) × (G.UT n → ℂ) ≃ᵐ _))
      ((volume : Measure (Fin 1 → Fin n → ℂ)).prod ((volume : Measure (Fin n → Fin 1 → ℂ)).prod volume))
      ((volume : Measure (Fin 1 → Fin n → ℂ)).prod ((volume : Measure (G.UT n → ℂ)).prod volume)) :=
    (MeasurePreserving.id _).prod (Measure.measurePreserving_swap)
  have h3a : MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) (Fin n → ℂ)) volume volume := by
    rw [volume_pi]; exact measurePreserving_funUnique volume (Fin 1)
  have h3b : MeasurePreserving (MeasurableEquiv.piCongrRight fun _ : Fin n => MeasurableEquiv.funUnique (Fin 1) ℂ)
      volume volume := by
    have := measurePreserving_pi (fun _ : Fin n => (volume : Measure (Fin 1 → ℂ))) (fun _ => (volume : Measure ℂ))
      (f := fun _ x => MeasurableEquiv.funUnique (Fin 1) ℂ x)
      (fun _ => by rw [volume_pi]; exact measurePreserving_funUnique volume (Fin 1))
    rw [volume_pi, volume_pi]
    exact this
  have h3 := h3a.prod ((MeasurePreserving.id (volume : Measure (G.UT n → ℂ))).prod h3b)
  have h4 := (MeasurePreserving.id (volume : Measure (Fin n → ℂ))).prod (shearU_mp n)
  exact (h4.comp h3).comp (h2.comp h1)

theorem muBlock_eq (β : ℂ) (n : ℕ) : G.muBlock β n =
    (Real.toNNReal (‖β‖ / (2 * Real.pi)) ^ (Fintype.card (Fin n) + (Fintype.card (G.UT n) + Fintype.card (Fin n)))) •
      ((volume : Measure (Fin n → ℂ)).prod ((volume : Measure (G.UT n → ℂ)).prod (volume : Measure (Fin n → ℂ)))) := by
  unfold G.muBlock
  simp only [muPi_eq]
  simp only [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  congr 1
  rw [pow_add, pow_add]
  ring

theorem omBlock_eq (β : ℂ) (n : ℕ) (t c : ℂ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (Φ : G.Mat (n + 1) → V) :
    G.OmBlock β n Φ t c = (((Real.toNNReal (‖β‖ / (2 * Real.pi)) ^ (Fintype.card (Fin n) +
        (Fintype.card (G.UT n) + Fintype.card (Fin n))) : NNReal) : ℝ) : ℂ) •
      U.PhiTop (p := n + 1) (s := 0) β (σB n) (Fub.dQ (fun _ : Fin n => t) (fun _ : Fin 1 => c)) Φ
        (fun x => x.elim0) := by
  set σh : Equiv.Perm (Fin n) := Fin.revPerm
  set σb : Equiv.Perm (Fin 1) := 1

  let gA : U.XiH n 1 σh × U.XiH 1 0 σb → V := fun y =>
    U.psiH β σb y.2 • (U.psiH β σh y.1 • Φ (U.ZjH (p := n) (s := 1) σh (fun _ => t) y.1
      (U.ZjH (p := 1) (s := 0) σb (fun _ => c) y.2 (fun x => x.elim0))))
  have hA : (fun η : U.XiH (n + 1) 0 (σB n) => U.psiH β (σB n) η •
      Φ (U.ZjH (p := n + 1) (s := 0) (σB n) (Fub.dQ (fun _ : Fin n => t) (fun _ : Fin 1 => c)) η
        (fun x => x.elim0))) = gA ∘ Fub.xiE σh σb := by
    funext η
    obtain ⟨⟨a0, b0⟩, v, u⟩ := η
    rw [Function.comp_apply, Fub.xiE_apply]
    simp only [gA, U.ZjH, Dx2.SL.zj_zero]
    rw [Fub.zj_split σh σb (fun _ => t) (fun _ => c) v u,
      Fub.psiH_split σh σb β a0 b0 (Dx2.SL.uniqueT 1).toInhabited.default v u, mul_comm]
    exact (smul_smul _ _ _).symm
  have s1 := Fub.sfXiH n 1 σh
  have hP1 : U.PhiTop (p := n + 1) (s := 0) β (σB n) (Fub.dQ (fun _ : Fin n => t) (fun _ : Fin 1 => c)) Φ
      (fun x => x.elim0) = ∫ y, gA y ∂(volume.prod volume) := by
    unfold U.PhiTop
    rw [show U.muXiH (n + 1) 0 (σB n) = volume from rfl, hA]
    exact (Fub.xiE_mp σh σb).integral_comp' gA

  let eB : U.XiH n 1 σh × U.XiH 1 0 σb ≃ᵐ U.XiH n 1 σh :=
    MeasurableEquiv.prodComm.trans (Dx2.SL.dropE (U.XiH 1 0 σb) (U.XiH n 1 σh))
  have hT1 := isProbabilityMeasure_rank_one_torus
  have heB : MeasurePreserving eB (volume.prod volume) volume :=
    (Dx2.SL.dropE_mp (U.XiH 1 0 σb) (U.XiH n 1 σh) volume volume).comp Measure.measurePreserving_swap
  let gB : U.XiH n 1 σh → V := fun x =>
    U.psiH β σh x • Φ (U.ZjH (p := n) (s := 1) σh (fun _ => t) x (Matrix.of fun _ _ => c))
  have hB : gA = gB ∘ eB := by
    funext y
    obtain ⟨x, y2⟩ := y
    simp only [gA, gB, Function.comp_apply]
    rw [character_rank_one_eq_one, one_smul, corner_matrix_rank_one_eq]
    rfl
  have hP2 : ∫ y, gA y ∂(volume.prod volume) = ∫ x, gB x := by
    rw [hB]; exact heB.integral_comp' gB

  let eC : U.XiH n 1 σh ≃ᵐ ((Fin 1 → Fin n → ℂ) × (Fin n → Fin 1 → ℂ)) × (G.UT n → ℂ) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (Dx2.SL.dropE (U.LW σh → ℂ) (G.UT n → ℂ))
  have hL : IsProbabilityMeasure (volume : Measure (U.LW σh → ℂ)) := probE
  have s2 : SigmaFinite (volume : Measure (G.UT n → ℂ)) := inferInstance
  have s2' : SigmaFinite (volume : Measure (U.LW σh → ℂ)) := inferInstance
  have s3 : SFinite (volume : Measure ((U.LW σh → ℂ) × (G.UT n → ℂ))) := by
    rw [Measure.volume_eq_prod]; infer_instance
  have s4a : SigmaFinite (volume : Measure (Fin 1 → Fin n → ℂ)) := inferInstance
  have s4b : SigmaFinite (volume : Measure (Fin n → Fin 1 → ℂ)) := inferInstance
  have s4 : SFinite (volume : Measure ((Fin 1 → Fin n → ℂ) × (Fin n → Fin 1 → ℂ))) := by
    rw [Measure.volume_eq_prod]; infer_instance
  have heC : MeasurePreserving eC volume volume :=
    (MeasurePreserving.id _).prod (Dx2.SL.dropE_mp (U.LW σh → ℂ) (G.UT n → ℂ) volume volume)
  let gC : ((Fin 1 → Fin n → ℂ) × (Fin n → Fin 1 → ℂ)) × (G.UT n → ℂ) → V := fun q =>
    G.psi β (U.supS (G.upper q.2) + U.cornerA q.1.1 + U.cornerB q.1.2) •
      Φ (U.Zj q.1.1 q.1.2 (G.ptLong n t * G.upper q.2) (Matrix.of fun _ _ => c))
  have hC : gB = gC ∘ eC := by
    funext x
    obtain ⟨⟨a, b⟩, v, u⟩ := x
    simp only [gB, gC, Function.comp_apply]
    have e1 : U.headH σh (fun _ => t) v u = G.ptLong n t * G.upper u := by
      unfold U.headH
      rw [lowW_of_empty, Matrix.mul_one, ← hMat_rev]
      rfl
    unfold U.psiH U.ZjH
    rw [lowW_of_empty, Matrix.mul_one, Matrix.mul_nonsing_inv _ (Dx2.SL.isUnit_wP σh), Dx2.SL.subS_one, zero_add,
      e1]
    rfl
  have hP3 : ∫ x, gB x = ∫ q, gC q := by
    rw [hC]; exact heC.integral_comp' gC

  have hD : gC = G.blockIntegrand β n Φ t c ∘ eD n := by
    funext q
    obtain ⟨⟨a, b⟩, u⟩ := q
    simp only [gC, Function.comp_apply, eD_apply, G.blockIntegrand]
    rw [chars_block, mat_block]
  have hP4 : ∫ q, gC q = ∫ q, G.blockIntegrand β n Φ t c q ∂(volume.prod (volume.prod volume)) := by
    rw [hD]; exact (eD_mp n).integral_comp' _
  rw [hP1, hP2, hP3, hP4]
  unfold G.OmBlock
  rw [muBlock_eq, integral_smul_nnreal_measure, NNReal.smul_def, ← Complex.coe_smul]

end block

end Formalism.FourierDecayAlt.P.PBJ.Om

namespace Formalism.FourierDecayAlt.P.PBJ

open Formalism.FourierDecayAlt.P.PBJ.Om

theorem nnpow_ne (β : ℂ) (hβ : β ≠ 0) (N : ℕ) :
    (((Real.toNNReal (‖β‖ / (2 * Real.pi)) ^ N : NNReal) : ℝ) : ℂ) ≠ 0 := by
  have hc : 0 < ‖β‖ / (2 * Real.pi) := div_pos (norm_pos_iff.2 hβ) (by positivity)
  rw [Ne, Complex.ofReal_eq_zero, NNReal.coe_eq_zero]
  exact pow_ne_zero _ (ne_of_gt (Real.toNNReal_pos.2 hc))

theorem long_orbital_integral_multiple : OmLongTop := by
  intro β hβ n
  refine ⟨_, nnpow_ne β hβ (Fintype.card (G.UT (n + 1))), ?_⟩
  intro σ d z V _ _ _ Φ hz hM
  obtain ⟨rfl, rfl⟩ := Fub.hMat_inj σ Fin.revPerm d (fun _ => z) (fun _ => hz) (hM.trans (hMat_rev (n + 1) z).symm)
  exact omLong_eq β n z Φ

theorem block_orbital_integral_multiple : OmBlockTop := by
  intro β hβ n
  refine ⟨_, nnpow_ne β hβ (Fintype.card (Fin n) + (Fintype.card (G.UT n) + Fintype.card (Fin n))), ?_⟩
  intro σ d t c V _ _ _ Φ ht hc hM
  have hd : ∀ i, Fub.dQ (fun _ : Fin n => t) (fun _ : Fin 1 => c) i ≠ 0 := by
    intro i
    induction i using Fin.addCases with
    | left j => simp only [Fub.dQ, Fin.addCases_left]; exact ht
    | right j => simp only [Fub.dQ, Fin.addCases_right]; exact hc
  obtain ⟨rfl, rfl⟩ := Fub.hMat_inj σ (σB n) d _ hd (hM.trans (hMat_block n t c).symm)
  exact omBlock_eq β n t c Φ

end Formalism.FourierDecayAlt.P.PBJ
