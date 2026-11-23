import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorusUOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay

noncomputable section

namespace GlobalTheory.TorusHeight

open scoped Matrix.Norms.L2Operator

theorem opNorm_le_of_shape {n q : ℕ} (X Y' : Matrix (Fin n) (Fin q) ℂ) (Y X' : Matrix (Fin q) (Fin n) ℂ)
    (d d' : Fin q → ℂ) {s : ℝ} (hs : 0 ≤ s) (hd : ∀ i, ‖d i‖ ≤ s) (hd' : ∀ i, ‖d' i‖ ≤ s) :
    (opNorm (1 + X * Matrix.diagonal d * Y + Y' * Matrix.diagonal d' * X') : ℝ) ≤
      1 + (‖X‖ * ‖Y‖ + ‖Y'‖ * ‖X'‖) * s := by
  have e : ∀ M : Matrix (Fin n) (Fin n) ℂ, (opNorm M : ℝ) = ‖M‖ := fun M => by
    rw [opNorm, coe_nnnorm]; exact (Matrix.l2_opNorm_def M).symm
  rw [e]
  have h1 : ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ => by simp
  have hD : ‖Matrix.diagonal d‖ ≤ s := by
    rw [Matrix.l2_opNorm_diagonal]; exact (pi_norm_le_iff_of_nonneg hs).2 hd
  have hD' : ‖Matrix.diagonal d'‖ ≤ s := by
    rw [Matrix.l2_opNorm_diagonal]; exact (pi_norm_le_iff_of_nonneg hs).2 hd'
  have h2 : ‖X * Matrix.diagonal d * Y‖ ≤ ‖X‖ * s * ‖Y‖ :=
    (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right
      ((Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_left hD (norm_nonneg _))) (norm_nonneg _))
  have h3 : ‖Y' * Matrix.diagonal d' * X'‖ ≤ ‖Y'‖ * s * ‖X'‖ :=
    (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right
      ((Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_left hD' (norm_nonneg _))) (norm_nonneg _))
  calc _ ≤ ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ + ‖X * Matrix.diagonal d * Y‖ + ‖Y' * Matrix.diagonal d' * X'‖ :=
        norm_add₃_le
    _ ≤ 1 + ‖X‖ * s * ‖Y‖ + ‖Y'‖ * s * ‖X'‖ := by linarith
    _ = _ := by ring

theorem le_prod_of_forall_le {q : ℕ} {c : ℝ} (hc : 0 < c) (t : Fin q → ℝ) (ht : ∀ i, c ≤ t i) (k : Fin q) :
    t k * (min 1 c) ^ (q - 1) ≤ ∏ i, t i := by
  have hm : 0 < min 1 c := lt_min one_pos hc
  rw [← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ k)]
  have hk : 0 ≤ t k := hc.le.trans (ht k)
  refine mul_le_mul_of_nonneg_left ?_ hk
  have := Finset.prod_le_prod (s := Finset.univ.erase k) (f := fun _ => min 1 c) (g := t) (fun _ _ => hm.le)
    (fun i _ => (min_le_right _ _).trans (ht i))
  simpa [Finset.prod_const, Finset.card_erase_of_mem, Finset.card_univ, Fintype.card_fin] using this

theorem norm_ofReal_sub_one (x : ℝ) : ‖(x : ℂ) - 1‖ = |x - 1| := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

theorem norm_ofReal_inv_sub_one (x : ℝ) : ‖(x : ℂ)⁻¹ - 1‖ = |x⁻¹ - 1| := by
  rw [← Complex.ofReal_inv, norm_ofReal_sub_one]

theorem height_torus_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (q : ℕ) (Xf Yf : Matrix (Fin n) (Fin q) E) (c : ℝ), 0 < c →
    ∃ (C : ℝ) (A : ℕ), ∀ (t : Fin q → ℝ), (∀ i, c ≤ t i) → ∀ a : GAd σ J, a ∈ infPts σ J →
      (∀ (w : InfinitePlace F) (τ : EmbOver E w),
        GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = (1 + (Xf).map τ.1 * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ) - 1) * (Formalism.UG.cT (σ : E →+* E) Yf * J).map τ.1 +
          (Yf).map τ.1 * Matrix.diagonal (fun i => ((t i : ℝ) : ℂ)⁻¹ - 1) * (Formalism.UG.cT (σ : E →+* E) Xf * J).map τ.1) ∧
        GlobalTheory.Orb.archMat σ J τ (projArch σ J w a⁻¹) = (1 + (Xf).map τ.1 * Matrix.diagonal (fun i => (((fun i => (t i)⁻¹) i : ℝ) : ℂ) - 1) * (Formalism.UG.cT (σ : E →+* E) Yf * J).map τ.1 +
          (Yf).map τ.1 * Matrix.diagonal (fun i => (((fun i => (t i)⁻¹) i : ℝ) : ℂ)⁻¹ - 1) * (Formalism.UG.cT (σ : E →+* E) Xf * J).map τ.1)) →
      (height σ J a : ℝ) ≤ C * (1 + ∏ i, t i) ^ A := by
  intro F E _ _ _ _ _ σ hcm n J q Xf Yf c hc
  classical
  have hm : 0 < min 1 c := lt_min one_pos hc
  set c0 : ℝ := ((min 1 c) ^ (q - 1))⁻¹ + c⁻¹ + 1 with hc0
  have hc0' : 1 ≤ c0 := by
    have : 0 ≤ ((min 1 c) ^ (q - 1))⁻¹ := inv_nonneg.2 (pow_nonneg hm.le _)
    have : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
    linarith
  let τ0 : ∀ w : InfinitePlace F, EmbOver E w := fun w => Classical.arbitrary _
  let K : InfinitePlace F → ℝ := fun w =>
    ‖(Xf).map (τ0 w).1‖ * ‖(Formalism.UG.cT (σ : E →+* E) Yf * J).map (τ0 w).1‖ +
      ‖(Yf).map (τ0 w).1‖ * ‖(Formalism.UG.cT (σ : E →+* E) Xf * J).map (τ0 w).1‖
  have hK : ∀ w, 0 ≤ K w := fun w => by positivity
  refine ⟨∏ w, (1 + K w * c0), Fintype.card (InfinitePlace F), fun t ht a ha hA => ?_⟩
  set P := ∏ i, t i with hP'
  have hP : 0 ≤ P := Finset.prod_nonneg fun i _ => hc.le.trans (ht i)
  have hs : 0 ≤ c0 * (1 + P) := by positivity
  have hs1 : ∀ k, |t k - 1| ≤ c0 * (1 + P) := fun k => by
    have htk : 0 ≤ t k := hc.le.trans (ht k)
    have h1 := le_prod_of_forall_le hc t ht k
    have hpow : 0 < (min 1 c) ^ (q - 1) := pow_pos hm _
    have h2 : t k ≤ ((min 1 c) ^ (q - 1))⁻¹ * P := by
      rw [← div_eq_inv_mul, le_div_iff₀ hpow]; exact h1
    have h3 : |t k - 1| ≤ t k + 1 := by
      rw [abs_le]; constructor <;> linarith
    have h4 : ((min 1 c) ^ (q - 1))⁻¹ * P ≤ c0 * P := by
      apply mul_le_mul_of_nonneg_right _ hP
      have : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
      linarith
    nlinarith
  have hs2 : ∀ k, |(t k)⁻¹ - 1| ≤ c0 * (1 + P) := fun k => by
    have htk : 0 < t k := hc.trans_le (ht k)
    have h1 : (t k)⁻¹ ≤ c⁻¹ := inv_anti₀ hc (ht k)
    have h0 : 0 ≤ (t k)⁻¹ := inv_nonneg.2 htk.le
    have h3 : |(t k)⁻¹ - 1| ≤ (t k)⁻¹ + 1 := by
      rw [abs_le]; constructor <;> linarith
    have : 0 ≤ ((min 1 c) ^ (q - 1))⁻¹ := inv_nonneg.2 (pow_nonneg hm.le _)
    nlinarith

  have hfin : ∀ v, htFin F v (matHom _ σ J (proj σ J v a)) = 1 := fun v => by
    rw [mem_infPts_iff_forall.1 ha v, map_one]
    exact htOf_eq_one.2 ⟨by simpa using normFin_one_le (E := E) F v, by simpa using normFin_one_le (E := E) F v⟩

  have hinf : ∀ w, (htInf F w (matHom _ σ J (projArch σ J w a)) : ℝ) ≤ (1 + K w * c0) * (1 + P) := by
    intro w
    obtain ⟨h1, h2⟩ := hA w (τ0 w)
    have e1 : normInf F w ((matHom _ σ J (projArch σ J w a) : GL (Fin n) (w.Completion ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E)) = opNorm (GlobalTheory.Orb.archMat σ J (τ0 w) (projArch σ J w a)) :=
      normInf_eq_opNorm hcm (τ0 w) _
    have e2 : normInf F w (((matHom _ σ J (projArch σ J w a))⁻¹ : GL (Fin n) (w.Completion ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E)) =
        opNorm (GlobalTheory.Orb.archMat σ J (τ0 w) (projArch σ J w a⁻¹)) := by
      rw [← map_inv, ← map_inv]; exact normInf_eq_opNorm hcm (τ0 w) _
    have B1 : (opNorm (GlobalTheory.Orb.archMat σ J (τ0 w) (projArch σ J w a)) : ℝ) ≤ 1 + K w * (c0 * (1 + P)) := by
      rw [h1]
      refine (opNorm_le_of_shape _ _ _ _ _ _ hs (fun i => ?_) (fun i => ?_)).trans le_rfl
      · rw [norm_ofReal_sub_one]; exact hs1 i
      · rw [norm_ofReal_inv_sub_one]; exact hs2 i
    have B2 : (opNorm (GlobalTheory.Orb.archMat σ J (τ0 w) (projArch σ J w a⁻¹)) : ℝ) ≤ 1 + K w * (c0 * (1 + P)) := by
      rw [h2]
      refine (opNorm_le_of_shape _ _ _ _ _ _ hs (fun i => ?_) (fun i => ?_)).trans le_rfl
      · rw [norm_ofReal_sub_one]; exact hs2 i
      · rw [norm_ofReal_inv_sub_one, inv_inv]; exact hs1 i
    have hfin' : (1 + K w * (c0 * (1 + P))) ≤ (1 + K w * c0) * (1 + P) := by
      have := hK w; nlinarith
    have hone : (1 : ℝ) ≤ (1 + K w * c0) * (1 + P) := by
      have := hK w; nlinarith
    simp only [htInf, htOf, NNReal.coe_max, NNReal.coe_one]
    rw [e1, e2]
    exact max_le hone (max_le (B1.trans hfin') (B2.trans hfin'))
  have hh : (height σ J a : ℝ) = ∏ w, (htInf F w (matHom _ σ J (projArch σ J w a)) : ℝ) := by
    rw [height_eq]
    simp only [hfin, finprod_one, mul_one, NNReal.coe_prod]
  rw [hh]
  calc _ ≤ ∏ w, ((1 + K w * c0) * (1 + P)) :=
        Finset.prod_le_prod (fun _ _ => NNReal.coe_nonneg _) (fun w _ => hinf w)
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

end GlobalTheory.TorusHeight
