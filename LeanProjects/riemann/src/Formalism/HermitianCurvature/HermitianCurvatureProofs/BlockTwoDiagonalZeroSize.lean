import Formalism.HermitianCurvature.HermitianCurvatureProofs.KloostDensOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopCellsOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnitaryInvariantGaussian

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBJ.Frz

open MeasureTheory Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

abbrev AB (p : ℕ) : Type := (Fin 1 → Fin p → ℂ) × (Fin p → Fin 1 → ℂ)

def gI (β c : ℂ) {p : ℕ} (Ψ : G.Mat (p + 1) → V) (H : G.Mat p) (y : AB p) : V :=
  G.psi β (cornerA y.1 + cornerB y.2) • Ψ (Zj y.1 y.2 (Matrix.of H) (Matrix.of fun _ _ => c))

def Psc (β c : ℂ) {p : ℕ} (Ψ : G.Mat (p + 1) → V) (H : G.Mat p) : V := ∫ y, gI β c Ψ H y

theorem block_two_one_lower_zero {p : ℕ} (a : Fin 0 → Fin p → ℂ) :
    (blk2 (1 : Matrix (Fin p) (Fin p) ℂ) 0 (Matrix.of a) 1 : Matrix (Fin (p + 0)) (Fin (p + 0)) ℂ) = 1 := by
  ext i j
  obtain ⟨i', rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j', rfl⟩ := finSumFinEquiv.surjective j
  rcases i' with i' | i'
  · rcases j' with j' | j'
    · simp [blk2, Matrix.one_apply]
    · exact j'.elim0
  · exact i'.elim0

theorem block_two_one_upper_zero {p : ℕ} (b : Fin p → Fin 0 → ℂ) :
    (blk2 (1 : Matrix (Fin p) (Fin p) ℂ) (Matrix.of b) 0 1 : Matrix (Fin (p + 0)) (Fin (p + 0)) ℂ) = 1 := by
  ext i j
  obtain ⟨i', rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j', rfl⟩ := finSumFinEquiv.surjective j
  rcases i' with i' | i'
  · rcases j' with j' | j'
    · simp [blk2, Matrix.one_apply]
    · exact j'.elim0
  · exact i'.elim0

theorem block_two_diagonal_zero_size {p : ℕ} (H : Matrix (Fin p) (Fin p) ℂ) (Z : Matrix (Fin 0) (Fin 0) ℂ) :
    (blk2 H 0 0 Z : Matrix (Fin (p + 0)) (Fin (p + 0)) ℂ) = H := by
  ext i j
  obtain ⟨i', rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j', rfl⟩ := finSumFinEquiv.surjective j
  rcases i' with i' | i'
  · rcases j' with j' | j'
    · simp [blk2]
      rfl
    · exact j'.elim0
  · exact i'.elim0

theorem zj_zero {p : ℕ} (a : Fin 0 → Fin p → ℂ) (b : Fin p → Fin 0 → ℂ) (H : Matrix (Fin p) (Fin p) ℂ)
    (Z : Matrix (Fin 0) (Fin 0) ℂ) : (Zj a b H Z : Matrix (Fin (p + 0)) (Fin (p + 0)) ℂ) = H := by
  unfold Zj
  rw [block_two_one_lower_zero, block_two_one_upper_zero, block_two_diagonal_zero_size, Matrix.one_mul, Matrix.mul_one]

theorem cornerA_zero {p : ℕ} (a : Fin 0 → Fin p → ℂ) : cornerA a = 0 := by
  unfold cornerA; simp

theorem cornerB_zero {p : ℕ} (b : Fin p → Fin 0 → ℂ) : cornerB b = 0 := by
  unfold cornerB; simp

theorem vol_univ_zero (p : ℕ) : (volume : Measure ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))).real Set.univ = 1 := by
  rw [Measure.volume_eq_prod, measureReal_def, ← Set.univ_prod_univ, Measure.prod_prod]
  rw [volume_pi, volume_pi, Measure.pi_univ, Measure.pi_univ]
  simp [volume_pi, Measure.pi_univ]

end Formalism.FourierDecayAlt.P.PBJ.Frz

namespace Formalism.FourierDecayAlt.P.PBJ.Frz

open MeasureTheory Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

instance sfAB (p : ℕ) : SigmaFinite (volume : Measure (AB p)) := by
  have h1 : SigmaFinite (volume : Measure (Fin 1 → Fin p → ℂ)) := inferInstance
  have h2 : SigmaFinite (volume : Measure (Fin p → Fin 1 → ℂ)) := inferInstance
  rw [Measure.volume_eq_prod]; exact Measure.prod.instSigmaFinite

instance sfVU {p : ℕ} (σ : Equiv.Perm (Fin p)) : SigmaFinite (volume : Measure ((LW σ → ℂ) × (G.UT p → ℂ))) := by
  have h1 : SigmaFinite (volume : Measure (LW σ → ℂ)) := inferInstance
  have h2 : SigmaFinite (volume : Measure (G.UT p → ℂ)) := inferInstance
  rw [Measure.volume_eq_prod]; exact Measure.prod.instSigmaFinite

theorem decay0 {n : ℕ} {Ψ : G.Mat n → V} (hΨ : KCls Ψ) (E : ℝ) (hE : 0 ≤ E) :
    ∃ K : ℝ, DecayAll 0 (fun _ => E) K Ψ := by
  obtain ⟨hs, hc, _⟩ := hΨ
  have hcont : Continuous Ψ := hs.continuous
  obtain ⟨M, hM⟩ := hcont.bounded_above_of_compact_support hc
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.exists_norm_le
  set R' := max R 0 with hR'
  set M' := max M 0 with hM'
  refine ⟨M' * (1 + R') ^ E, ?_, ?_⟩
  · rw [Nat.cast_zero]; exact contDiff_zero.2 hcont
  · intro i hi Z
    have hi0 : i = 0 := Nat.le_zero.1 hi
    subst hi0
    rw [norm_iteratedFDeriv_zero]
    have h1 : (0 : ℝ) < 1 + ‖Z‖ := by positivity
    have hpow : (1 + ‖Z‖) ^ E * (1 + ‖Z‖) ^ (-E) = 1 := by
      rw [Real.rpow_neg h1.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos h1 E).ne']
    by_cases hZ : Z ∈ tsupport Ψ
    · have hZR : ‖Z‖ ≤ R' := le_trans (hR Z hZ) (le_max_left _ _)
      have hle : (1 + ‖Z‖) ^ E ≤ (1 + R') ^ E := Real.rpow_le_rpow h1.le (by linarith) hE
      have hneg : 0 ≤ (1 + ‖Z‖) ^ (-E) := (Real.rpow_pos_of_pos h1 _).le
      calc ‖Ψ Z‖ ≤ M' := le_trans (hM Z) (le_max_left _ _)
        _ = M' * ((1 + ‖Z‖) ^ E * (1 + ‖Z‖) ^ (-E)) := by rw [hpow, mul_one]
        _ ≤ M' * ((1 + R') ^ E * (1 + ‖Z‖) ^ (-E)) := by
          apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
          exact mul_le_mul_of_nonneg_right hle hneg
        _ = M' * (1 + R') ^ E * (1 + ‖Z‖) ^ (-E) := by ring
    · rw [image_eq_zero_of_notMem_tsupport hZ, norm_zero]
      have : 0 ≤ (1 + R') ^ E := Real.rpow_nonneg (by positivity) E
      have : 0 ≤ (1 + ‖Z‖) ^ (-E) := (Real.rpow_pos_of_pos h1 _).le
      have : 0 ≤ M' := le_max_right _ _
      positivity

theorem integrable_one [CompleteSpace V] (β c : ℂ) {p : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ)
    (hd : ∀ i, d i ≠ 0) {Ψ : G.Mat (p + 1) → V} (hΨ : KCls Ψ) :
    Integrable (fun η : XiH p 1 σ => psiH β σ η • Ψ (ZjH σ d η (fun _ _ => c))) (muXiH p 1 σ) := by
  set E : ℝ := 10 * ((p + 1 : ℕ) : ℝ) ^ 3 + 1 with hEdef
  have hE : 0 ≤ E := by positivity
  obtain ⟨Cst, hC⟩ := Formalism.FourierDecayAlt.P.top_cells p 1 β σ d hd le_rfl 0 (fun _ => E) (by
    intro i _
    have hn : (0 : ℝ) < ((p + 1 : ℕ) : ℝ) := by positivity
    rw [lt_div_iff₀ (by positivity)]
    nlinarith)
  obtain ⟨K, hK⟩ := decay0 hΨ E hE
  exact (hC V Ψ K hK).1 (fun _ _ => c)

theorem psiH_one (β : ℂ) {p : ℕ} (σ : Equiv.Perm (Fin p)) (η : XiH p 1 σ) :
    psiH β σ η = G.psi β (subS (wP σ * lowW σ η.2.1 * (wP σ)⁻¹) + supS (G.upper η.2.2)) *
      G.psi β (cornerA η.1.1 + cornerB η.1.2) := by
  unfold psiH
  rw [← Formalism.FourierDecayAlt.P.G8.psi_add]
  congr 1
  ring

theorem psiH_zero (β : ℂ) {p : ℕ} (σ : Equiv.Perm (Fin p)) (η : XiH p 0 σ) :
    psiH β σ η = G.psi β (subS (wP σ * lowW σ η.2.1 * (wP σ)⁻¹) + supS (G.upper η.2.2)) := by
  unfold psiH
  rw [cornerA_zero, cornerB_zero, add_zero, add_zero]

theorem phiTop_freeze [CompleteSpace V] (β c : ℂ) {p : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ)
    (hd : ∀ i, d i ≠ 0) {Ψ : G.Mat (p + 1) → V} (hΨ : KCls Ψ) :
    PhiTop (p := p) (s := 1) β σ d Ψ (fun _ _ => c) =
      PhiTop (p := p) (s := 0) β σ d (Psc β c Ψ) (fun x => x.elim0) := by
  have hint := integrable_one β c σ d hd hΨ
  set X : (LW σ → ℂ) × (G.UT p → ℂ) → ℂ :=
    fun vu => G.psi β (subS (wP σ * lowW σ vu.1 * (wP σ)⁻¹) + supS (G.upper vu.2)) with hX
  have eL : (fun η : XiH p 1 σ => psiH β σ η • Ψ (ZjH σ d η (fun _ _ => c))) =
      fun η => X η.2 • gI β c Ψ (headH σ d η.2.1 η.2.2) η.1 := by
    funext η
    rw [psiH_one, mul_smul]
    rfl
  have eR : (fun η : XiH p 0 σ => psiH β σ η • Psc β c Ψ (ZjH σ d η (fun x => x.elim0))) =
      fun η => X η.2 • Psc β c Ψ (headH σ d η.2.1 η.2.2) := by
    funext η
    rw [psiH_zero]
    unfold ZjH
    rw [zj_zero]
  unfold PhiTop muXiH
  rw [eL, eR]
  rw [eL] at hint
  unfold muXiH at hint
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [integral_prod_symm _ hint]
  rw [Measure.volume_eq_prod (α := (Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))]
  rw [integral_fun_snd (fun vu : (LW σ → ℂ) × (G.UT p → ℂ) => X vu • Psc β c Ψ (headH σ d vu.1 vu.2))]
  rw [vol_univ_zero, one_smul]
  congr 1
  funext vu
  show ∫ x, X vu • gI β c Ψ (headH σ d vu.1 vu.2) x = X vu • ∫ x, gI β c Ψ (headH σ d vu.1 vu.2) x
  exact integral_smul _ _

end Formalism.FourierDecayAlt.P.PBJ.Frz

namespace Formalism.FourierDecayAlt.P.PBJ.Frz

open MeasureTheory Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem zj_apply_ll {p : ℕ} (a : Fin 1 → Fin p → ℂ) (b : Fin p → Fin 1 → ℂ) (H : Matrix (Fin p) (Fin p) ℂ)
    (C : Matrix (Fin 1) (Fin 1) ℂ) (i j : Fin p) : Zj a b H C (Fin.castAdd 1 i) (Fin.castAdd 1 j) = H i j := by
  rw [Formalism.FourierDecayAlt.P.level_z_affine]
  simp [blk2]

theorem zj_apply_lr {p : ℕ} (a : Fin 1 → Fin p → ℂ) (b : Fin p → Fin 1 → ℂ) (H : Matrix (Fin p) (Fin p) ℂ)
    (C : Matrix (Fin 1) (Fin 1) ℂ) (i : Fin p) : Zj a b H C (Fin.castAdd 1 i) (Fin.natAdd p 0) = (H * Matrix.of b) i 0 := by
  rw [Formalism.FourierDecayAlt.P.level_z_affine]
  simp [blk2]

theorem zj_apply_rl {p : ℕ} (a : Fin 1 → Fin p → ℂ) (b : Fin p → Fin 1 → ℂ) (H : Matrix (Fin p) (Fin p) ℂ)
    (C : Matrix (Fin 1) (Fin 1) ℂ) (j : Fin p) : Zj a b H C (Fin.natAdd p 0) (Fin.castAdd 1 j) = (Matrix.of a * H) 0 j := by
  rw [Formalism.FourierDecayAlt.P.level_z_affine]
  simp [blk2]

theorem det_zj {p s : ℕ} (a : Fin s → Fin p → ℂ) (b : Fin p → Fin s → ℂ) (H : Matrix (Fin p) (Fin p) ℂ)
    (C : Matrix (Fin s) (Fin s) ℂ) : (Zj a b H C).det = H.det * C.det := by
  unfold Zj
  rw [Matrix.det_mul, Matrix.det_mul, Formalism.FourierDecayAlt.P.Ux3.block2_det_lower_triangular, Formalism.FourierDecayAlt.P.Ux3.block2_det_lower_triangular,
    Formalism.FourierDecayAlt.P.Ux3.block2_det_upper_triangular]
  simp

theorem cont_detM (n : ℕ) : Continuous (fun H : G.Mat n => G.detM H) := by
  unfold G.detM
  exact Continuous.matrix_det continuous_id

theorem entry_le {n : ℕ} (Z : G.Mat n) (i j : Fin n) : ‖Z i j‖ ≤ ‖Z‖ :=
  le_trans (norm_le_pi_norm (Z i) j) (norm_le_pi_norm Z i)

theorem supp_bounds {n : ℕ} {Ψ : G.Mat n → V} (hΨ : KCls Ψ) :
    ∃ R δ : ℝ, 0 ≤ R ∧ 0 < δ ∧ ∀ Z ∈ tsupport Ψ, ‖Z‖ ≤ R ∧ δ ≤ ‖G.detM Z‖ := by
  obtain ⟨_, hc, hdet⟩ := hΨ
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.exists_norm_le
  by_cases hne : (tsupport Ψ).Nonempty
  · obtain ⟨Z₀, hZ₀, hmin⟩ := hc.isCompact.exists_isMinOn hne
      ((continuous_norm.comp (cont_detM n)).continuousOn)
    refine ⟨max R 0, ‖G.detM Z₀‖, le_max_right _ _, norm_pos_iff.2 (hdet Z₀ hZ₀), fun Z hZ => ⟨le_trans (hR Z hZ)
      (le_max_left _ _), hmin hZ⟩⟩
  · refine ⟨0, 1, le_rfl, one_pos, fun Z hZ => absurd ⟨Z, hZ⟩ hne⟩

def Sset (p : ℕ) (R δ' : ℝ) : Set (G.Mat p) := {H | ‖H‖ ≤ R ∧ δ' ≤ ‖G.detM H‖}

theorem isCompact_Sset (p : ℕ) (R δ' : ℝ) : IsCompact (Sset p R δ') := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact (isClosed_le continuous_norm continuous_const).inter
      (isClosed_le continuous_const (continuous_norm.comp (cont_detM p)))
  · exact (Metric.isBounded_closedBall (x := (0 : G.Mat p)) (r := R)).subset fun H hH => by
      simpa [Metric.mem_closedBall, dist_zero_right] using hH.1

theorem inv_bound (p : ℕ) (R δ' : ℝ) (hδ : 0 < δ') : ∃ M : ℝ, 0 ≤ M ∧
    ∀ H ∈ Sset p R δ', ∀ i j, ‖((Matrix.of H)⁻¹ : Matrix (Fin p) (Fin p) ℂ) i j‖ ≤ M := by
  have hcont : ∀ i j, ContinuousOn (fun H : G.Mat p => ((Matrix.of H)⁻¹ : Matrix (Fin p) (Fin p) ℂ) i j)
      (Sset p R δ') := by
    intro i j
    have e : (fun H : G.Mat p => ((Matrix.of H)⁻¹ : Matrix (Fin p) (Fin p) ℂ) i j) =
        fun H => (G.detM H)⁻¹ * (Matrix.of H).adjugate i j := by
      funext H
      rw [Matrix.inv_def, Ring.inverse_eq_inv']
      rfl
    rw [e]
    refine ContinuousOn.mul ?_ ((Continuous.matrix_adjugate continuous_id).matrix_elem i j).continuousOn
    refine (cont_detM p).continuousOn.inv₀ fun H hH => ?_
    exact norm_pos_iff.1 (lt_of_lt_of_le hδ hH.2)
  have hb : ∀ i j, ∃ C : ℝ, ∀ H ∈ Sset p R δ', ‖((Matrix.of H)⁻¹ : Matrix (Fin p) (Fin p) ℂ) i j‖ ≤ C :=
    fun i j => (isCompact_Sset p R δ').exists_bound_of_continuousOn (hcont i j)
  choose C hC using hb
  refine ⟨∑ i, ∑ j, max (C i j) 0, by positivity, fun H hH i j => ?_⟩
  refine le_trans (hC i j H hH) (le_trans (le_max_left _ 0) ?_)
  have h1 : max (C i j) 0 ≤ ∑ j', max (C i j') 0 :=
    Finset.single_le_sum (f := fun j' => max (C i j') 0) (fun _ _ => le_max_right _ _) (Finset.mem_univ j)
  have h2 : ∑ j', max (C i j') 0 ≤ ∑ i', ∑ j', max (C i' j') 0 :=
    Finset.single_le_sum (f := fun i' => ∑ j', max (C i' j') 0)
      (fun _ _ => Finset.sum_nonneg fun _ _ => le_max_right _ _) (Finset.mem_univ i)
  exact le_trans h1 h2

theorem gI_ne {β c : ℂ} {p : ℕ} {Ψ : G.Mat (p + 1) → V} {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    (hb : ∀ Z ∈ tsupport Ψ, ‖Z‖ ≤ R ∧ δ ≤ ‖G.detM Z‖) {H : G.Mat p} {y : AB p} (hne : gI β c Ψ H y ≠ 0) :
    H ∈ Sset p R (δ / ‖c‖) ∧ (∀ j, ‖(Matrix.of y.1 * Matrix.of H) 0 j‖ ≤ R) ∧
      ∀ i, ‖(Matrix.of H * Matrix.of y.2) i 0‖ ≤ R := by
  have hΨne : Ψ (Zj y.1 y.2 (Matrix.of H) (Matrix.of fun _ _ => c)) ≠ 0 := by
    intro h; apply hne; unfold gI; rw [h, smul_zero]
  obtain ⟨h1, h2⟩ := hb _ (subset_tsupport _ hΨne)
  set Z : G.Mat (p + 1) := Zj y.1 y.2 (Matrix.of H) (Matrix.of fun _ _ => c) with hZ
  have hdet : G.detM Z = G.detM H * c := by
    unfold G.detM
    rw [hZ]
    show (Zj y.1 y.2 (Matrix.of H) (Matrix.of fun _ _ => c)).det = _
    rw [det_zj]
    simp [Matrix.det_unique]
  refine ⟨⟨?_, ?_⟩, fun j => ?_, fun i => ?_⟩
  · refine (pi_norm_le_iff_of_nonneg hR).2 fun i => (pi_norm_le_iff_of_nonneg hR).2 fun j => ?_
    have := entry_le Z (Fin.castAdd 1 i) (Fin.castAdd 1 j)
    rw [hZ, zj_apply_ll] at this
    exact le_trans this h1
  · by_cases hc : c = 0
    · exfalso
      rw [hdet, hc, mul_zero, norm_zero] at h2
      exact absurd h2 (not_le.2 hδ)
    · rw [div_le_iff₀ (norm_pos_iff.2 hc), ← norm_mul, ← hdet]; exact h2
  · have := entry_le Z (Fin.natAdd p 0) (Fin.castAdd 1 j)
    rw [hZ, zj_apply_rl] at this
    exact le_trans this h1
  · have := entry_le Z (Fin.castAdd 1 i) (Fin.natAdd p 0)
    rw [hZ, zj_apply_lr] at this
    exact le_trans this h1

end Formalism.FourierDecayAlt.P.PBJ.Frz

namespace Formalism.FourierDecayAlt.P.PBJ.Frz

open MeasureTheory Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem y_bound {β c : ℂ} {p : ℕ} {Ψ : G.Mat (p + 1) → V} {R δ M : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) (hc : c ≠ 0)
    (hb : ∀ Z ∈ tsupport Ψ, ‖Z‖ ≤ R ∧ δ ≤ ‖G.detM Z‖) (hM0 : 0 ≤ M)
    (hM : ∀ H ∈ Sset p R (δ / ‖c‖), ∀ i j, ‖((Matrix.of H)⁻¹ : Matrix (Fin p) (Fin p) ℂ) i j‖ ≤ M)
    {H : G.Mat p} {y : AB p} (hne : gI β c Ψ H y ≠ 0) : ‖y‖ ≤ p * R * M := by
  obtain ⟨hS, ha, hbb⟩ := gI_ne hR hδ hb hne
  have hpos : 0 < δ / ‖c‖ := div_pos hδ (norm_pos_iff.2 hc)
  have hdet : IsUnit (Matrix.of H).det :=
    isUnit_iff_ne_zero.2 (norm_pos_iff.1 (lt_of_lt_of_le hpos hS.2))
  have hRM : 0 ≤ (p : ℝ) * R * M := by positivity
  rw [norm_prod_le_iff]
  constructor
  · refine (pi_norm_le_iff_of_nonneg hRM).2 fun i => (pi_norm_le_iff_of_nonneg hRM).2 fun j => ?_
    have e : y.1 i j = ∑ k, (Matrix.of y.1 * Matrix.of H) i k * ((Matrix.of H)⁻¹ : Matrix (Fin p) (Fin p) ℂ) k j := by
      rw [← Matrix.mul_apply, Matrix.mul_nonsing_inv_cancel_right _ _ hdet]; rfl
    rw [e]
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    calc ‖∑ k, (Matrix.of y.1 * Matrix.of H) 0 k * ((Matrix.of H)⁻¹ : Matrix (Fin p) (Fin p) ℂ) k j‖
        ≤ ∑ k, ‖(Matrix.of y.1 * Matrix.of H) 0 k * ((Matrix.of H)⁻¹ : Matrix (Fin p) (Fin p) ℂ) k j‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _k : Fin p, R * M := Finset.sum_le_sum fun k _ => by
          rw [norm_mul]; exact mul_le_mul (ha k) (hM H hS k j) (norm_nonneg _) hR
      _ = p * R * M := by simp; ring
  · refine (pi_norm_le_iff_of_nonneg hRM).2 fun i => (pi_norm_le_iff_of_nonneg hRM).2 fun j => ?_
    have e : y.2 i j = ∑ k, ((Matrix.of H)⁻¹ : Matrix (Fin p) (Fin p) ℂ) i k * (Matrix.of H * Matrix.of y.2) k j := by
      rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul_cancel_left _ _ hdet]; rfl
    rw [e]
    have hj : j = 0 := Subsingleton.elim j 0
    subst hj
    calc ‖∑ k, ((Matrix.of H)⁻¹ : Matrix (Fin p) (Fin p) ℂ) i k * (Matrix.of H * Matrix.of y.2) k 0‖
        ≤ ∑ k, ‖((Matrix.of H)⁻¹ : Matrix (Fin p) (Fin p) ℂ) i k * (Matrix.of H * Matrix.of y.2) k 0‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _k : Fin p, R * M := Finset.sum_le_sum fun k _ => by
          rw [norm_mul, mul_comm R M]; exact mul_le_mul (hM H hS i k) (hbb k) (norm_nonneg _) hM0
      _ = p * R * M := by simp; ring

theorem contDiff_zj (p : ℕ) (C : Matrix (Fin 1) (Fin 1) ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : G.Mat p × AB p =>
      fun (i j : Fin (p + 1)) => Zj q.2.1 q.2.2 (Matrix.of q.1) C i j) := by
  have e : (fun q : G.Mat p × AB p => fun (i j : Fin (p + 1)) => Zj q.2.1 q.2.2 (Matrix.of q.1) C i j) = fun q =>
      fun (i j : Fin (p + 1)) => blk2 (Matrix.of q.1) (Matrix.of q.1 * Matrix.of q.2.2) (Matrix.of q.2.1 * Matrix.of q.1)
        (Matrix.of q.2.1 * Matrix.of q.1 * Matrix.of q.2.2 + C) i j := by
    funext q; rw [Formalism.FourierDecayAlt.P.level_z_affine]
  rw [e]
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  obtain ⟨i', rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j', rfl⟩ := finSumFinEquiv.surjective j
  rcases i' with i' | i' <;> rcases j' with j' | j' <;>
    simp only [blk2, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.mul_apply,
      Matrix.add_apply, Matrix.of_apply] <;> fun_prop

theorem contDiff_psi (β : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (fun w : ℂ => G.psi β w) := by
  unfold G.psi
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun w : ℂ => (((β * w).re : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp (contDiff_const.mul contDiff_id))
  exact Complex.contDiff_exp.comp (contDiff_const.mul h1)

theorem contDiff_corner (p : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : G.Mat p × AB p => cornerA q.2.1 + cornerB q.2.2) := by
  by_cases hp : 0 < p
  · have e : (fun q : G.Mat p × AB p => cornerA q.2.1 + cornerB q.2.2) =
        fun q => q.2.1 0 ⟨p - 1, by omega⟩ + q.2.2 ⟨p - 1, by omega⟩ 0 := by
      funext q; simp [cornerA, cornerB, hp]
    rw [e]; fun_prop
  · have e : (fun q : G.Mat p × AB p => cornerA q.2.1 + cornerB q.2.2) = fun _ => 0 := by
      funext q; simp [cornerA, cornerB, hp]
    rw [e]; exact contDiff_const

theorem contDiff_gI (β c : ℂ) {p : ℕ} {Ψ : G.Mat (p + 1) → V} (hΨ : KCls Ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : G.Mat p × AB p => gI β c Ψ q.1 q.2) := by
  unfold gI
  exact ((contDiff_psi β).comp (contDiff_corner p)).smul (hΨ.1.comp (contDiff_zj p _))

end Formalism.FourierDecayAlt.P.PBJ.Frz

namespace Formalism.FourierDecayAlt.P.PBJ.Frz

open MeasureTheory Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open scoped Convolution

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

instance haar1 (p : ℕ) : (volume : Measure (Fin 1 → Fin p → ℂ)).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure (fun _ : Fin 1 => (volume : Measure (Fin p → ℂ)))

instance haar2 (p : ℕ) : (volume : Measure (Fin p → Fin 1 → ℂ)).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure (fun _ : Fin p => (volume : Measure (Fin 1 → ℂ)))

instance haarAB (p : ℕ) : (volume : Measure (AB p)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; exact Measure.prod.instIsAddHaarMeasure _ _

instance lfAB (p : ℕ) : IsLocallyFiniteMeasure (volume : Measure (AB p)) :=
  isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts

theorem contDiff_Psc [CompleteSpace V] (β c : ℂ) {p : ℕ} {Ψ : G.Mat (p + 1) → V} (hΨ : KCls Ψ) (hc : c ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (Psc β c Ψ) := by
  obtain ⟨R, δ, hR, hδ, hb⟩ := supp_bounds hΨ
  obtain ⟨M, hM0, hM⟩ := inv_bound p R (δ / ‖c‖) (div_pos hδ (norm_pos_iff.2 hc))
  set k : Set (AB p) := Metric.closedBall 0 (p * R * M) with hkdef
  have hk : IsCompact k := isCompact_closedBall _ _
  set g : G.Mat p → AB p → V := fun H y => gI β c Ψ H (-y) with hgdef
  have hgs : ∀ H y, H ∈ (Set.univ : Set (G.Mat p)) → y ∉ k → g H y = 0 := by
    intro H y _ hy
    by_contra hne
    apply hy
    have := y_bound hR hδ hc hb hM0 hM hne
    rw [norm_neg] at this
    simpa [hkdef, Metric.mem_closedBall, dist_zero_right] using this
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry g) (Set.univ ×ˢ Set.univ) := by
    have h := (contDiff_gI β c hΨ).comp (contDiff_fst.prodMk contDiff_snd.neg)
    exact h.contDiffOn
  have hconv := contDiffOn_convolution_right_with_param (μ := (volume : Measure (AB p)))
    (f := fun _ : AB p => (1 : ℝ)) (ContinuousLinearMap.lsmul ℝ ℝ) isOpen_univ hk hgs
    (locallyIntegrable_const 1) hg
  rw [Set.univ_prod_univ, contDiffOn_univ] at hconv
  have hc2 := hconv.comp (contDiff_id.prodMk (contDiff_const (c := (0 : AB p))))
  have e : ((fun q : G.Mat p × AB p => ((fun _ : AB p => (1 : ℝ)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g q.1) q.2) ∘
      fun H : G.Mat p => (id H, (0 : AB p))) = Psc β c Ψ := by
    funext H
    simp only [Function.comp, id]
    rw [convolution_def]
    unfold Psc
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hgdef, zero_sub, neg_neg, ContinuousLinearMap.lsmul_apply, one_smul]
  rw [e] at hc2
  exact hc2

theorem kcls_Psc [CompleteSpace V] (β c : ℂ) {p : ℕ} {Ψ : G.Mat (p + 1) → V} (hΨ : KCls Ψ) (hc : c ≠ 0) :
    KCls (Psc β c Ψ) := by
  obtain ⟨R, δ, hR, hδ, hb⟩ := supp_bounds hΨ
  have hpos : 0 < δ / ‖c‖ := div_pos hδ (norm_pos_iff.2 hc)
  have hsupp : Function.support (Psc β c Ψ) ⊆ Sset p R (δ / ‖c‖) := by
    intro H hH
    by_contra hS
    apply hH
    have h0 : ∀ y, gI β c Ψ H y = 0 := fun y => by
      by_contra hne
      exact hS (gI_ne hR hδ hb hne).1
    show ∫ y, gI β c Ψ H y = 0
    simp [h0]
  have hcl : IsClosed (Sset p R (δ / ‖c‖)) := (isCompact_Sset p R _).isClosed
  have hts : tsupport (Psc β c Ψ) ⊆ Sset p R (δ / ‖c‖) := closure_minimal hsupp hcl
  refine ⟨contDiff_Psc β c hΨ hc, ?_, fun H hH => ?_⟩
  · exact (isCompact_Sset p R _).of_isClosed_subset (isClosed_tsupport _) hts
  · exact norm_pos_iff.1 (lt_of_lt_of_le hpos (hts hH).2)

end Formalism.FourierDecayAlt.P.PBJ.Frz

namespace Formalism.FourierDecayAlt.P.PBJ

theorem freeze_last_entry : FreezeLast := by
  intro β p V _ _ _ Ψ hΨ c hc
  refine ⟨Frz.Psc β c Ψ, Frz.kcls_Psc β c hΨ hc, fun σ d hd => ?_⟩
  exact Frz.phiTop_freeze β c σ d hd hΨ

end Formalism.FourierDecayAlt.P.PBJ
