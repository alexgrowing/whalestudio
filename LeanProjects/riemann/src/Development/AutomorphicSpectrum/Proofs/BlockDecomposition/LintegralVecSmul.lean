import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import GroundTheory.GlobalFields.TateThesis.AdeleScaling
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CountingPairs

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS PositivityTheory.AdelicQuotientData
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.UnipotentNormalizer

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem map_vec_smul {ι : Type} [Fintype ι] (a : ι → (Ad E)ˣ) :
    (vecMeasure E ι).map (fun x p => a p • x p) =
      (∏ p, ENNReal.ofReal ((GroundTheory.Global.IdeleGroup.ideleModule E (a p) : ℝ))⁻¹) • vecMeasure E ι := by
  classical
  let c : ι → NNReal := fun p => Real.toNNReal ((GroundTheory.Global.IdeleGroup.ideleModule E (a p) : ℝ))⁻¹
  have hm : ∀ p, (GroundTheory.Global.adeleMeasure E).map (fun x => a p • x) = c p • GroundTheory.Global.adeleMeasure E := fun p => by
    rw [GroundTheory.Global.map_smul_adeleMeasure]; rfl
  have : ∀ p, SigmaFinite ((GroundTheory.Global.adeleMeasure E).map (fun x => a p • x)) := fun p => by
    rw [hm]; infer_instance
  have hmeas : ∀ p, Measurable (fun x : Ad E => a p • x) := fun p =>
    (show Continuous fun x : Ad E => (a p : Ad E) * x from continuous_const_mul _).measurable
  have h := Measure.pi_map_pi (μ := fun _ : ι => GroundTheory.Global.adeleMeasure E) (f := fun p x => a p • x)
    (fun p => (hmeas p).aemeasurable)
  rw [vecMeasure, h]
  simp_rw [hm]
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [Measure.smul_apply]
  rfl

theorem lintegral_vec_smul {ι : Type} [Fintype ι] (a : ι → (Ad E)ˣ) (G : (ι → Ad E) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x, G (fun p => a p • x p) ∂vecMeasure E ι =
      (∏ p, ENNReal.ofReal ((GroundTheory.Global.IdeleGroup.ideleModule E (a p) : ℝ))⁻¹) * ∫⁻ x, G x ∂vecMeasure E ι := by
  have hf : Measurable (fun (x : ι → Ad E) p => a p • x p) := measurable_pi_lambda _ fun p =>
    (show Continuous fun x : Ad E => (a p : Ad E) * x from continuous_const_mul _).measurable.comp (measurable_pi_apply p)
  rw [← lintegral_map hG hf, map_vec_smul, lintegral_smul_measure]
  rfl

theorem conj_blkU {R : Type} [CommRing R] (D : GL (Fin k) R) (u : Fin k → Rˣ)
    (hD : D.val = diagonal fun i => (u i : R)) {r m : ℕ} (x : UnipotentBlockColumnIndex k r m → R) :
    D * blkU x * D⁻¹ = blkU (fun t => ((u t.1.1 * (u t.1.2)⁻¹ : Rˣ) : R) * x t) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  change D.val * (1 + posM Subtype.val x) = (1 + posM Subtype.val _) * D.val
  rw [hD]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply, Matrix.add_apply, mul_add, add_mul]
  congr 1
  · by_cases h : i = j
    · subst h; simp
    · simp [h]
  · simp only [posM, Matrix.sum_apply, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases h : t.1.1 = i ∧ t.1.2 = j
    · obtain ⟨rfl, rfl⟩ := h
      simp only [Matrix.single_apply_same, Units.val_mul]
      have e : ((u t.1.2)⁻¹ : Rˣ).val * (u t.1.2).val = 1 := Units.inv_mul _
      linear_combination (-(u t.1.1).val * x t) * e
    · have e : ∀ y : R, Matrix.single t.1.1 t.1.2 y i j = 0 := fun y => by
        rw [Matrix.single_apply_of_ne]; exact h
      rw [e, e]; simp

def locId (w : Pl E) : (w.adicCompletion E)ˣ →* (Ad E)ˣ := (finId E).comp (Units.map (corner (sLoc E w)))

theorem fl_torus (w : Pl E) (l : Fin k → ℤ) :
    (fl k w (Iwasawa.torusPow (w.adicCompletion E) k l)).val =
      diagonal fun i => ((locId w (Iwasawa.uniformizerUnit (w.adicCompletion E) ^ l i) : (Ad E)ˣ) : Ad E) := by
  ext i j
  change (1 : Matrix (Fin k) (Fin k) (Ad E)) i j - sFin E ((1 : Matrix (Fin k) (Fin k) (Af E)) i j) +
    sFin E ((1 : Matrix (Fin k) (Fin k) (Af E)) i j - sLoc E w ((1 : Matrix (Fin k) (Fin k) (w.adicCompletion E)) i j) +
      sLoc E w ((Iwasawa.torusPow (w.adicCompletion E) k l).val i j)) = _
  rw [Iwasawa.torusPow, Iwasawa.coe_diagGL]
  by_cases h : i = j
  · subst h
    simp only [Matrix.one_apply_eq, Matrix.diagonal_apply_eq]
    rfl
  · simp [h]

end GlobalTheory.CompanionTheory.UnipotentNormalizer

namespace GlobalTheory.CompanionTheory.UnipotentNormalizer

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

def colS (e : Fin k → ℤ) (j : ℕ) : ℤ := ∑ p : UnipotentBlockColumnIndex k j j, (e p.1.1 - e p.1.2)

def totS (e : Fin k → ℤ) (d : ℕ) : ℤ := ∑ i ∈ Finset.range d, colS e (k - (i + 1))

theorem prod_ofReal_zpow {ι : Type} (s : Finset ι) {q : ℝ} (hq : 0 < q) (e : ι → ℤ) :
    ∏ p ∈ s, ENNReal.ofReal (q ^ e p) = ENNReal.ofReal (q ^ ∑ p ∈ s, e p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hq.ne', ENNReal.ofReal_mul (zpow_nonneg hq.le _)]

theorem sFinite_nuD (d : ℕ) : SFinite (nuD E k d) := by
  induction d with
  | zero => change SFinite (Measure.dirac _); infer_instance
  | succ d ih => change SFinite (Measure.map _ _); infer_instance

theorem measurable_blkMul (j : ℕ) : Measurable (fun p : (UnipotentBlockColumnIndex k j j → Ad E) × GA E k => blkU p.1 * p.2) :=
  ((continuous_posU _).measurable.comp measurable_fst).mul measurable_snd

theorem nuD_conj (t : GA E k) (u : Fin k → (Ad E)ˣ) (ht : t.val = diagonal fun i => (u i : Ad E)) {q : ℝ} (hq : 0 < q)
    (e : Fin k → ℤ) (hmod : ∀ a b, ((GroundTheory.Global.IdeleGroup.ideleModule E (u a * (u b)⁻¹) : ℝ))⁻¹ = q ^ (e a - e b))
    (d : ℕ) (F : GA E k → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ h, F (t * h * t⁻¹) ∂nuD E k d = ENNReal.ofReal (q ^ totS e d) * ∫⁻ h, F h ∂nuD E k d := by
  have hc : Measurable (fun h : GA E k => t * h * t⁻¹) :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  induction d generalizing F with
  | zero =>
    have hFc : Measurable fun h => F (t * h * t⁻¹) := hF.comp hc
    change ∫⁻ h, F (t * h * t⁻¹) ∂Measure.dirac 1 = _ * ∫⁻ h, F h ∂Measure.dirac 1
    rw [lintegral_dirac' _ hFc, lintegral_dirac' _ hF]
    simp [totS]
  | succ d ih =>
    have := sFinite_nuD (E := E) (k := k) d
    have hM := measurable_blkMul (E := E) (k := k) (k - (d + 1))
    let a : UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → (Ad E)ˣ := fun p => u p.1.1 * (u p.1.2)⁻¹
    let G : (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E) → ℝ≥0∞ := fun y => ∫⁻ h, F (blkU y * h) ∂nuD E k d
    have hFM : Measurable fun p : (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E) × GA E k => F (blkU p.1 * p.2) := hF.comp hM
    have hFc : Measurable fun h => F (t * h * t⁻¹) := hF.comp hc
    have hFcM : Measurable fun p : (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E) × GA E k =>
        F (t * (blkU p.1 * p.2) * t⁻¹) := hFc.comp hM
    have hG : Measurable G := hFM.lintegral_prod_right'
    have hf : Measurable (fun (x : UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E) p => a p • x p) :=
      measurable_pi_lambda _ fun p =>
        (show Continuous fun x : Ad E => (a p : Ad E) * x from continuous_const_mul _).measurable.comp (measurable_pi_apply p)
    have hR : ∫⁻ h, F h ∂nuD E k (d + 1) = ∫⁻ y, G y ∂vecMeasure E _ := by
      change ∫⁻ h, F h ∂(Measure.map _ _) = _
      rw [lintegral_map hF hM, lintegral_prod _ hFM.aemeasurable]
    have hL : ∫⁻ h, F (t * h * t⁻¹) ∂nuD E k (d + 1) =
        ∫⁻ x, ENNReal.ofReal (q ^ totS e d) * G (fun p => a p • x p) ∂vecMeasure E _ := by
      change ∫⁻ h, F (t * h * t⁻¹) ∂(Measure.map _ _) = _
      rw [lintegral_map hFc hM, lintegral_prod _ hFcM.aemeasurable]
      refine lintegral_congr fun x => ?_
      have key : ∀ h, t * (blkU x * h) * t⁻¹ = blkU (fun p => a p • x p) * (t * h * t⁻¹) := fun h => by
        have e1 : blkU (fun p => a p • x p) = t * blkU x * t⁻¹ := (conj_blkU t u ht x).symm
        rw [e1]; group
      simp only [key]
      exact ih (fun y => F (blkU (fun p => a p • x p) * y)) (hF.comp (measurable_const_mul _))
    have hstep : (∏ p, ENNReal.ofReal ((GroundTheory.Global.IdeleGroup.ideleModule E (a p) : ℝ))⁻¹) =
        ENNReal.ofReal (q ^ colS e (k - (d + 1))) := by
      simp only [a, hmod]
      exact prod_ofReal_zpow _ hq _
    have hGf : Measurable fun x : UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E => G (fun p => a p • x p) := hG.comp hf
    rw [hL, hR, lintegral_const_mul _ hGf, lintegral_vec_smul a G hG, hstep, ← mul_assoc,
      ← ENNReal.ofReal_mul (zpow_nonneg hq.le _), ← zpow_add₀ hq.ne']
    simp only [totS, Finset.sum_range_succ]

theorem nuP_zero : nuP E k 0 = nuD E k (k - 1) := by
  have h1 : IsMir 0 (1 : GL (Fin k) E) := fun i j _ => rfl
  let i0 : ({γ : GL (Fin k) E | IsMir 0 γ} : Set _) := ⟨1, h1⟩
  have hu : ∀ γ : ({γ : GL (Fin k) E | IsMir 0 γ} : Set _), γ = i0 := fun γ => Subtype.ext (Units.ext (Matrix.ext fun i j =>
    γ.2 i j (Or.inl (Nat.zero_le _))))
  ext s hs
  rw [nuP, nuG, Measure.sum_apply _ hs, tsum_eq_single i0 (fun b hb => absurd (hu b) hb)]
  simp [i0]

theorem colS_eq (l : Fin k → ℤ) (c : Fin k) : colS l c = ∑ i : Fin k, if i < c then l i - l c else 0 := by
  classical
  unfold colS
  rw [← Finset.sum_subtype (Finset.univ.filter fun p : Fin k × Fin k => (p.1 : ℕ) < c ∧ (c : ℕ) ≤ p.2 ∧ (p.2 : ℕ) ≤ c)
    (by simp) (fun p => l p.1 - l p.2), Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single c]
  · simp only [le_refl, and_true, Fin.val_fin_lt]
  · intro b _ hb
    rw [if_neg]
    rintro ⟨-, h1, h2⟩
    have h1' : (c : ℕ) ≤ b := h1
    have h2' : (b : ℕ) ≤ c := h2
    exact hb (Fin.ext (by omega))
  · simp

theorem sum_cols (l : Fin k → ℤ) : ∑ c : Fin k, ∑ i : Fin k, (if i < c then l i - l c else 0) = rhoPair l :=
  _root_.UpperTheory.Reformulated.B.CountingPairs.main l

theorem totS_eq (l : Fin k → ℤ) : totS l (k - 1) = rhoPair l := by
  rw [← sum_cols l]
  simp only [← colS_eq]
  rw [Fin.sum_univ_eq_sum_range (fun j => colS l j) k]
  rcases k with _ | n
  · simp [totS]
  · have h0 : colS l 0 = 0 := Finset.sum_eq_zero fun t _ => absurd t.2.1 (Nat.not_lt_zero _)
    rw [← Finset.sum_range_reflect, Finset.sum_range_succ]
    simp only [totS, Nat.add_sub_cancel]
    rw [Nat.sub_self, h0, add_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    congr 1
    have := Finset.mem_range.1 hi
    omega

variable [IsTotallyComplex E]

theorem mod_locId (hD : D0) (w : Pl E) (m : ℤ) :
    (GroundTheory.Global.IdeleGroup.ideleModule E (locId w (Iwasawa.uniformizerUnit (w.adicCompletion E) ^ m)) : ℝ) =
      (Ideal.absNorm w.asIdeal : ℝ) ^ (-m) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ := hD E 1
  have h2 := h w (fun _ => m)
  have e : GeneralLinearGroup.det (fl 1 w (Iwasawa.torusPow (w.adicCompletion E) 1 fun _ => m)) =
      locId w (Iwasawa.uniformizerUnit (w.adicCompletion E) ^ m) := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, fl_torus, Matrix.det_diagonal]
    simp
  rw [Dt, e] at h2
  simpa using h2

theorem main : PositivityTheory.AdelicQuotientData.D0 → PositivityTheory.jumpWindows.G0 → PositivityTheory.AdelicQuotientData.N2 := by
  intro hD _ E _ _ _ k w l F hF
  have hm1 := mod_locId hD w 1
  have hq : 0 < (Ideal.absNorm w.asIdeal : ℝ) := by
    have h0 := (GroundTheory.Global.IdeleGroup.ideleModule E (locId w (Iwasawa.uniformizerUnit (w.adicCompletion E) ^ (1 : ℤ)))).2
    rw [hm1] at h0
    by_contra hc
    have h00 : (Ideal.absNorm w.asIdeal : ℝ) = 0 := le_antisymm (not_lt.1 hc) (Nat.cast_nonneg _)
    rw [h00] at h0
    simp at h0
  have hmod : ∀ a b, ((GroundTheory.Global.IdeleGroup.ideleModule E
      (locId w (Iwasawa.uniformizerUnit (w.adicCompletion E) ^ l a) *
        (locId w (Iwasawa.uniformizerUnit (w.adicCompletion E) ^ l b))⁻¹) : ℝ))⁻¹ =
      (Ideal.absNorm w.asIdeal : ℝ) ^ (l a - l b) := fun a b => by
    rw [← map_inv, ← map_mul, ← _root_.zpow_neg, ← _root_.zpow_add, ← sub_eq_add_neg, mod_locId hD, _root_.zpow_neg, inv_inv]
  rw [nuP_zero, nuD_conj _ _ (fl_torus w l) hq l hmod (k - 1) F hF, totS_eq]

end GlobalTheory.CompanionTheory.UnipotentNormalizer

end
