import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnMatInfOfIsUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandCLMInfApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArchimedeanRapidKernelOperatorFinsetSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumNormEntriesMulLe
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

noncomputable section

namespace GlobalTheory.JSW.MirCinf.SecFamInf

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem sum_norm_mul_le' {α : Type} [NormedRing α] (a b : Matrix (Fin n) (Fin n) α) :
    ∑ i, ∑ j, ‖(a * b) i j‖ ≤ (∑ i, ∑ j, ‖a i j‖) * ∑ i, ∑ j, ‖b i j‖ := by
  first
  | exact @_root_.GlobalTheory.EntryNormProductBound.sum_norm_entries_mul_le
  | exact _root_.GlobalTheory.EntryNormProductBound.sum_norm_entries_mul_le
  | (apply _root_.GlobalTheory.EntryNormProductBound.sum_norm_entries_mul_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.EntryNormProductBound.sum_norm_entries_mul_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EntryNormProductBound.sum_norm_entries_mul_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EntryNormProductBound.sum_norm_entries_mul_le ..)

theorem norm_sandCLMInf_le (A B : Matrix (Fin n) (Fin n) (Cinf E)) :
    ‖sandCLMInf A B‖ ≤ (n : ℝ) ^ 2 * (∑ i, ∑ j, ‖A i j‖) * (∑ i, ∑ j, ‖B i j‖) := by
  have hA : 0 ≤ ∑ i, ∑ j, ‖A i j‖ := by positivity
  have hB : 0 ≤ ∑ i, ∑ j, ‖B i j‖ := by positivity
  have h0 : 0 ≤ (n : ℝ) ^ 2 * (∑ i, ∑ j, ‖A i j‖) * (∑ i, ∑ j, ‖B i j‖) := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ h0 fun x => ?_
  have h1 : 0 ≤ (n : ℝ) ^ 2 * (∑ i, ∑ j, ‖A i j‖) * (∑ i, ∑ j, ‖B i j‖) * ‖x‖ := mul_nonneg h0 (norm_nonneg _)
  have key : ∀ i j, ‖sandCLMInf A B x i j‖ ≤ (n : ℝ) ^ 2 * (∑ i, ∑ j, ‖A i j‖) * (∑ i, ∑ j, ‖B i j‖) * ‖x‖ := by
    intro i j
    rw [sandCLMInf_apply]
    have e1 : ‖(A * Matrix.of x * B) i j‖ ≤ ∑ i, ∑ j, ‖(A * Matrix.of x * B) i j‖ :=
      (Finset.single_le_sum (f := fun j => ‖(A * Matrix.of x * B) i j‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, ‖(A * Matrix.of x * B) i j‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
    have e2 := sum_norm_mul_le' (A * Matrix.of x) B
    have e3 := sum_norm_mul_le' A (Matrix.of x)
    have e4 : ∑ i, ∑ j, ‖(Matrix.of x) i j‖ ≤ (n : ℝ) ^ 2 * ‖x‖ := by
      calc ∑ i, ∑ j, ‖(Matrix.of x) i j‖ ≤ ∑ _i : Fin n, ∑ _j : Fin n, ‖x‖ :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
              (norm_le_pi_norm (x i) j).trans (norm_le_pi_norm x i)
        _ = _ := by simp; ring
    calc ‖(A * Matrix.of x * B) i j‖ ≤ (∑ i, ∑ j, ‖(A * Matrix.of x) i j‖) * ∑ i, ∑ j, ‖B i j‖ := e1.trans e2
      _ ≤ ((∑ i, ∑ j, ‖A i j‖) * ((n : ℝ) ^ 2 * ‖x‖)) * ∑ i, ∑ j, ‖B i j‖ :=
          mul_le_mul_of_nonneg_right (e3.trans (mul_le_mul_of_nonneg_left e4 hA)) hB
      _ = _ := by ring
  exact (pi_norm_le_iff_of_nonneg h1).2 fun i => (pi_norm_le_iff_of_nonneg h1).2 fun j => key i j

theorem sum_norm_le_of_le (A : Matrix (Fin n) (Fin n) (Cinf E)) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i j w, ‖A i j w‖ ≤ c) : ∑ i, ∑ j, ‖A i j‖ ≤ (n : ℝ) ^ 2 * c := by
  calc ∑ i, ∑ j, ‖A i j‖ ≤ ∑ _i : Fin n, ∑ _j : Fin n, c :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          (pi_norm_le_iff_of_nonneg hc).2 fun w => h i j w
    _ = _ := by simp; ring

theorem measurable_sandCLMInf_apply {Y : Type} [MeasurableSpace Y] {A B : Y → Matrix (Fin n) (Fin n) (Cinf E)}
    (hA : ∀ i j, Measurable fun y => A y i j) (hB : ∀ i j, Measurable fun y => B y i j) (c : Fin n → Fin n → Cinf E) :
    Measurable fun y => sandCLMInf (A y) (B y) c := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [sandCLMInf_apply, Matrix.mul_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ fun l _ => ?_
  refine Measurable.mul ?_ (hB l j)
  exact Finset.measurable_sum _ fun k _ => (hA i k).mul measurable_const

theorem measurable_clm_evalInf {Y V : Type} [MeasurableSpace Y] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {f : Y → V →L[ℝ] ℝ} {w : Y → V}
    (hf : ∀ e, Measurable fun y => f y e) (hw : Measurable w) : Measurable fun y => f y (w y) := by
  have h1 : Measurable f := measurable_dual hf
  have hc : Continuous fun p : (V →L[ℝ] ℝ) × V => p.1 p.2 := isBoundedBilinearMap_apply.continuous
  exact hc.measurable.comp (h1.prodMk hw)

theorem measurable_htInf_comp {Y : Type} [MeasurableSpace Y] {γ : Y → GL (Fin n) (Cinf E)}
    (hγ : ∀ i j, Measurable fun y => (γ y : Matrix (Fin n) (Fin n) (Cinf E)) i j) :
    Measurable fun y => htInf (γ y) := by
  unfold htInf
  refine Finset.measurable_prod _ fun w _ => ?_
  exact measurable_comp_GL (F := htGL) continuous_htGL fun i j => (measurable_pi_apply w).comp (hγ i j)

theorem isOpen_isUnit_ofInf : IsOpen {x : Fin n → Fin n → Cinf E | IsUnit (Matrix.of x)} := by
  have := (isOpenEmbedding_entriesGLInf (E := E) (n := n)).isOpen_range
  convert this using 1
  ext x
  exact ⟨fun ⟨u, hu⟩ => ⟨u, hu⟩, fun ⟨u, hu⟩ => ⟨u, hu⟩⟩

theorem measurable_toGLInf_entry (i j : Fin n) :
    Measurable fun x : Fin n → Fin n → Cinf E => (toGLInf (Matrix.of x) : Matrix (Fin n) (Fin n) (Cinf E)) i j := by
  classical
  have : (fun x : Fin n → Fin n → Cinf E => (toGLInf (Matrix.of x) : Matrix (Fin n) (Fin n) (Cinf E)) i j) =
      fun x => if x ∈ {x : Fin n → Fin n → Cinf E | IsUnit (Matrix.of x)} then x i j
        else (1 : Matrix (Fin n) (Fin n) (Cinf E)) i j := by
    funext x
    by_cases h : IsUnit (Matrix.of x) <;> simp [toGLInf, h]
  rw [this]
  exact Measurable.ite isOpen_isUnit_ofInf.measurableSet (by fun_prop) measurable_const

theorem continuous_jacInf : Continuous (jacInf : Matrix (Fin n) (Fin n) (Cinf E) → ℝ) := by
  unfold jacInf
  refine continuous_finset_prod _ fun w _ => ?_
  exact (Complex.continuous_normSq.comp ((continuous_apply w).comp (continuous_id.matrix_det))).pow n

theorem one_le_htInf' (y : GL (Fin n) (Cinf E)) : 1 ≤ htInf y := by
  unfold htInf
  calc (1 : ℝ) = ∏ _w : InfinitePlace E, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) fun w _ => one_le_htGL _

theorem htGL_le_htInf' (y : GL (Fin n) (Cinf E)) (w : InfinitePlace E) :
    htGL (Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w) y) ≤ htInf y := by
  classical
  unfold htInf
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)]
  refine le_mul_of_one_le_right (htGL_pos _).le ?_
  calc (1 : ℝ) = ∏ _w ∈ Finset.univ.erase w, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) fun w _ => one_le_htGL _

theorem norm_entry_le_htInf' (y : GL (Fin n) (Cinf E)) (i j : Fin n) (w : InfinitePlace E) :
    ‖(y : Matrix (Fin n) (Fin n) (Cinf E)) i j w‖ ≤ htInf y ∧
      ‖((y⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) i j w‖ ≤ htInf y := by
  set p : GL (Fin n) (Cinf E) →* GL (Fin n) ℂ :=
    Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w)
  refine ⟨(norm_entry_le_htGL (p y) i j).trans (htGL_le_htInf' y w), ?_⟩
  have e : ((y⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) i j w =
      (((p y)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j := by
    rw [← map_inv]; rfl
  rw [e]
  exact (norm_entry_le_htGL _ i j).trans ((htGL_inv (p y)).le.trans (htGL_le_htInf' y w))

theorem measurable_secKInf_secEtaInf {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {X : Type} [MeasurableSpace X] (κ : X → ℂ) (τ : X → (Z × (Fin n → Fin n → Cinf E)) →L[ℝ] ℝ)
    (hκ : Measurable κ) (hτ : ∀ z, Measurable fun x => τ x z) (R : ℝ) (σ₀ : Fin n → Fin n → Cinf E)
    (L : Z →L[ℝ] (Fin n → Fin n → Cinf E)) (X₀ : Type) [MeasurableSpace X₀] (γ₀ : X₀ → GL (Fin n) (Cinf E))
    (hγ₀ : ∀ i j, Measurable fun x => (γ₀ x : Matrix (Fin n) (Fin n) (Cinf E)) i j) :
    Measurable (fun p : X₀ × ((Fin n → Fin n → Cinf E) × X) => secKInf R σ₀ κ τ (γ₀ p.1) p.2) ∧
      ∀ z, Measurable fun p : X₀ × ((Fin n → Fin n → Cinf E) × X) => secEtaInf L τ (γ₀ p.1) p.2 z := by
  letI : MeasurableSpace Z := borel Z
  haveI : BorelSpace Z := ⟨rfl⟩
  have hq : ∀ i j, Measurable fun p : X₀ × ((Fin n → Fin n → Cinf E) × X) =>
      (γ₀ p.1 : Matrix (Fin n) (Fin n) (Cinf E)) i j :=
    fun i j => (hγ₀ i j).comp measurable_fst
  have hinv : ∀ i j, Measurable fun p : X₀ × ((Fin n → Fin n → Cinf E) × X) =>
      (((γ₀ p.1)⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) i j := fun i j =>
    measurable_comp_GLInf
      (F := fun g : GL (Fin n) (Cinf E) => ((g⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) i j)
      (Units.continuous_coe_inv.matrix_elem i j) hq
  have hx1 : Measurable fun p : X₀ × ((Fin n → Fin n → Cinf E) × X) => p.2.1 := measurable_fst.comp measurable_snd
  have hx : ∀ i j, Measurable fun p : X₀ × ((Fin n → Fin n → Cinf E) × X) => Matrix.of p.2.1 i j :=
    fun i j => (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hx1)
  have hy : Measurable fun p : X₀ × ((Fin n → Fin n → Cinf E) × X) => p.2.2 := measurable_snd.comp measurable_snd
  have hτy : ∀ e, Measurable fun p : X₀ × ((Fin n → Fin n → Cinf E) × X) => τ p.2.2 e := fun e => (hτ e).comp hy
  refine ⟨?_, fun z => ?_⟩
  · unfold secKInf
    refine Measurable.ite ?_ ?_ measurable_const
    · have e : {p : X₀ × ((Fin n → Fin n → Cinf E) × X) | IsUnit (Matrix.of p.2.1) ∧
          htInf (toGLInf (Matrix.of p.2.1)) ≤ R * htInf (γ₀ p.1)} =
          (fun p : X₀ × ((Fin n → Fin n → Cinf E) × X) => p.2.1) ⁻¹' {x | IsUnit (Matrix.of x)} ∩
          {p | htInf (toGLInf (Matrix.of p.2.1)) ≤ R * htInf (γ₀ p.1)} := by
        ext p; simp
      rw [e]
      refine (isOpen_isUnit_ofInf.measurableSet.preimage hx1).inter (measurableSet_le ?_ ?_)
      · exact measurable_htInf_comp (γ := fun p : X₀ × ((Fin n → Fin n → Cinf E) × X) => toGLInf (Matrix.of p.2.1))
          (fun i j => (measurable_toGLInf_entry i j).comp hx1)
      · exact (measurable_htInf_comp hq).const_mul R
    · refine Measurable.mul (Measurable.mul ?_ (hκ.comp hy)) ?_
      · exact measurable_comp_GLInf
          (F := fun g : GL (Fin n) (Cinf E) =>
            ((jacInf ((g⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ))
          (Complex.continuous_ofReal.comp (continuous_jacInf.comp Units.continuous_coe_inv)) hq
      · exact (continuous_subtype_val.comp Real.continuous_fourierChar).measurable.comp
          (measurable_clm_evalInf hτy (measurable_const.prodMk (measurable_sandCLMInf_apply hinv hx σ₀)))
  · have e : (fun p : X₀ × ((Fin n → Fin n → Cinf E) × X) => secEtaInf L τ (γ₀ p.1) p.2 z) = fun p =>
        τ p.2.2 (z, sandCLMInf (((γ₀ p.1)⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E))
          (Matrix.of p.2.1) (L z)) := by
      funext p; rfl
    rw [e]
    exact measurable_clm_evalInf hτy (measurable_const.prodMk (measurable_sandCLMInf_apply hinv hx (L z)))

theorem jacInf_inv_le (q : GL (Fin n) (Cinf E)) :
    jacInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) ≤
      ((((n.factorial : ℝ) * htInf q ^ n) ^ 2) ^ n) ^ Fintype.card (InfinitePlace E) := by
  unfold jacInf
  rw [← Finset.card_univ, ← Finset.prod_const]
  refine Finset.prod_le_prod (fun w _ => pow_nonneg (Complex.normSq_nonneg _) _) fun w _ => ?_
  set M := ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) with hM
  have hdw : M.det w = ((Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w).mapMatrix M).det :=
    RingHom.map_det (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w) M
  have hdet : ‖M.det w‖ ≤ n.factorial * htInf q ^ n := by
    rw [hdw]
    have := Matrix.det_le (abv := NormedField.toAbsoluteValue ℂ)
      (A := (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w).mapMatrix M) (x := htInf q)
      (fun i j => (norm_entry_le_htInf' q i j w).2)
    rw [Fintype.card_fin, nsmul_eq_mul] at this
    exact this
  refine pow_le_pow_left₀ (Complex.normSq_nonneg _) ?_ n
  rw [Complex.normSq_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) hdet 2

theorem secKInf_moment_le {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {X : Type} (κ : X → ℂ)
    (τ : X → (Z × (Fin n → Fin n → Cinf E)) →L[ℝ] ℝ) (R : ℝ) (σ₀ : Fin n → Fin n → Cinf E)
    (L : Z →L[ℝ] (Fin n → Fin n → Cinf E)) (N : ℕ) (q : GL (Fin n) (Cinf E)) (p : (Fin n → Fin n → Cinf E) × X) :
    ‖secKInf R σ₀ κ τ q p‖ * (htInf (toGLInf (Matrix.of p.1)) * (1 + ‖secEtaInf L τ q p‖)) ^ N ≤
      (Metric.closedBall (0 : Fin n → Fin n → Cinf E) (|R| * htInf q)).indicator
        (fun _ => ((((n.factorial : ℝ) * htInf q ^ n) ^ 2) ^ n) ^ Fintype.card (InfinitePlace E) *
          ((|R| * (1 + (n : ℝ) ^ 6 * |R| * ‖L‖)) * htInf q ^ 3) ^ N) p.1 *
        (‖κ p.2‖ * (1 + ‖τ p.2‖) ^ N) := by
  have hh1 := one_le_htInf' q
  have hh0 : 0 ≤ htInf q := by linarith
  have hK0 : 0 ≤ ((((n.factorial : ℝ) * htInf q ^ n) ^ 2) ^ n) ^ Fintype.card (InfinitePlace E) *
      ((|R| * (1 + (n : ℝ) ^ 6 * |R| * ‖L‖)) * htInf q ^ 3) ^ N := by
    have : 0 ≤ |R| * (1 + (n : ℝ) ^ 6 * |R| * ‖L‖) := by positivity
    exact mul_nonneg (pow_nonneg (pow_nonneg (sq_nonneg _) _) _)
      (pow_nonneg (mul_nonneg this (pow_nonneg hh0 _)) _)
  by_cases hc : IsUnit (Matrix.of p.1) ∧ htInf (toGLInf (Matrix.of p.1)) ≤ R * htInf q
  · obtain ⟨hu, hle⟩ := hc
    have hg1 := one_le_htInf' (toGLInf (Matrix.of p.1))
    have hR : 0 ≤ R := by
      by_contra hR
      push_neg at hR
      nlinarith
    have habs : |R| = R := abs_of_nonneg hR
    have hval : (toGLInf (Matrix.of p.1) : Matrix (Fin n) (Fin n) (Cinf E)) = Matrix.of p.1 := val_toGLInf hu
    have hent : ∀ i j w, ‖p.1 i j w‖ ≤ R * htInf q := by
      intro i j w
      have := (norm_entry_le_htInf' (toGLInf (Matrix.of p.1)) i j w).1
      rw [hval] at this
      exact this.trans hle
    have hRh : 0 ≤ R * htInf q := mul_nonneg hR hh0
    have hball : p.1 ∈ Metric.closedBall (0 : Fin n → Fin n → Cinf E) (|R| * htInf q) := by
      rw [mem_closedBall_zero_iff, habs]
      exact (pi_norm_le_iff_of_nonneg hRh).2 fun i => (pi_norm_le_iff_of_nonneg hRh).2 fun j =>
        (pi_norm_le_iff_of_nonneg hRh).2 fun w => hent i j w
    rw [Set.indicator_of_mem hball]
    set D := jacInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) with hDdef
    have hD0 : 0 ≤ D := Finset.prod_nonneg fun w _ => pow_nonneg (Complex.normSq_nonneg _) _
    have hK : ‖secKInf R σ₀ κ τ q p‖ = D * ‖κ p.2‖ := by
      simp only [secKInf, if_pos (And.intro hu hle), norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
      rw [abs_of_nonneg hD0]
    have hD : D ≤ ((((n.factorial : ℝ) * htInf q ^ n) ^ 2) ^ n) ^ Fintype.card (InfinitePlace E) :=
      jacInf_inv_le q
    set s := sandCLMInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) (Matrix.of p.1)
    have hs : ‖s‖ ≤ (n : ℝ) ^ 6 * R * htInf q ^ 2 := by
      refine (norm_sandCLMInf_le _ _).trans ?_
      have e1 := sum_norm_le_of_le ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) hh0
        (fun i j w => (norm_entry_le_htInf' q i j w).2)
      have e2 := sum_norm_le_of_le (Matrix.of p.1) hRh hent
      have e0 : 0 ≤ ∑ i, ∑ j, ‖((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) i j‖ :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
      have e3 : 0 ≤ ∑ i, ∑ j, ‖(Matrix.of p.1) i j‖ :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
      have hn : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
      calc (n : ℝ) ^ 2 * (∑ i, ∑ j, ‖((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) i j‖) *
            (∑ i, ∑ j, ‖(Matrix.of p.1) i j‖)
          ≤ (n : ℝ) ^ 2 * ((n : ℝ) ^ 2 * htInf q) * ((n : ℝ) ^ 2 * (R * htInf q)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left e1 hn) e2 e3 (mul_nonneg hn (mul_nonneg hn hh0))
        _ = _ := by ring
    have hη : ‖secEtaInf L τ q p‖ ≤ ‖τ p.2‖ * (1 + ‖s‖ * ‖L‖) := by
      unfold secEtaInf
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      rw [ContinuousLinearMap.opNorm_prod, Prod.norm_def]
      refine max_le ?_ ?_
      · have := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := Z)
        have : 0 ≤ ‖s‖ * ‖L‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
        linarith
      · have := ContinuousLinearMap.opNorm_comp_le s L
        linarith
    set t := ‖τ p.2‖
    set ℓ := ‖L‖
    set h := htInf q
    have ht0 : 0 ≤ t := norm_nonneg _
    have hl0 : 0 ≤ ℓ := norm_nonneg _
    have hc0 : 0 ≤ (n : ℝ) ^ 6 * R * ℓ := by positivity
    have hsl : ‖s‖ * ℓ ≤ (n : ℝ) ^ 6 * R * ℓ * h ^ 2 := by
      calc ‖s‖ * ℓ ≤ ((n : ℝ) ^ 6 * R * h ^ 2) * ℓ := mul_le_mul_of_nonneg_right hs hl0
        _ = _ := by ring
    have hbase : htInf (toGLInf (Matrix.of p.1)) * (1 + ‖secEtaInf L τ q p‖) ≤
        (|R| * (1 + (n : ℝ) ^ 6 * |R| * ℓ)) * h ^ 3 * (1 + t) := by
      rw [habs]
      have h2 : 1 ≤ h ^ 2 := one_le_pow₀ hh1
      have a1 : 1 + ‖secEtaInf L τ q p‖ ≤ (1 + t) * ((1 + (n : ℝ) ^ 6 * R * ℓ) * h ^ 2) := by
        have b1 : 1 + ‖secEtaInf L τ q p‖ ≤ 1 + t * (1 + (n : ℝ) ^ 6 * R * ℓ * h ^ 2) := by
          have := mul_le_mul_of_nonneg_left (add_le_add_left hsl 1) ht0
          linarith
        have b2 : 1 + (n : ℝ) ^ 6 * R * ℓ * h ^ 2 ≤ (1 + (n : ℝ) ^ 6 * R * ℓ) * h ^ 2 := by nlinarith
        have b3 : 1 ≤ (1 + (n : ℝ) ^ 6 * R * ℓ) * h ^ 2 := by nlinarith
        nlinarith
      have a0 : 0 ≤ 1 + ‖secEtaInf L τ q p‖ := by positivity
      calc htInf (toGLInf (Matrix.of p.1)) * (1 + ‖secEtaInf L τ q p‖)
          ≤ (R * h) * ((1 + t) * ((1 + (n : ℝ) ^ 6 * R * ℓ) * h ^ 2)) :=
            mul_le_mul hle a1 a0 (by nlinarith)
        _ = _ := by ring
    have hpow := pow_le_pow_left₀ (mul_nonneg (htInf_pos' _).le (by positivity)) hbase N
    rw [mul_pow _ (1 + t)] at hpow
    rw [hK]
    have k0 : 0 ≤ ‖κ p.2‖ := norm_nonneg _
    calc D * ‖κ p.2‖ * (htInf (toGLInf (Matrix.of p.1)) * (1 + ‖secEtaInf L τ q p‖)) ^ N
        ≤ ((((n.factorial : ℝ) * h ^ n) ^ 2) ^ n) ^ Fintype.card (InfinitePlace E) * ‖κ p.2‖ *
            (((|R| * (1 + (n : ℝ) ^ 6 * |R| * ℓ)) * h ^ 3) ^ N * (1 + t) ^ N) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hD k0) hpow
            (pow_nonneg (mul_nonneg (htInf_pos' _).le (by positivity)) _) (mul_nonneg (hD0.trans hD) k0)
      _ = _ := by ring
  · have : secKInf R σ₀ κ τ q p = 0 := by simp only [secKInf, if_neg hc]
    rw [this, norm_zero, zero_mul]
    exact mul_nonneg (Set.indicator_nonneg (fun _ _ => hK0) _) (by positivity)

theorem isRapidFamInf_secKInf : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (κ : X → ℂ)
    (τ : X → (Z × (Fin n → Fin n → Cinf E)) →L[ℝ] ℝ), Measurable κ → (∀ z, Measurable fun x => τ x z) →
    (∀ N : ℕ, Integrable (fun x => ‖κ x‖ * (1 + ‖τ x‖) ^ N) ν) → ∀ (R : ℝ) (σ₀ : Fin n → Fin n → Cinf E)
    (L : Z →L[ℝ] (Fin n → Fin n → Cinf E)), IsRapidFamInf ((volume : Measure (Fin n → Fin n → Cinf E)).prod ν)
      (secKInf R σ₀ κ τ) (fun p => toGLInf (Matrix.of p.1)) (secEtaInf L τ) := by
  intro E _ _ n Z _ _ _ X _ ν _ κ τ hκ hτ hint R σ₀ L
  have hγ : ∀ i j, Measurable fun p : (Fin n → Fin n → Cinf E) × X =>
      (toGLInf (Matrix.of p.1) : Matrix (Fin n) (Fin n) (Cinf E)) i j :=
    fun i j => (measurable_toGLInf_entry i j).comp measurable_fst
  refine ⟨hγ, fun X₀ _ γ₀ hγ₀ => measurable_secKInf_secEtaInf κ τ hκ hτ R σ₀ L X₀ γ₀ hγ₀, fun N => ?_⟩
  refine ⟨(n.factorial : ℝ) ^ (2 * n * Fintype.card (InfinitePlace E)) *
      (|R| * (1 + (n : ℝ) ^ 6 * |R| * ‖L‖)) ^ N *
      |R| ^ Module.finrank ℝ (Fin n → Fin n → Cinf E) *
      (volume : Measure (Fin n → Fin n → Cinf E)).real (Metric.ball 0 1) * ∫ y, ‖κ y‖ * (1 + ‖τ y‖) ^ N ∂ν,
    n * 2 * n * Fintype.card (InfinitePlace E) + 3 * N + Module.finrank ℝ (Fin n → Fin n → Cinf E), fun q => ?_⟩
  have hm := measurable_secKInf_secEtaInf κ τ hκ hτ R σ₀ L Unit (fun _ => q) (fun _ _ => measurable_const)
  have hu : Measurable fun p : (Fin n → Fin n → Cinf E) × X => (((), p) : Unit × ((Fin n → Fin n → Cinf E) × X)) :=
    measurable_const.prodMk measurable_id
  have hk : Measurable (secKInf R σ₀ κ τ q) := hm.1.comp hu
  have hη : Measurable (secEtaInf L τ q) := measurable_dual fun z => (hm.2 z).comp hu
  have hg : Measurable fun p : (Fin n → Fin n → Cinf E) × X => htInf (toGLInf (Matrix.of p.1)) :=
    measurable_htInf_comp hγ
  have hF : Measurable fun p : (Fin n → Fin n → Cinf E) × X =>
      ‖secKInf R σ₀ κ τ q p‖ * (htInf (toGLInf (Matrix.of p.1)) * (1 + ‖secEtaInf L τ q p‖)) ^ N :=
    hk.norm.mul ((hg.mul (measurable_const.add hη.norm)).pow_const N)
  have h0 : ∀ p : (Fin n → Fin n → Cinf E) × X,
      0 ≤ ‖secKInf R σ₀ κ τ q p‖ * (htInf (toGLInf (Matrix.of p.1)) * (1 + ‖secEtaInf L τ q p‖)) ^ N := fun p =>
    mul_nonneg (norm_nonneg _) (pow_nonneg (mul_nonneg (htInf_pos' _).le (by positivity)) _)
  have hbd := secKInf_moment_le κ τ R σ₀ L N q
  have hr : 0 ≤ |R| * htInf q := mul_nonneg (abs_nonneg _) (htInf_pos' _).le
  set K := ((((n.factorial : ℝ) * htInf q ^ n) ^ 2) ^ n) ^ Fintype.card (InfinitePlace E) *
    ((|R| * (1 + (n : ℝ) ^ 6 * |R| * ‖L‖)) * htInf q ^ 3) ^ N with hK
  have hB : Integrable (fun p : (Fin n → Fin n → Cinf E) × X =>
      (Metric.closedBall (0 : Fin n → Fin n → Cinf E) (|R| * htInf q)).indicator (fun _ => K) p.1 *
        (‖κ p.2‖ * (1 + ‖τ p.2‖) ^ N)) ((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) :=
    Integrable.mul_prod ((integrable_indicator_iff measurableSet_closedBall).2
      (integrableOn_const measure_closedBall_lt_top.ne)) (hint N)
  refine ⟨hB.mono' hF.aestronglyMeasurable (ae_of_all _ fun p => ?_), ?_⟩
  · rw [Real.norm_eq_abs, abs_of_nonneg (h0 p)]
    exact hbd p
  · refine (integral_mono_of_nonneg (ae_of_all _ h0) hB (ae_of_all _ hbd)).trans (le_of_eq ?_)
    rw [integral_prod_mul ((Metric.closedBall (0 : Fin n → Fin n → Cinf E) (|R| * htInf q)).indicator fun _ => K)
      (fun y => ‖κ y‖ * (1 + ‖τ y‖) ^ N), integral_indicator_const _ measurableSet_closedBall, smul_eq_mul]
    simp only [Measure.real, Measure.addHaar_closedBall _ _ hr, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ (|R| * htInf q) ^ Module.finrank ℝ (Fin n → Fin n → Cinf E)), hK]
    simp only [mul_pow, ← pow_mul, pow_add]
    ring

example : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (κ : X → ℂ)
    (τ : X → (Z × (Fin n → Fin n → Cinf E)) →L[ℝ] ℝ), Measurable κ → (∀ z, Measurable fun x => τ x z) →
    (∀ N : ℕ, Integrable (fun x => ‖κ x‖ * (1 + ‖τ x‖) ^ N) ν) → ∀ (R : ℝ) (σ₀ : Fin n → Fin n → Cinf E)
    (L : Z →L[ℝ] (Fin n → Fin n → Cinf E)), IsRapidFamInf ((volume : Measure (Fin n → Fin n → Cinf E)).prod ν)
      (secKInf R σ₀ κ τ) (fun p => toGLInf (Matrix.of p.1)) (secEtaInf L τ) := isRapidFamInf_secKInf

end GlobalTheory.JSW.MirCinf.SecFamInf
