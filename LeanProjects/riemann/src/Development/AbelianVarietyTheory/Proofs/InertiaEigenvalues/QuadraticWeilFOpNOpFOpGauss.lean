import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStableGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticStarStructure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualMeasureExistsUniqueFourierInversion

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open scoped Pointwise

noncomputable section

namespace GlobalTheory.JR.WeilQuad.Fnf

theorem continuous_std {F : Type} [NormedField F] (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) : Continuous ψ := by
  rw [continuous_iff_continuousAt]
  intro a
  refine (continuousAt_const (y := ψ a)).congr ?_
  filter_upwards [Metric.ball_mem_nhds a one_pos] with y hy
  show ψ a = ψ y
  have h1 : ψ (y - a) = 1 := hψ.1 _ (by rw [← dist_eq_norm]; exact (Metric.mem_ball.1 hy).le)
  calc ψ a = ψ a * ψ (y - a) := by rw [h1, mul_one]
    _ = ψ y := by rw [← AddChar.map_add_eq_mul]; congr 1; abel

theorem isCompact_sup {V : Type} [AddCommGroup V] [TopologicalSpace V] [ContinuousAdd V]
    (H K : AddSubgroup V) (hH : IsCompact (H : Set V)) (hK : IsCompact (K : Set V)) :
    IsCompact ((H ⊔ K : AddSubgroup V) : Set V) := by
  have : ((H ⊔ K : AddSubgroup V) : Set V) =
      (fun p : V × V => p.1 + p.2) '' ((H : Set V) ×ˢ (K : Set V)) := by
    ext v
    simp only [SetLike.mem_coe, AddSubgroup.mem_sup, Set.mem_image, Set.mem_prod, Prod.exists]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, b, ⟨ha, hb⟩, rfl⟩
    · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
  rw [this]
  exact (hH.prod hK).image continuous_add

theorem isCompact_finset_sup {V ι : Type} [AddCommGroup V] [TopologicalSpace V] [ContinuousAdd V]
    (t : Finset ι) (H : ι → AddSubgroup V) (hH : ∀ i, IsCompact (H i : Set V)) :
    IsCompact ((t.sup H : AddSubgroup V) : Set V) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.sup_insert]; exact isCompact_sup _ _ (hH a) ih

theorem exists_big {F V : Type} [NontriviallyNormedField F] [AddCommGroup V] [Module F V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul F V]
    (Λ₀ : AddSubgroup V) (ho : IsOpen (Λ₀ : Set V)) (hc : IsCompact (Λ₀ : Set V)) (C : Set V)
    (hC : IsCompact C) :
    ∃ Λ : AddSubgroup V, IsOpen (Λ : Set V) ∧ IsCompact (Λ : Set V) ∧ Λ₀ ≤ Λ ∧ C ⊆ Λ := by
  obtain ⟨c, hc1⟩ := NormedField.exists_one_lt_norm F
  have hc0 : c ≠ 0 := norm_pos_iff.1 (one_pos.trans hc1)
  let S : ℕ → AddSubgroup V := fun n => (c ^ n) • Λ₀
  have hS : ∀ n, (S n : Set V) = (c ^ n) • (Λ₀ : Set V) := fun n => AddSubgroup.coe_pointwise_smul _ _
  have hSo : ∀ n, IsOpen (S n : Set V) := fun n => by rw [hS]; exact ho.smul₀ (pow_ne_zero _ hc0)
  have hSc : ∀ n, IsCompact (S n : Set V) := fun n => by rw [hS]; exact hc.smul _
  have hcov : C ⊆ ⋃ n, (S n : Set V) := by
    intro y _
    have ht : Tendsto (fun n : ℕ => (c⁻¹) ^ n • y) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => (c⁻¹) ^ n) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hc1)
      simpa using h1.smul_const y
    obtain ⟨n, hn⟩ := (ht.eventually (ho.mem_nhds Λ₀.zero_mem)).exists
    refine Set.mem_iUnion.2 ⟨n, ?_⟩
    rw [hS]
    refine ⟨(c⁻¹) ^ n • y, hn, ?_⟩
    simp [smul_smul, mul_inv_cancel₀ (pow_ne_zero n hc0)]
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun n => (S n : Set V)) hSo hcov
  refine ⟨Λ₀ ⊔ t.sup S, AddSubgroup.isOpen_mono le_sup_left ho,
    isCompact_sup _ _ hc (isCompact_finset_sup t S hSc), le_sup_left, ?_⟩
  intro y hy
  obtain ⟨n, hn, hy'⟩ := Set.mem_iUnion₂.1 (ht hy)
  exact (le_sup_right : t.sup S ≤ Λ₀ ⊔ t.sup S) (Finset.le_sup (f := S) hn hy')

theorem setIntegral_add_left_mem {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddLeftInvariant] (Λ : AddSubgroup V)
    (hΛ : MeasurableSet (Λ : Set V)) (g : V → ℂ) (w : V) (hw : w ∈ Λ) :
    ∫ y in (Λ : Set V), g (w + y) ∂μ = ∫ y in (Λ : Set V), g y ∂μ := by
  rw [← integral_indicator hΛ, ← integral_indicator hΛ]
  have : (Set.indicator (Λ : Set V) fun y => g (w + y)) = fun y => Set.indicator (Λ : Set V) g (w + y) := by
    funext y
    by_cases hy : y ∈ Λ
    · have h2 : w + y ∈ Λ := Λ.add_mem hw hy
      simp [Set.indicator_apply, hy, h2]
    · have h2 : w + y ∉ Λ := fun h => hy (by simpa using Λ.sub_mem h hw)
      simp [Set.indicator_apply, hy, h2]
  rw [this, integral_add_left_eq_self (fun y => Set.indicator (Λ : Set V) g y) w]

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem NL_add [Unram F E] (A : Et F E) (a b : A.L) :
    A.NL (a + b) = A.NL a + A.NL b + Algebra.trace A.K A.L (star a * b) := by
  obtain ⟨-, hinj, hN, htr, -⟩ := Et.quadratic_structure F E A
  apply hinj
  rw [map_add, map_add, hN, hN, hN, htr, star_add, star_mul', star_star]
  ring

theorem NL_smul [Unram F E] (A : Et F E) (c : A.K) (a : A.L) : A.NL (c • a) = c ^ 2 * A.NL a := by
  obtain ⟨-, hinj, hN, -, -⟩ := Et.quadratic_structure F E A
  apply hinj
  rw [map_mul, map_pow, hN, hN, EtMeas.star_smul_K, Algebra.smul_def, Algebra.smul_def]
  ring

theorem tr_symm [Unram F E] (A : Et F E) (a b : A.L) :
    Algebra.trace A.K A.L (star a * b) = Algebra.trace A.K A.L (star b * a) := by
  obtain ⟨-, hinj, -, htr, -⟩ := Et.quadratic_structure F E A
  apply hinj
  rw [htr, htr, star_mul', star_mul', star_star, star_star]
  ring

theorem tr_smul_right (A : Et F E) (c : A.K) (a b : A.L) :
    Algebra.trace A.K A.L (star a * (c • b)) = c * Algebra.trace A.K A.L (star a * b) := by
  rw [mul_smul_comm, map_smul, smul_eq_mul]

theorem tr_add_right (A : Et F E) (a b b' : A.L) :
    Algebra.trace A.K A.L (star a * (b + b')) =
      Algebra.trace A.K A.L (star a * b) + Algebra.trace A.K A.L (star a * b') := by
  rw [mul_add, map_add]

theorem psiK_add (A : Et F E) (ψ : AddChar F ℂ) (a b : A.K) :
    A.psiK ψ (a + b) = A.psiK ψ a * A.psiK ψ b := by
  simp only [Et.psiK, map_add, AddChar.map_add_eq_mul]

end GlobalTheory.JR.WeilQuad.Fnf

namespace GlobalTheory.JR.WeilQuad

open Fnf in

theorem fOp_nOp_fOp (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [U : Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ)
    (hH : Hyp A ψ x μ ω) (u : A.Kˣ) (G : ℂ) (hG : IsStableGauss A ψ x μ u G) (φ : A.L → ℂ) (hφ : IsTest φ)
    (z : A.L) :
    fOp A ψ x μ (nOp A ψ x u (fOp A ψ x μ φ)) z = G * A.psiK ψ (-((u⁻¹ : A.Kˣ) : A.K) * x * A.NL z) *
      fOp A ψ x μ (nOp A ψ x (-((u⁻¹ : A.Kˣ) : A.K)) φ) ((-((u⁻¹ : A.Kˣ) : A.K)) • z) := by
  obtain ⟨-, -, hψ, hsd, -⟩ := hH
  have := U.charZero; have := U.ultraF; have := U.lcF
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  have := EtMeas.finite_L A
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  have : ContinuousStar A.L := ⟨IsModuleTopology.continuous_of_linearMap (EtMeas.starF A)⟩
  have hμ : μ.IsAddHaarMeasure := hsd.1
  obtain ⟨-, hinj, -, htr, hnd0⟩ := Et.quadratic_structure F E A

  have hψc := continuous_std ψ hψ
  have htrKc : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap _
  have htrLc : Continuous (Algebra.trace A.K A.L) :=
    IsModuleTopology.continuous_of_linearMap ((Algebra.trace A.K A.L).restrictScalars F)
  have hec : Continuous (A.psiK ψ) := by
    show Continuous fun t => ψ (Algebra.trace F A.K t)
    exact hψc.comp htrKc
  have hNc := EtMeas.continuous_NL A
  have hk2 : Continuous (fun p : A.L × A.L => A.kerL ψ x p.1 p.2) := by
    show Continuous fun p : A.L × A.L => A.psiK ψ ((x : A.K) * Algebra.trace A.K A.L (star p.1 * p.2))
    exact hec.comp (continuous_const.mul (htrLc.comp ((continuous_star.comp continuous_fst).mul continuous_snd)))
  have hφc : Continuous φ := hφ.1.continuous
  have hsmc : ∀ c : A.K, Continuous (fun v : A.L => c • v) := fun c => by
    simp_rw [Algebra.smul_def]; exact continuous_const.mul continuous_id

  have hs : (EtMeas.formL A x).IsSymm := ⟨fun y y' => by
    rw [EtMeas.formL_apply, EtMeas.formL_apply]
    congr 2
    apply hinj
    rw [htr, htr]; simp [add_comm, mul_comm]⟩
  have hl : ∀ y', (∀ y, EtMeas.formL A x y' y = 0) → y' = 0 := fun y' h => hnd0 y' fun y => by
    have h1 : (x : A.K) * Algebra.trace A.K A.L (star y' * y) = 0 := EtMeas.eq_zero_of_trace F A.K _ fun k => by
      have := h (k • y)
      rw [EtMeas.formL_apply, mul_smul_comm, map_smul, smul_eq_mul] at this
      rw [← this]; congr 1; ring
    simpa using h1
  have hfφ : IsTest (fOp A ψ x μ φ) :=
    (SelfDualUniq.selfDual_exists_unique_isTest F E ψ hψ A.L (EtMeas.formL A x) hs
      ⟨hl, fun y h => hl y fun y' => by rw [hs.eq]; exact h y'⟩).2 μ hμ φ hφ

  set ui : A.K := ((u⁻¹ : A.Kˣ) : A.K) with hui
  have huui : (u : A.K) * ui = 1 := by simp [hui]
  obtain ⟨Λ₀, hΛ₀o, hΛ₀c, hΛ₀⟩ := hG
  set S := tsupport φ with hSdef
  have hSc : IsCompact S := hφ.2
  have hSm : MeasurableSet S := (isClosed_tsupport φ).measurableSet
  have hCc : IsCompact (tsupport (fOp A ψ x μ φ) ∪ (fun y => ui • (y + z)) '' S) :=
    hfφ.2.union (hSc.image ((hsmc ui).comp (continuous_id.add continuous_const)))
  obtain ⟨Λ, hΛo, hΛc, hΛ₀Λ, hCΛ⟩ := exists_big (F := F) Λ₀ hΛ₀o hΛ₀c _ hCc
  have hGΛ : gaussInt A ψ x μ u Λ = G := hΛ₀ Λ hΛo hΛc hΛ₀Λ
  have hΛm : MeasurableSet (Λ : Set A.L) := hΛo.measurableSet
  have hφ0 : ∀ y ∉ S, φ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  have hf0 : ∀ y' ∉ (Λ : Set A.L), fOp A ψ x μ φ y' = 0 := fun y' hy' =>
    image_eq_zero_of_notMem_tsupport fun h => hy' (hCΛ (Or.inl h))
  have hfS : ∀ y', fOp A ψ x μ φ y' = ∫ y in S, φ y * A.kerL ψ x y y' ∂μ := fun y' =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by rw [hφ0 y hy, zero_mul]).symm

  have e1 : fOp A ψ x μ (nOp A ψ x u (fOp A ψ x μ φ)) z =
      ∫ y' in (Λ : Set A.L), ∫ y in S, φ y * (A.psiK ψ ((u : A.K) * x * A.NL y') * A.kerL ψ x y y' *
        A.kerL ψ x y' z) ∂μ ∂μ := by
    show ∫ y', nOp A ψ (x : A.K) (u : A.K) (fOp A ψ x μ φ) y' * A.kerL ψ x y' z ∂μ = _
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := (Λ : Set A.L))]
    · refine setIntegral_congr_fun hΛm fun y' _ => ?_
      simp only [nOp, hfS y']
      rw [← integral_const_mul, ← integral_mul_const]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      dsimp only
      ring
    · intro y' hy'
      simp only [nOp, hf0 y' hy', mul_zero, zero_mul]

  have hint : Integrable (Function.uncurry fun y' y => φ y * (A.psiK ψ ((u : A.K) * x * A.NL y') *
      A.kerL ψ x y y' * A.kerL ψ x y' z)) ((μ.restrict Λ).prod (μ.restrict S)) := by
    rw [Measure.prod_restrict]
    have hc : Continuous fun p : A.L × A.L => φ p.2 * (A.psiK ψ ((u : A.K) * x * A.NL p.1) *
        A.kerL ψ x p.2 p.1 * A.kerL ψ x p.1 z) :=
      (hφc.comp continuous_snd).mul (((hec.comp (continuous_const.mul (hNc.comp continuous_fst))).mul
        (hk2.comp continuous_swap)).mul (hk2.comp (continuous_fst.prodMk continuous_const)))
    exact hc.continuousOn.integrableOn_compact (hΛc.prod hSc)
  have e2 := integral_integral_swap hint

  have e3 : ∀ y ∈ S, ∫ y' in (Λ : Set A.L), φ y * (A.psiK ψ ((u : A.K) * x * A.NL y') * A.kerL ψ x y y' *
      A.kerL ψ x y' z) ∂μ = φ y * (G * A.psiK ψ (-(ui * x * A.NL (y + z)))) := by
    intro y hy
    have hw : ui • (y + z) ∈ Λ := hCΛ (Or.inr ⟨y, hy, rfl⟩)
    have hpt : (fun y' => φ y * (A.psiK ψ ((u : A.K) * x * A.NL y') * A.kerL ψ x y y' * A.kerL ψ x y' z)) =
        fun y' => (φ y * A.psiK ψ (-(ui * x * A.NL (y + z)))) * A.psiK ψ ((u : A.K) * x * A.NL (ui • (y + z) + y')) := by
      funext y'
      have h3 : A.psiK ψ ((u : A.K) * x * A.NL y') * A.kerL ψ x y y' * A.kerL ψ x y' z =
          A.psiK ψ (-(ui * x * A.NL (y + z))) * A.psiK ψ ((u : A.K) * x * A.NL (ui • (y + z) + y')) := by
        simp only [Et.kerL]
        rw [← psiK_add, ← psiK_add, ← psiK_add]
        congr 1
        rw [NL_add A (ui • (y + z)) y', NL_smul, tr_symm A (ui • (y + z)) y', tr_smul_right, tr_add_right,
          tr_symm A y y']
        linear_combination (-(ui * x * A.NL (y + z)) - (x : A.K) * (Algebra.trace A.K A.L (star y' * y) +
          Algebra.trace A.K A.L (star y' * z))) * huui
      rw [h3]; ring
    have hT : ∫ y' in (Λ : Set A.L), A.psiK ψ ((u : A.K) * x * A.NL (ui • (y + z) + y')) ∂μ = G := by
      rw [← hGΛ]
      exact setIntegral_add_left_mem μ Λ hΛm (fun t => A.psiK ψ ((u : A.K) * x * A.NL t)) _ hw
    rw [hpt, integral_const_mul, hT]
    ring

  rw [e1, e2, setIntegral_congr_fun hSm e3]
  show _ = G * A.psiK ψ (-ui * x * A.NL z) *
    ∫ y, nOp A ψ (x : A.K) (-ui) φ y * A.kerL ψ x y (-ui • z) ∂μ
  have hR : ∫ y, nOp A ψ (x : A.K) (-ui) φ y * A.kerL ψ x y (-ui • z) ∂μ =
      ∫ y in S, nOp A ψ (x : A.K) (-ui) φ y * A.kerL ψ x y (-ui • z) ∂μ :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
      simp only [nOp, hφ0 y hy, mul_zero, zero_mul]).symm
  rw [hR, ← integral_const_mul]
  refine setIntegral_congr_fun hSm fun y _ => ?_
  simp only [nOp, Et.kerL]
  have h4 : -(ui * x * A.NL (y + z)) = -ui * x * A.NL z +
      (-ui * x * A.NL y + (x : A.K) * Algebra.trace A.K A.L (star y * (-ui • z))) := by
    rw [NL_add, tr_smul_right]; ring
  rw [h4, psiK_add, psiK_add]
  ring

end GlobalTheory.JR.WeilQuad
