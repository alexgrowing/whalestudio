import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryLatticeStabilizerDetRoot
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralRpowNegChangeOfVariable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeWithDensityDetNormSqStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagLeviRealPlacesProductMeasureStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsScalarStableLatticeAutomorphismFundamentalStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

namespace GlobalTheory.FlagBase.LeviInt

theorem lintegral_pi_succ {a : ℕ} {X : Fin (a + 1) → Type} [∀ i, MeasurableSpace (X i)] (ν : ∀ i, Measure (X i))
    [∀ i, SigmaFinite (ν i)] (f : (∀ i, X i) → ENNReal) (hf : Measurable f) :
    ∫⁻ z, f z ∂Measure.pi ν =
      ∫⁻ x, ∫⁻ y, f (Fin.insertNth 0 x y) ∂(Measure.pi fun i => ν (Fin.succAbove 0 i)) ∂ν 0 := by
  rw [← (MeasurePreserving.symm _ (measurePreserving_piFinSuccAbove ν 0)).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _) f]
  refine (lintegral_prod (fun q => f ((MeasurableEquiv.piFinSuccAbove X 0).symm q)) ?_).trans ?_
  · exact (hf.comp (MeasurableEquiv.measurable _)).aemeasurable
  · rfl

theorem measurable_insertNth {a : ℕ} {X : Fin (a + 1) → Type} [∀ i, MeasurableSpace (X i)] :
    Measurable fun q : X 0 × (∀ i, X (Fin.succAbove 0 i)) => (Fin.insertNth 0 q.1 q.2 : ∀ i, X i) := by
  exact (MeasurableEquiv.piFinSuccAbove X 0).symm.measurable

theorem lintegral_pi_comp (ρ : Measure ℝ) [SigmaFinite ρ] : ∀ (a : ℕ) (X : Fin a → Type)
    [∀ i, MeasurableSpace (X i)] (ν : ∀ i, Measure (X i)) [∀ i, SigmaFinite (ν i)] (p : ∀ i, X i → ℝ)
    (w : Fin a → ℝ → ENNReal) (s : Fin a → ENNReal), (∀ i, Measurable (p i)) → (∀ i, Measurable (w i)) →
    (∀ i (G : ℝ → ENNReal), Measurable G → ∫⁻ x, G (p i x) ∂ν i = s i * ∫⁻ t, G t * w i t ∂ρ) →
    ∀ F : (Fin a → ℝ) → ENNReal, Measurable F → ∫⁻ z, F (fun i => p i (z i)) ∂Measure.pi ν =
      (∏ i, s i) * ∫⁻ τ, F τ * ∏ i, w i (τ i) ∂Measure.pi fun _ => ρ := by
  intro a
  induction a with
  | zero =>
    intro X _ ν _ p w s hp hw hs F hF
    rw [lintegral_unique, lintegral_unique, Measure.pi_univ, Measure.pi_univ]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul, mul_one]
    all_goals exact congrArg F (Subsingleton.elim _ _)
  | succ a ih =>
    intro X _ ν _ p w s hp hw hs F hF
    have hprod : Measurable fun τ : Fin a → ℝ => ∏ i, w (Fin.succAbove 0 i) (τ i) :=
      Finset.measurable_prod _ fun i _ => (hw _).comp (measurable_pi_apply i)
    have hK : Measurable fun q : ℝ × (Fin a → ℝ) =>
        F (Fin.insertNth 0 q.1 q.2) * ∏ i, w (Fin.succAbove 0 i) (q.2 i) :=
      (hF.comp (measurable_insertNth (X := fun _ => ℝ))).mul (hprod.comp measurable_snd)
    have hKt : ∀ t : ℝ, Measurable fun τ : Fin a → ℝ =>
        F (Fin.insertNth 0 t τ) * ∏ i, w (Fin.succAbove 0 i) (τ i) := by
      intro t
      have hc : Measurable fun τ : Fin a → ℝ => ((t, τ) : ℝ × (Fin a → ℝ)) :=
        by fun_prop
      exact hK.comp hc
    obtain ⟨H, hHdef⟩ : ∃ H : ℝ → ENNReal, ∀ t, H t = ∫⁻ τ, F (Fin.insertNth 0 t τ) *
        ∏ i, w (Fin.succAbove 0 i) (τ i) ∂Measure.pi (fun _ : Fin a => ρ) := ⟨_, fun t => rfl⟩
    have hH : Measurable H := by
      have hHf : H = fun t => ∫⁻ τ, F (Fin.insertNth 0 t τ) *
          ∏ i, w (Fin.succAbove 0 i) (τ i) ∂Measure.pi (fun _ : Fin a => ρ) := funext hHdef
      rw [hHf]
      exact hK.lintegral_prod_right'
    have hinner : ∀ x : X 0, ∫⁻ y, F (fun i => p i (Fin.insertNth 0 x y i))
        ∂Measure.pi (fun i => ν (Fin.succAbove 0 i)) = (∏ i, s (Fin.succAbove 0 i)) * H (p 0 x) := by
      intro x
      have hfun : ∀ y : (∀ i, X (Fin.succAbove 0 i)), (fun i => p i (Fin.insertNth 0 x y i)) =
          Fin.insertNth (α := fun _ => ℝ) 0 (p 0 x) (fun i => p (Fin.succAbove 0 i) (y i)) := by
        intro y
        clear ih hs hw hprod hK hKt hHdef hH
        symm
        rw [Fin.insertNth_eq_iff]
        constructor
        · simp only [Fin.insertNth_apply_same]
        · funext k
          show p (Fin.succAbove 0 k) (y k) = p (Fin.succAbove 0 k) (Fin.insertNth 0 x y (Fin.succAbove 0 k))
          rw [Fin.insertNth_apply_succAbove]
      have hFx : Measurable fun τ : Fin a → ℝ => F (Fin.insertNth 0 (p 0 x) τ) := by
        have hc : Measurable fun τ : Fin a → ℝ => ((p 0 x, τ) : ℝ × (Fin a → ℝ)) :=
          by fun_prop
        exact (hF.comp (measurable_insertNth (X := fun _ => ℝ))).comp hc
      refine (lintegral_congr fun y => congrArg F (hfun y)).trans ?_
      rw [hHdef]
      exact ih (fun i => X (Fin.succAbove 0 i)) (fun i => ν (Fin.succAbove 0 i))
        (fun i => p (Fin.succAbove 0 i)) (fun i => w (Fin.succAbove 0 i)) (fun i => s (Fin.succAbove 0 i))
        (fun i => hp _) (fun i => hw _) (fun i => hs _) (fun τ => F (Fin.insertNth 0 (p 0 x) τ)) hFx
    have hR : ∀ t, ∫⁻ τ, F (Fin.insertNth 0 t τ) * ∏ i, w i (Fin.insertNth (α := fun _ => ℝ) 0 t τ i)
        ∂Measure.pi (fun _ : Fin a => ρ) = w 0 t * H t := by
      intro t
      rw [hHdef]
      calc _ = ∫⁻ τ, w 0 t * (F (Fin.insertNth 0 t τ) * ∏ i, w (Fin.succAbove 0 i) (τ i))
              ∂Measure.pi (fun _ : Fin a => ρ) := by
            refine lintegral_congr fun τ => ?_
            rw [Fin.prod_univ_succAbove _ 0]
            simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
            ring
        _ = _ := lintegral_const_mul _ (hKt t)
    have hmL : Measurable fun z : (∀ i, X i) => F (fun i => p i (z i)) :=
      hF.comp (measurable_pi_lambda _ fun i => (hp i).comp (measurable_pi_apply i))
    have hmR : Measurable fun τ : Fin (a + 1) → ℝ => F τ * ∏ i, w i (τ i) :=
      hF.mul (Finset.measurable_prod _ fun i _ => (hw i).comp (measurable_pi_apply i))
    calc ∫⁻ z, F (fun i => p i (z i)) ∂Measure.pi ν
        = ∫⁻ x, ∫⁻ y, F (fun i => p i (Fin.insertNth 0 x y i))
            ∂Measure.pi (fun i => ν (Fin.succAbove 0 i)) ∂ν 0 := lintegral_pi_succ ν _ hmL
      _ = ∫⁻ x, (∏ i, s (Fin.succAbove 0 i)) * H (p 0 x) ∂ν 0 := lintegral_congr fun x => hinner x
      _ = (∏ i, s (Fin.succAbove 0 i)) * (s 0 * ∫⁻ t, H t * w 0 t ∂ρ) := by
          have hHp : Measurable fun x => H (p 0 x) := hH.comp (hp 0)
          rw [lintegral_const_mul _ hHp]
          rw [show ∫⁻ x, H (p 0 x) ∂ν 0 = _ from hs 0 H hH]
      _ = (∏ i, s i) * ∫⁻ t, w 0 t * H t ∂ρ := by
          rw [Fin.prod_univ_succAbove s 0]
          simp_rw [mul_comm (H _) (w 0 _)]
          ring
      _ = (∏ i, s i) * ∫⁻ t, ∫⁻ τ, F (Fin.insertNth 0 t τ) *
            ∏ i, w i (Fin.insertNth (α := fun _ => ℝ) 0 t τ i) ∂Measure.pi (fun _ : Fin a => ρ) ∂ρ := by
          congr 1
          exact lintegral_congr fun t => (hR t).symm
      _ = (∏ i, s i) * ∫⁻ τ, F τ * ∏ i, w i (τ i) ∂Measure.pi fun _ => ρ := by
          congr 1
          exact (lintegral_pi_succ (fun _ => ρ) _ hmR).symm

theorem covol_ne_zero {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T1Space G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
    [μ.IsOpenPosMeasure] (Γ : Set G) (hc : Γ.Countable) (hm : ∀ x ∈ Γ, ∀ y ∈ Γ, x⁻¹ * y ∈ Γ)
    (hf : ∀ C, IsCompact C → (Γ ∩ C).Finite) : covol Γ μ Set.univ ≠ 0 := by
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (1 : G)
  have hfin : ((Γ ∩ K) \ {1}).Finite := (hf K hK).subset Set.sdiff_subset
  have hW : interior K ∩ ((Γ ∩ K) \ {1})ᶜ ∈ nhds (1 : G) := by
    refine Filter.inter_mem (interior_mem_nhds.2 hKn) ?_
    exact hfin.isClosed.isOpen_compl.mem_nhds (by simp)
  obtain ⟨U, hUo, hU1, hUU⟩ := exists_open_nhds_one_mul_subset hW
  have hsep : ∀ x ∈ U, ∀ y, y⁻¹ ∈ U → x * y⁻¹ ∈ interior K ∩ ((Γ ∩ K) \ {1})ᶜ :=
    fun x hx y hy => hUU (Set.mul_mem_mul hx hy)
  have hpos : 0 < μ (U ∩ U⁻¹) := (hUo.inter hUo.inv).measure_pos μ ⟨1, hU1, by simpa using hU1⟩
  refine (lt_of_lt_of_le hpos ?_).ne'
  unfold covol
  refine le_iInf fun D => le_iInf fun hD => le_iInf fun hcov => ?_
  haveI : Countable Γ := hc.to_subtype
  let S : Γ → Set G := fun γ => D ∩ {y | (γ : G)⁻¹ * y ∈ U ∩ U⁻¹}
  have hSm : ∀ γ, MeasurableSet (S γ) := fun γ =>
    hD.inter ((hUo.inter hUo.inv).preimage (continuous_const.mul continuous_id)).measurableSet
  have hdisj : Pairwise (Function.onFun Disjoint S) := by
    intro γ γ' hne
    refine Set.disjoint_left.2 fun y hy hy' => hne ?_
    have h1 := hsep _ hy.2.1 ((γ' : G)⁻¹ * y) hy'.2.2
    have h2 : (γ : G)⁻¹ * γ' ∈ Γ := hm _ γ.2 _ γ'.2
    have h3 : (γ : G)⁻¹ * y * ((γ' : G)⁻¹ * y)⁻¹ = (γ : G)⁻¹ * γ' := by group
    rw [h3] at h1
    have h4 : (γ : G)⁻¹ * γ' = 1 := by
      by_contra h5
      exact h1.2 ⟨⟨h2, interior_subset h1.1⟩, h5⟩
    exact Subtype.ext (inv_mul_eq_one.1 h4)
  calc μ (U ∩ U⁻¹) ≤ μ (⋃ γ : Γ, (fun h => (γ : G) * h) ⁻¹' S γ) := by
        refine measure_mono fun x hx => ?_
        obtain ⟨γ, hγ, hγx⟩ := hcov x (Set.mem_univ x)
        exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, hγx, by simpa using hx⟩
    _ ≤ ∑' γ : Γ, μ ((fun h => (γ : G) * h) ⁻¹' S γ) := measure_iUnion_le _
    _ = ∑' γ : Γ, μ (S γ) := by simp only [measure_preimage_mul]
    _ = μ (⋃ γ, S γ) := (measure_iUnion hdisj hSm).symm
    _ ≤ μ D := measure_mono (Set.iUnion_subset fun γ => Set.inter_subset_left)

theorem one_mem_latGroup (I : AutInst) (xf : I.Gf) : 1 ∈ latGroup I xf := by
  refine ⟨1, by exact (GlobalTheory.RatDiscrete.ratSub I).one_mem, rfl, ?_⟩
  show xf⁻¹ * 1 * xf ∈ I.Kset
  rw [mul_one, inv_mul_cancel]
  exact (Formalism.UG.stabGL I.Lf).one_mem

theorem covol_latGroup_ne_zero (I : AutInst) (xf : I.Gf) :
    covol (latGroup I xf) (Measure.pi fun v => Formalism.REAL.muG (I.ε v)) Set.univ ≠ 0 := by
  obtain ⟨-, -, -, hKc, -, ⟨Ksub, hKsub⟩, -⟩ := GlobalTheory.CongTop.adelic_topology I
  refine covol_ne_zero _ (latGroup I xf) ?_ ?_ ?_
  · refine ((GlobalTheory.RatDiscrete.countable_GFset I).image Prod.fst).mono ?_
    rintro g ⟨γ, hγ, h1, -⟩
    exact ⟨γ, hγ, h1⟩
  · rintro x ⟨γ, hγ, rfl, hγK⟩ y ⟨δ, hδ, rfl, hδK⟩
    refine ⟨γ⁻¹ * δ, (GlobalTheory.RatDiscrete.ratSub I).mul_mem ((GlobalTheory.RatDiscrete.ratSub I).inv_mem hγ) hδ,
      rfl, ?_⟩
    rw [← hKsub] at hγK hδK ⊢
    have h : xf⁻¹ * (γ⁻¹ * δ).2 * xf = (xf⁻¹ * γ.2 * xf)⁻¹ * (xf⁻¹ * δ.2 * xf) := by
      rw [Prod.snd_mul, Prod.snd_inv]
      group
    rw [h]
    exact Ksub.mul_mem (Ksub.inv_mem hγK) hδK
  · intro C hC
    have hC' : IsCompact (C ×ˢ ((fun k => xf * k * xf⁻¹) '' I.Kset)) :=
      hC.prod (hKc.image ((continuous_const.mul continuous_id).mul continuous_const))
    refine ((GlobalTheory.RatDiscrete.finite_inter I hC').image Prod.fst).subset ?_
    rintro g ⟨⟨γ, hγ, rfl, hγK⟩, hgC⟩
    refine ⟨γ, ⟨⟨hgC, xf⁻¹ * γ.2 * xf, hγK, ?_⟩, hγ⟩, rfl⟩
    group

theorem le_mul_covol {G : Type} [Monoid G] [MeasurableSpace G] (Γ : Set G) (μ : Measure G) (h1 : 1 ∈ Γ)
    (h0 : covol Γ μ Set.univ ≠ 0) (L X : ENNReal)
    (h : ∀ D, MeasurableSet D → (∀ x ∈ Set.univ, ∃ γ ∈ Γ, γ * x ∈ D) → L ≤ X * μ D) :
    L ≤ X * covol Γ μ Set.univ := by
  by_cases hX0 : X = 0
  · have hL := h Set.univ MeasurableSet.univ (fun x _ => ⟨1, h1, Set.mem_univ _⟩)
    rw [hX0, zero_mul] at hL ⊢
    exact hL
  by_cases hXt : X = ⊤
  · rw [hXt, ENNReal.top_mul h0]
    exact le_top
  unfold covol
  rw [ENNReal.mul_iInf_of_ne hX0 hXt]
  refine le_iInf fun D => ?_
  rw [ENNReal.mul_iInf_of_ne hX0 hXt]
  refine le_iInf fun hD => ?_
  rw [ENNReal.mul_iInf_of_ne hX0 hXt]
  exact le_iInf fun hcov => h D hD hcov

section GenLin

variable {E : Type} [Field E] [NumberField E] {j : ℕ}

theorem measurable_detNorm : Measurable (detNorm E j) := by
  have hc : Continuous fun x : InfinitePlace E → Fin j → Fin j → ℂ =>
      ∏ w, ‖(Matrix.of (x w)).det‖ ^ 2 := by
    refine continuous_finsetProd _ fun w _ => ?_
    exact ((Continuous.matrix_det (continuous_apply w :
      Continuous fun x : InfinitePlace E → Fin j → Fin j → ℂ => Matrix.of (x w))).norm).pow 2
  exact hc.measurable

theorem sigmaFinite_haarGL : SigmaFinite (haarGL E j) := by
  haveI h1 : SigmaFinite (volume : Measure (Fin j → ℂ)) := by rw [volume_pi]; infer_instance
  haveI h2 : SigmaFinite (volume : Measure (Fin j → Fin j → ℂ)) := by rw [volume_pi]; infer_instance
  haveI h3 : SigmaFinite (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) := by
    rw [volume_pi]; infer_instance
  show SigmaFinite ((volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)).withDensity
    fun x => ENNReal.ofReal ((∏ w, ‖(Matrix.of (x w)).det‖ ^ 2)⁻¹ ^ j))
  exact SigmaFinite.withDensity_ofReal _

theorem detNorm_aut_mul (hE : IsTotallyComplex E) {Λ : Submodule (𝓞 E) (Fin j → E)} (hΛ : Submodule.IsLattice E Λ)
    {γ : MatInf E j} (hγ : γ ∈ autGL E j Λ) (g : MatInf E j) : detNorm E j (γ * g) = detNorm E j g := by
  obtain ⟨γ', hγΛ, hγw⟩ := hγ

  have hstab : ∀ a : 𝓞 E, ∀ y ∈ Submodule.span ℚ (Λ : Set (Fin j → E)),
      (a : E) • y ∈ Submodule.span ℚ (Λ : Set (Fin j → E)) := by
    intro a y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      refine Submodule.subset_span ?_
      have e1 : ((a : E) • x : Fin j → E) = a • x := algebraMap_smul E a x
      rw [e1]
      exact Λ.smul_mem a hx
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
    | smul q x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ q hx
  have hEstab : ∀ e : E, ∀ y ∈ Submodule.span ℚ (Λ : Set (Fin j → E)),
      e • y ∈ Submodule.span ℚ (Λ : Set (Fin j → E)) := by
    intro e y hy
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (Rₘ := ℚ)
      (nonZeroDivisors ℤ) e (Algebra.IsIntegral.isIntegral e)
    have hint : IsIntegral ℤ ((m : ℤ) • e) := by rwa [Submonoid.smul_def] at hm
    obtain ⟨n, hn⟩ : ∃ n : ℤ, n = m := ⟨_, rfl⟩
    have hn0 : n ≠ 0 := hn ▸ nonZeroDivisors.coe_ne_zero m
    rw [← hn] at hint
    have h1 := hstab ⟨n • e, hint⟩ y hy
    have hn' : (n : E) ≠ 0 := Int.cast_ne_zero.2 hn0
    have h2 : e • y = ((n : ℚ)⁻¹) • (((⟨n • e, hint⟩ : 𝓞 E) : E) • y) := by
      funext i
      show e * y i = ((n : ℚ)⁻¹) • ((n • e) * y i)
      rw [Rat.smul_def, zsmul_eq_mul, Rat.cast_inv, Rat.cast_intCast, ← mul_assoc, ← mul_assoc,
        inv_mul_cancel₀ hn', one_mul]
    rw [h2]
    exact Submodule.smul_mem _ _ h1
  have hspanQ : Submodule.span ℚ (Λ : Set (Fin j → E)) = ⊤ := by
    let M : Submodule E (Fin j → E) :=
      { carrier := Submodule.span ℚ (Λ : Set (Fin j → E))
        add_mem' := fun hx hy => Submodule.add_mem _ hx hy
        zero_mem' := Submodule.zero_mem _
        smul_mem' := fun e y hy => hEstab e y hy }
    have hle : Submodule.span E (Λ : Set (Fin j → E)) ≤ M :=
      Submodule.span_le.2 fun x hx => Submodule.subset_span hx
    rw [hΛ.span_eq_top] at hle
    exact eq_top_iff.2 fun x _ => hle Submodule.mem_top

  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hΛ.fg
  haveI : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 E) Λ
  haveI : NoZeroSMulDivisors ℤ Λ :=
    Subtype.val_injective.noZeroSMulDivisors _ rfl fun c x => rfl
  haveI : Module.Free ℤ Λ := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis ℤ Λ
  let f : Λ →ₗ[ℤ] (Fin j → E) := Λ.subtype.toAddMonoidHom.toIntLinearMap
  have hvZ : LinearIndependent ℤ (fun k => (b k : Fin j → E)) :=
    b.linearIndependent.map' f (LinearMap.ker_eq_bot.2 Subtype.val_injective)
  have hvQ : LinearIndependent ℚ (fun k => (b k : Fin j → E)) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).1 hvZ
  have hspv : ⊤ ≤ Submodule.span ℚ (Set.range fun k => (b k : Fin j → E)) := by
    rw [← hspanQ]
    refine Submodule.span_le.2 fun x hx => ?_
    have h1 : x ∈ Submodule.span ℤ (Set.range fun k => (b k : Fin j → E)) := by
      have h := Submodule.mem_map_of_mem (f := f) (b.mem_span ⟨x, hx⟩)
      rw [Submodule.map_span, ← Set.range_comp] at h
      exact h
    exact Submodule.span_le_restrictScalars ℤ ℚ _ h1
  let bQ := Module.Basis.mk hvQ hspv
  have hcoord : ∀ y : Λ, ∀ l, bQ.repr (y : Fin j → E) l = (b.repr y l : ℚ) := by
    intro y l
    have hy : (y : Fin j → E) = ∑ m, ((b.repr y m : ℚ)) • bQ m := by
      conv_lhs => rw [← b.sum_repr y]
      rw [Submodule.coe_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Module.Basis.mk_apply, Int.cast_smul_eq_zsmul]
      rfl
    rw [hy, bQ.repr_sum_self]

  have hA'Λ : ∀ y ∈ Λ, (↑γ'⁻¹ : Matrix (Fin j) (Fin j) E) *ᵥ y ∈ Λ := by
    intro y hy
    refine (hγΛ _).1 ?_
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    exact hy
  let Fo : Λ →ₗ[𝓞 E] Λ := ((Matrix.toLin' (γ' : Matrix (Fin j) (Fin j) E)).restrictScalars (𝓞 E)).restrict
    (p := Λ) (q := Λ) fun y hy => (hγΛ y).2 hy
  let Go : Λ →ₗ[𝓞 E] Λ := ((Matrix.toLin' (↑γ'⁻¹ : Matrix (Fin j) (Fin j) E)).restrictScalars (𝓞 E)).restrict
    (p := Λ) (q := Λ) fun y hy => hA'Λ y hy
  let Fz : Λ →ₗ[ℤ] Λ := Fo.restrictScalars ℤ
  let Gz : Λ →ₗ[ℤ] Λ := Go.restrictScalars ℤ
  have hFG : Fz ∘ₗ Gz = LinearMap.id := by
    refine LinearMap.ext fun y => Subtype.ext ?_
    show (γ' : Matrix (Fin j) (Fin j) E) *ᵥ ((↑γ'⁻¹ : Matrix (Fin j) (Fin j) E) *ᵥ (y : Fin j → E)) = y
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hmul : LinearMap.det Fz * LinearMap.det Gz = 1 := by
    rw [← LinearMap.det_comp, hFG, LinearMap.det_id]
  have hunit : IsUnit (LinearMap.det Fz) := ⟨⟨_, _, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩
  have hz := Int.isUnit_iff.1 hunit
  have hdetQ : LinearMap.det ((Matrix.toLin' (γ' : Matrix (Fin j) (Fin j) E)).restrictScalars ℚ) =
      ((LinearMap.det Fz : ℤ) : ℚ) := by
    rw [← LinearMap.det_toMatrix bQ, ← LinearMap.det_toMatrix b]
    rw [show ((LinearMap.toMatrix b b Fz).det : ℚ) =
      ((Int.castRingHom ℚ).mapMatrix (LinearMap.toMatrix b b Fz)).det from by rw [← RingHom.map_det]; rfl]
    congr 1
    ext l k
    rw [LinearMap.toMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply,
      Module.Basis.mk_apply]
    exact hcoord (Fz (b k)) l
  have hnorm : ((|Algebra.norm ℚ (γ' : Matrix (Fin j) (Fin j) E).det| : ℚ) : ℝ) = 1 := by
    have h1 : LinearMap.det ((Matrix.toLin' (γ' : Matrix (Fin j) (Fin j) E)).restrictScalars ℚ) =
        Algebra.norm ℚ (γ' : Matrix (Fin j) (Fin j) E).det := by
      rw [LinearMap.det_restrictScalars, LinearMap.det_toLin']
    rw [← h1, hdetQ]
    rcases hz with h | h <;> rw [h] <;> norm_num

  have hprod : ∏ w : InfinitePlace E, ‖(Matrix.of (γ w)).det‖ ^ 2 = 1 := by
    have h1 : ∀ w : InfinitePlace E,
        (Matrix.of (γ w)).det = w.embedding (γ' : Matrix (Fin j) (Fin j) E).det := by
      intro w
      rw [RingHom.map_det]
      congr 1
      ext a c
      exact hγw w a c
    have h2 : ∀ w : InfinitePlace E, w.mult = 2 := fun w => by
      unfold InfinitePlace.mult
      rw [if_neg (InfinitePlace.not_isReal_iff_isComplex.2 (hE.isComplex w))]
    simp_rw [h1, InfinitePlace.norm_embedding_eq]
    rw [← hnorm, ← InfinitePlace.prod_eq_abs_norm]
    simp_rw [h2]
  unfold detNorm
  have h3 : ∀ w, (Matrix.of ((γ * g) w)).det = (Matrix.of (γ w)).det * (Matrix.of (g w)).det :=
    fun w => by rw [← Matrix.det_mul]; rfl
  simp_rw [h3, norm_mul, mul_pow, Finset.prod_mul_distrib, hprod, one_mul]

theorem haarGL_restrict (hj : 1 ≤ j) : (haarGL E j).restrict {g | 0 < detNorm E j g} = haarGL E j := by
  have hm : MeasurableSet {g : MatInf E j | ¬ 0 < detNorm E j g} :=
    (measurableSet_lt measurable_const measurable_detNorm).compl
  refine Measure.restrict_eq_self_of_ae_mem ?_
  rw [ae_iff]
  show haarGL E j {g | ¬ 0 < detNorm E j g} = 0
  have key : (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)).withDensity
      (fun x => ENNReal.ofReal ((∏ w, ‖(Matrix.of (x w)).det‖ ^ 2)⁻¹ ^ j))
      {x | ¬ 0 < ∏ w, ‖(Matrix.of (x w)).det‖ ^ 2} = 0 := by
    have hm2 : MeasurableSet
        {x : InfinitePlace E → Fin j → Fin j → ℂ | ¬ 0 < ∏ w, ‖(Matrix.of (x w)).det‖ ^ 2} := hm
    rw [withDensity_apply _ hm2, ← lintegral_indicator hm2]
    have hz : {x : InfinitePlace E → Fin j → Fin j → ℂ | ¬ 0 < ∏ w, ‖(Matrix.of (x w)).det‖ ^ 2}.indicator
        (fun x => ENNReal.ofReal ((∏ w, ‖(Matrix.of (x w)).det‖ ^ 2)⁻¹ ^ j)) = 0 := by
      funext x
      refine Set.indicator_apply_eq_zero.2 fun hx => ?_
      have h0 : ∏ w, ‖(Matrix.of (x w)).det‖ ^ 2 = 0 :=
        le_antisymm (not_lt.1 hx) (Finset.prod_nonneg fun w _ => sq_nonneg _)
      rw [h0, _root_.inv_zero, zero_pow (by omega), ENNReal.ofReal_zero]
    rw [hz]
    exact lintegral_zero
  exact key

theorem exists_dom (hE : IsTotallyComplex E) (hj : 1 ≤ j) {Λ : Submodule (𝓞 E) (Fin j → E)}
    (hΛ : Submodule.IsLattice E Λ) {N κ : ℝ} (hN : 0 < N) (hκ : 0 < κ) :
    ∃ D : Set (MatInf E j), MeasurableSet D ∧ D ⊆ {g | 0 < detNorm E j g} ∧
      (∀ g, 0 < detNorm E j g → ∃ γ ∈ autGL E j Λ, γ * g ∈ D) ∧
      ∀ G : ℝ → ENNReal, Measurable G → ∫⁻ x in D, G ((detNorm E j x / κ) ^ (-(1 / N))) ∂haarGL E j =
        slabVol E j Λ * ∫⁻ t in Set.Ioi (0 : ℝ), G t * ENNReal.ofReal (N / t) := by
  obtain ⟨D, hDm, hDpos, hDcov, -, hDint⟩ := GlobalTheory.T.exists_scalarStable_latticeAutomorphismFundamentalDomain E hE j Λ hΛ
  refine ⟨D, hDm, hDpos, hDcov, fun G hG => ?_⟩
  have hAm : MeasurableSet {g : MatInf E j | 0 < detNorm E j g} :=
    measurableSet_lt measurable_const measurable_detNorm
  have hF : Measurable fun t : ℝ => G ((t / κ) ^ (-(1 / N))) :=
    hG.comp ((measurable_id.div_const κ).pow_const (-(1 / N)))
  have hGd : Measurable fun x : MatInf E j => G ((detNorm E j x / κ) ^ (-(1 / N))) :=
    hF.comp measurable_detNorm
  have h1 := hDint (fun x => G ((detNorm E j x / κ) ^ (-(1 / N)))) {g | 0 < detNorm E j g}
    (hGd.indicator hAm)
    (fun γ hγ g _ => by beta_reduce; rw [detNorm_aut_mul hE hΛ hγ g])
    hAm (fun _ h => h)
    (fun γ hγ g hg => by
      show 0 < detNorm E j (γ * g)
      rw [detNorm_aut_mul hE hΛ hγ g]
      exact hg)
  rw [haarGL_restrict hj, Set.inter_eq_right.2 hDpos] at h1
  beta_reduce at h1
  rw [← h1]
  have h2 := GlobalTheory.T.leftQuotientCovolume_withDensity_detNormSq E hE j hj Λ hΛ (fun t => G ((t / κ) ^ (-(1 / N)))) hF
  beta_reduce at h2
  rw [h2, GlobalTheory.FlagMeas.lintegral_rpow_neg_change_of_variable N κ hN hκ G hG]
  rfl

end GenLin

theorem covol_leviGroup_le : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), (∀ i, 1 ≤ j i) → IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ (μM : ∀ v, Measure (Formalism.REAL.UJ (I.ε v))) [∀ v, SigmaFinite (μM v)] (c₀ : InfinitePlace I₀.F → ℝ), (∀ v, IsGaugeSub (flagM (I.ε v) (flagAt I S v)) ((I.n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) (μM v)) → IsGaugeAll I₀ c₀ → ∀ F : (Fin a → ℝ) → ENNReal, Measurable F → covol (leviGroup I xf S) ((Measure.pi μM).withDensity fun m => F (sizesAt I xf S m)) {m | ∀ v, m v ∈ flagM (I.ε v) (flagAt I S v)} ≤ (∏ i, ENNReal.ofReal (2 ^ (I.f * j i ^ 2)) * slabVol I.E (j i) (Λ i)) * (ENNReal.ofReal (∏ v, c₀ v) * covol (latGroup I₀ x₀) (Measure.pi fun v => Formalism.REAL.muG (I₀.ε v)) Set.univ) * ∫⁻ τ in {τ : Fin a → ℝ | ∀ i, 0 < τ i}, F τ * ENNReal.ofReal (∏ i, 2 * (I.f : ℝ) * j i / τ i) := by
  intro I I₀ e xf a j S Λ x₀ T T' T₀ hj hA μM _ c₀ hM hc₀ F hF
  have hPol : ∀ (n : ℕ) (ε : Fin n → Bool), PolishSpace (Formalism.REAL.UJ ε) := fun n ε => by
    haveI : PolishSpace (Matrix (Fin n) (Fin n) ℂ) :=
      inferInstanceAs (PolishSpace (Fin n → Fin n → ℂ))
    exact (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.polishSpace
  have hSB : ∀ i, StandardBorelSpace (MatInf I.E (j i)) := fun i =>
    inferInstanceAs (StandardBorelSpace (InfinitePlace I.E → Fin (j i) → Fin (j i) → ℂ))
  haveI : ∀ i, SigmaFinite (haarGL I.E (j i)) := fun i => sigmaFinite_haarGL
  have hE : IsTotallyComplex I.E := I.cm.cmUnram.1
  have hfpos : (0 : ℝ) < I.f := by
    unfold AutInst.f
    exact Nat.cast_pos.2 Module.finrank_pos
  have hNpos : ∀ i, (0 : ℝ) < 2 * (I.f : ℝ) * j i := fun i =>
    mul_pos (mul_pos two_pos hfpos) (Nat.cast_pos.2 (by have := hj i; omega))
  obtain ⟨Θ, κ, hΘm, hκ, hΘA, hΘγ, hΘsz, hΘinj, hΘint⟩ :=
    GlobalTheory.T.flagLevi_realPlaces_product_measure I I₀ e xf a j S Λ x₀ T T' T₀ hj hA μM c₀ hM hc₀
  choose D hDm hDpos hDcov hDint using fun i =>
    exists_dom hE (hj i) (hA.2.2.1 i) (hNpos i) (hκ i)
  refine le_trans (le_mul_covol (latGroup I₀ x₀) (Measure.pi fun v => Formalism.REAL.muG (I₀.ε v))
      (one_mem_latGroup I₀ x₀) (covol_latGroup_ne_zero I₀ x₀) _
      ((∏ i, ENNReal.ofReal (2 ^ (I.f * j i ^ 2)) * slabVol I.E (j i) (Λ i)) *
        ENNReal.ofReal (∏ v, c₀ v) *
        ∫⁻ τ in {τ : Fin a → ℝ | ∀ i, 0 < τ i}, F τ * ENNReal.ofReal (∏ i, 2 * (I.f : ℝ) * j i / τ i))
      fun D₀ hD₀m hD₀cov => ?_) (le_of_eq (by ring))

  have hPosm : MeasurableSet {z₁ : ∀ i, MatInf I.E (j i) | ∀ i, 0 < detNorm I.E (j i) (z₁ i)} := by
    have : {z₁ : ∀ i, MatInf I.E (j i) | ∀ i, 0 < detNorm I.E (j i) (z₁ i)} =
        Set.univ.pi fun i => {g | 0 < detNorm I.E (j i) g} := by
      ext z; simp
    rw [this]
    exact MeasurableSet.univ_pi fun i => measurableSet_lt measurable_const measurable_detNorm
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Measure ((∀ i, MatInf I.E (j i)) × I₀.Ginf),
      ρ = ((Measure.pi fun i => haarGL I.E (j i)).restrict
        {z₁ | ∀ i, 0 < detNorm I.E (j i) (z₁ i)}).prod (Measure.pi fun v => Formalism.REAL.muG (I₀.ε v)) :=
    ⟨_, rfl⟩
  have hmeas : Measure.pi μM = ((∏ i, ENNReal.ofReal (2 ^ (I.f * j i ^ 2))) *
      ENNReal.ofReal (∏ v, c₀ v)) • Measure.map Θ ρ := by
    ext S hS
    rw [Measure.smul_apply, Measure.map_apply hΘm hS, smul_eq_mul]
    have h1 := hΘint (S.indicator 1) (measurable_one.indicator hS)
    rw [lintegral_indicator_one hS] at h1
    rw [h1]
    congr 1
    rw [← lintegral_indicator_one (hΘm hS), hρ,
      lintegral_prod _ ((measurable_one.indicator (hΘm hS)).aemeasurable)]
    refine lintegral_congr fun z₁ => lintegral_congr fun z₂ => ?_
    rfl
  obtain ⟨C, hC⟩ : ∃ C : ENNReal, C = (∏ i, ENNReal.ofReal (2 ^ (I.f * j i ^ 2))) *
      ENNReal.ofReal (∏ v, c₀ v) := ⟨_, rfl⟩
  rw [← hC] at hmeas
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : (∀ i, MatInf I.E (j i)) → ENNReal, ∀ z₁, ψ z₁ =
      F (fun i => (detNorm I.E (j i) (z₁ i) / κ i) ^ (-(1 / (2 * (I.f : ℝ) * j i)))) :=
    ⟨_, fun _ => rfl⟩
  have hψ : Measurable ψ := by
    have hψf : ψ = fun z₁ => F (fun i => (detNorm I.E (j i) (z₁ i) / κ i) ^ (-(1 / (2 * (I.f : ℝ) * j i)))) :=
      funext hψdef
    rw [hψf]
    exact hF.comp (measurable_pi_lambda _ fun i =>
      ((measurable_detNorm.comp (measurable_pi_apply i)).div_const _).pow_const _)
  have hBoxm : MeasurableSet ((Set.univ.pi D) ×ˢ D₀) := (MeasurableSet.univ_pi hDm).prod hD₀m
  have hBoxpos : ∀ z ∈ (Set.univ.pi D) ×ˢ D₀, ∀ i, 0 < detNorm I.E (j i) (z.1 i) :=
    fun z hz i => hDpos i (hz.1 i (Set.mem_univ i))
  have hDDm : MeasurableSet (Θ '' ((Set.univ.pi D) ×ˢ D₀)) :=
    hBoxm.image_of_measurable_injOn hΘm fun z hz z' hz' h =>
      hΘinj z z' (hBoxpos z hz) (hBoxpos z' hz') h
  have hcov : ∀ m ∈ {m : I.Ginf | ∀ v, m v ∈ flagM (I.ε v) (flagAt I S v)},
      ∃ γ ∈ leviGroup I xf S, γ * m ∈ Θ '' ((Set.univ.pi D) ×ˢ D₀) := by
    intro m hm
    obtain ⟨z', hz'pos, rfl⟩ := (hΘA m).1 hm
    choose g hg hgD using fun i => hDcov i (z'.1 i) (hz'pos i)
    obtain ⟨δ, hδ, hδD⟩ := hD₀cov z'.2 (Set.mem_univ _)
    obtain ⟨γ, hγ, hγeq⟩ := hΘγ (g, δ) z' hg hδ hz'pos
    exact ⟨γ, hγ, (fun i => g i * z'.1 i, δ * z'.2), ⟨fun i _ => hgD i, hδD⟩, hγeq.symm⟩
  have hin : ∀ z₁, ∫⁻ z₂, ((Set.univ.pi D) ×ˢ D₀).indicator (fun z => ψ z.1) (z₁, z₂)
      ∂(Measure.pi fun v => Formalism.REAL.muG (I₀.ε v)) =
      (Set.univ.pi D).indicator ψ z₁ * (Measure.pi fun v => Formalism.REAL.muG (I₀.ε v)) D₀ := by
    intro z₁
    by_cases h : z₁ ∈ Set.univ.pi D
    · rw [Set.indicator_of_mem h, ← lintegral_indicator_const hD₀m]
      refine lintegral_congr fun z₂ => ?_
      by_cases h2 : z₂ ∈ D₀
      · rw [Set.indicator_of_mem (Set.mk_mem_prod h h2), Set.indicator_of_mem h2]
      · rw [Set.indicator_of_notMem (fun hh => h2 hh.2), Set.indicator_of_notMem h2]
    · rw [Set.indicator_of_notMem h, zero_mul]
      exact (lintegral_congr fun z₂ => Set.indicator_of_notMem (fun hh => h hh.1) _).trans lintegral_zero
  have hset : {τ : Fin a → ℝ | ∀ i, 0 < τ i} = Set.univ.pi fun _ => Set.Ioi 0 := by
    ext τ; simp
  have hsetm : MeasurableSet {τ : Fin a → ℝ | ∀ i, 0 < τ i} := by
    rw [hset]; exact MeasurableSet.univ_pi fun _ => measurableSet_Ioi
  have hpi : Measure.pi (fun _ : Fin a => (volume : Measure ℝ).restrict (Set.Ioi 0)) =
      (volume : Measure (Fin a → ℝ)).restrict {τ | ∀ i, 0 < τ i} := by
    rw [hset, volume_pi, Measure.restrict_pi_pi]
  calc covol (leviGroup I xf S) ((Measure.pi μM).withDensity fun m => F (sizesAt I xf S m))
        {m | ∀ v, m v ∈ flagM (I.ε v) (flagAt I S v)}
      ≤ ((Measure.pi μM).withDensity fun m => F (sizesAt I xf S m)) (Θ '' ((Set.univ.pi D) ×ˢ D₀)) := by
        unfold covol
        exact iInf_le_of_le _ (iInf_le_of_le hDDm (iInf_le _ hcov))
    _ = ∫⁻ m, (Θ '' ((Set.univ.pi D) ×ˢ D₀)).indicator (fun m => F (sizesAt I xf S m)) m
          ∂Measure.pi μM := by
        rw [withDensity_apply _ hDDm, lintegral_indicator hDDm]
    _ ≤ C * ∫⁻ z, ((Set.univ.pi D) ×ˢ D₀).indicator (fun z => ψ z.1) z ∂ρ := by
        rw [hmeas, lintegral_smul_measure, smul_eq_mul]
        have hle : ∫⁻ m, (Θ '' ((Set.univ.pi D) ×ˢ D₀)).indicator (fun m => F (sizesAt I xf S m)) m
            ∂Measure.map Θ ρ ≤ ∫⁻ z, ((Set.univ.pi D) ×ˢ D₀).indicator (fun z => ψ z.1) z ∂ρ := by
          refine le_trans (lintegral_map_le _ Θ) (lintegral_mono_ae ?_)
          have hae : ∀ᵐ z ∂ρ, ∀ i, 0 < detNorm I.E (j i) (z.1 i) := by
            rw [hρ]
            exact Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst
              (ae_restrict_mem hPosm)
          filter_upwards [hae] with z hz
          by_cases hzD : Θ z ∈ Θ '' ((Set.univ.pi D) ×ˢ D₀)
          · obtain ⟨z'', hz'', hzz⟩ := hzD
            have hzeq : z'' = z := hΘinj z'' z (hBoxpos z'' hz'') hz hzz
            subst hzeq
            rw [Set.indicator_of_mem (Set.mem_image_of_mem Θ hz''), Set.indicator_of_mem hz'', hψdef]
            exact le_of_eq (congrArg F (funext fun i => hΘsz z'' hz i))
          · rw [Set.indicator_of_notMem hzD]
            exact zero_le'
        exact mul_le_mul' le_rfl hle
    _ ≤ C * ((∫⁻ z₁, (Set.univ.pi D).indicator ψ z₁ ∂(Measure.pi fun i => haarGL I.E (j i))) *
          (Measure.pi fun v => Formalism.REAL.muG (I₀.ε v)) D₀) := by
        refine mul_le_mul' le_rfl ?_
        have hprod : ∫⁻ z, ((Set.univ.pi D) ×ˢ D₀).indicator (fun z => ψ z.1) z
            ∂(((Measure.pi fun i => haarGL I.E (j i)).restrict {z₁ | ∀ i, 0 < detNorm I.E (j i) (z₁ i)}).prod
              (Measure.pi fun v => Formalism.REAL.muG (I₀.ε v))) =
            ∫⁻ z₁ in {z₁ | ∀ i, 0 < detNorm I.E (j i) (z₁ i)}, ∫⁻ z₂, ((Set.univ.pi D) ×ˢ D₀).indicator
              (fun z => ψ z.1) (z₁, z₂) ∂(Measure.pi fun v => Formalism.REAL.muG (I₀.ε v))
              ∂(Measure.pi fun i => haarGL I.E (j i)) :=
          lintegral_prod _ ((hψ.comp measurable_fst).indicator hBoxm).aemeasurable
        rw [hρ, hprod, lintegral_congr hin, lintegral_mul_const _ (hψ.indicator (MeasurableSet.univ_pi hDm))]
        exact mul_le_mul' (setLIntegral_le_lintegral _ _) le_rfl
    _ ≤ C * ((∏ i, slabVol I.E (j i) (Λ i)) *
          (∫⁻ τ in {τ : Fin a → ℝ | ∀ i, 0 < τ i}, F τ * ENNReal.ofReal (∏ i, 2 * (I.f : ℝ) * j i / τ i)) *
          (Measure.pi fun v => Formalism.REAL.muG (I₀.ε v)) D₀) := by
        refine mul_le_mul' le_rfl (mul_le_mul' ?_ le_rfl)
        rw [lintegral_indicator (MeasurableSet.univ_pi hDm), Measure.restrict_pi_pi]
        refine (lintegral_congr fun z => hψdef z).trans_le ?_
        refine (lintegral_pi_comp (volume.restrict (Set.Ioi 0)) a (fun i => MatInf I.E (j i))
          (fun i => (haarGL I.E (j i)).restrict (D i))
          (fun i x => (detNorm I.E (j i) x / κ i) ^ (-(1 / (2 * (I.f : ℝ) * j i))))
          (fun i t => ENNReal.ofReal (2 * (I.f : ℝ) * j i / t)) (fun i => slabVol I.E (j i) (Λ i))
          (fun i => (measurable_detNorm.div_const _).pow_const _)
          (fun i => (measurable_const.div measurable_id).ennreal_ofReal)
          (fun i G hG => hDint i G hG) F hF).trans_le (mul_le_mul' le_rfl ?_)
        rw [hpi]
        refine lintegral_mono_ae ((ae_restrict_mem hsetm).mono fun τ hτ => le_of_eq ?_)
        rw [ENNReal.ofReal_prod_of_nonneg fun i _ => (div_pos (hNpos i) (hτ i)).le]
    _ = _ := by
        rw [hC, Finset.prod_mul_distrib]
        ring

end GlobalTheory.FlagBase.LeviInt
