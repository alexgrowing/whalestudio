import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.UnipBlocks
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.TensInterp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.UnipBlocks

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace
open scoped NumberField.AdeleRing

private theorem cont_int {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] (ρ : Measure Y) [IsFiniteMeasure ρ] {F : X → Y → ℂ}
    (hF : Continuous fun p : X × Y => F p.1 p.2) : Continuous fun x => ∫ y, F x y ∂ρ := by
  let G : C(X, C(Y, ℂ)) := ContinuousMap.curry ⟨fun p : X × Y => F p.1 p.2, hF⟩
  have hI : ∀ f : C(Y, ℂ), Integrable (fun y => f y) ρ := fun f =>
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hL : LipschitzWith (Real.toNNReal (ρ.real Set.univ)) (fun f : C(Y, ℂ) => ∫ y, f y ∂ρ) := by
    refine LipschitzWith.of_dist_le_mul fun f g => ?_
    rw [dist_eq_norm, ← integral_sub (hI f) (hI g), Real.coe_toNNReal _ measureReal_nonneg, dist_eq_norm, mul_comm]
    refine norm_integral_le_of_norm_le_const (Eventually.of_forall fun y => ?_)
    exact (f - g).norm_coe_le_norm y
  exact hL.continuous.comp G.continuous

private theorem avg_mem {X Y : Type} [MeasurableSpace Y] (E : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ E] (ρ : Measure Y)
    (h : Y → X → ℂ) (hE : ∀ y, h y ∈ E) (hi : ∀ x, Integrable (fun y => h y x) ρ) :
    (fun x => ∫ y, h y x ∂ρ) ∈ E := by
  obtain ⟨a, b, φ, ψ, x, y, s, t, hφ, -, hT⟩ := tens E (⊤ : Submodule ℂ (Unit → ℂ))
  have e : ∀ f ∈ E, ∀ u, f u = ∑ l : Fin a × Fin b × Fin a × Fin b,
      (s l.1 l.2.2.1 * t l.2.1 l.2.2.2 * ψ l.2.1 ()) * f (x l.1 l.2.2.1) * φ l.1 u := by
    intro f hf u
    rw [hT (fun u _ => f u) (fun _ => hf) (fun _ => Submodule.mem_top) u ()]
    simp only [Fintype.sum_prod_type, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun p _ =>
      Finset.sum_congr rfl fun q _ => ?_
    ring
  have key : (fun u => ∫ w, h w u ∂ρ) = ∑ l : Fin a × Fin b × Fin a × Fin b,
      ((s l.1 l.2.2.1 * t l.2.1 l.2.2.2 * ψ l.2.1 ()) * ∫ w, h w (x l.1 l.2.2.1) ∂ρ) • φ l.1 := by
    funext u
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have : ∀ w, h w u = ∑ l : Fin a × Fin b × Fin a × Fin b,
        (s l.1 l.2.2.1 * t l.2.1 l.2.2.2 * ψ l.2.1 ()) * h w (x l.1 l.2.2.1) * φ l.1 u := fun w => e _ (hE w) u
    simp only [this]
    rw [integral_finset_sum _ fun l _ => ((hi _).const_mul _).mul_const _]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_mul_const, integral_const_mul]
  rw [key]
  exact E.sum_mem fun l _ => E.smul_mem _ (hφ _)

private def repSub {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    (τ : Submodule ℂ (L2 μ)) : Submodule ℂ (G1 K n → ℂ) where
  carrier := {f | ∃ v ∈ τ, Reps μ v f}
  zero_mem' := ⟨0, τ.zero_mem, by
    filter_upwards [(quasiMeasurePreserving_mk (Gam K n) μ).ae (Lp.coeFn_zero ℂ 2 (quotientMeasure (Gam K n) μ))] with y e
    simpa using e⟩
  add_mem' := by
    rintro f g ⟨v, hv, hf⟩ ⟨w, hw, hg⟩
    refine ⟨v + w, τ.add_mem hv hw, ?_⟩
    filter_upwards [(quasiMeasurePreserving_mk (Gam K n) μ).ae (Lp.coeFn_add v w), hf, hg] with y e1 e2 e3
    rw [e1, Pi.add_apply, e2, e3, Pi.add_apply]
  smul_mem' := by
    rintro c f ⟨v, hv, hf⟩
    refine ⟨c • v, τ.smul_mem c hv, ?_⟩
    filter_upwards [(quasiMeasurePreserving_mk (Gam K n) μ).ae (Lp.coeFn_smul c v), hf] with y e1 e2
    rw [e1, Pi.smul_apply, e2, Pi.smul_apply, smul_eq_mul]

private theorem reps_tr {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    {v : L2 μ} {φ : G1 K n → ℂ} (h : Reps μ v φ) (g : G1 K n) :
    Reps μ (rightRegularRep (Gam K n) μ g v) (fun y => φ (y * g)) := by
  have h1 := (quasiMeasurePreserving_mk (Gam K n) μ).ae (coeFn_rightRegularRep (Gam K n) μ g v)
  have h2 := (measurePreserving_mul_right μ g).quasiMeasurePreserving.ae h
  filter_upwards [h1, h2] with y e1 e2
  rw [e1]
  exact e2

private theorem span_le_rep {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    (τ : Submodule ℂ (L2 μ)) (hτ : CuspIrr μ τ) (S : Subgroup (G1 K n)) {φ : G1 K n → ℂ} (h : ∃ v ∈ τ, Reps μ v φ) :
    Submodule.span ℂ (Set.range fun k : S => fun m => φ (m * k)) ≤ repSub μ τ := by
  obtain ⟨v, hv, hr⟩ := h
  refine Submodule.span_le.2 ?_
  rintro _ ⟨k, rfl⟩
  exact ⟨_, hτ.inv _ v hv, reps_tr μ hr k⟩

private theorem int_cont {Y : Type} [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (ρ : Measure Y) [IsFiniteMeasure ρ] (F : Y → ℂ) (hF : Continuous F) : Integrable F ρ :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem dbl {D Y : Type} [TopologicalSpace D] [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] (ρ : Measure Y) [IsFiniteMeasure ρ] (A : D → Y → Y → ℂ)
    (hA : Continuous fun p : (D × Y) × Y => A p.1.1 p.1.2 p.2) :
    Continuous (fun d => ∫ v₁, ∫ v₂, A d v₁ v₂ ∂ρ ∂ρ) ∧ (∀ d v₁, Integrable (A d v₁) ρ) ∧
      ∀ d, Integrable (fun v₁ => ∫ v₂, A d v₁ v₂ ∂ρ) ρ := by
  have hB : Continuous fun p : D × Y => ∫ v₂, A p.1 p.2 v₂ ∂ρ :=
    cont_int ρ (F := fun (p : D × Y) v₂ => A p.1 p.2 v₂) hA
  exact ⟨cont_int ρ (F := fun d v₁ => ∫ v₂, A d v₁ v₂ ∂ρ) hB,
    fun d v₁ => int_cont ρ _ (hA.comp (Continuous.prodMk_right (d, v₁))),
    fun d => int_cont ρ _ (hB.comp (Continuous.prodMk_right d))⟩

private theorem cont_A {G S T : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [TopologicalSpace S]
    [TopologicalSpace T] (P : S × S × T → ℂ) (hP : Continuous P) (ι : S → G) (hι : Continuous ι) (φ₁ φ₂ : G → ℂ)
    (h₁ : Continuous φ₁) (h₂ : Continuous φ₂) :
    Continuous fun p : ((G × G × T) × S) × S =>
      P (p.1.2, p.2, p.1.1.2.2) * φ₁ (p.1.1.1 * (ι p.1.2)⁻¹) * φ₂ (p.1.1.2.1 * (ι p.2)⁻¹) := by
  have a1 : Continuous fun p : ((G × G × T) × S) × S => (p.1.2, p.2, p.1.1.2.2) := by fun_prop
  have a2 : Continuous fun p : ((G × G × T) × S) × S => p.1.1.1 * (ι p.1.2)⁻¹ := by fun_prop
  have a3 : Continuous fun p : ((G × G × T) × S) × S => p.1.1.2.1 * (ι p.2)⁻¹ := by fun_prop
  exact ((hP.comp a1).mul (h₁.comp a2)).mul (h₂.comp a3)

private theorem psi_cont {K : Type} [Field K] [NumberField K] (Ψ : G1 K (2 + 2) → ℂ)
    (hΨ : Continuous fun k : KG K (2 + 2) => Ψ k) :
    Continuous fun p : KG K 2 × KG K 2 × KG K (2 + 2) =>
      Ψ (lv (p.1 : G1 K 2) (p.2.1 : G1 K 2) 0 * (p.2.2 : G1 K (2 + 2))) := by
  obtain ⟨-, -, -, hlc, -, -, -, -, -, -, hlvK, -⟩ := blkLaws (K := K)
  have h00 : Continuous fun p : KG K 2 × KG K 2 × KG K (2 + 2) => ((p.1 : G1 K 2), (p.2.1 : G1 K 2), (0 : ℝ)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (((continuous_subtype_val.comp (continuous_fst.comp continuous_snd))).prodMk continuous_const)
  have h0 : Continuous fun p : KG K 2 × KG K 2 × KG K (2 + 2) =>
      lv (p.1 : G1 K 2) (p.2.1 : G1 K 2) 0 * (p.2.2 : G1 K (2 + 2)) :=
    (hlc.comp h00).mul (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
  exact hΨ.comp (h0.subtype_mk fun p => (KG K (2 + 2)).mul_mem (hlvK _ p.1.2 _ p.2.1.2) p.2.2.2)

private noncomputable def abelian₂ {K : Type} [Field K] [NumberField K] (ρ : Measure (KG K 2)) (Ψ : G1 K (2 + 2) → ℂ)
    (φ₁ φ₂ : G1 K 2 → ℂ) (m₁ m₂ : G1 K 2) (k : G1 K (2 + 2)) : ℂ :=
  ∫ v₁ : KG K 2, ∫ v₂ : KG K 2,
    Ψ (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * k) * φ₁ (m₁ * (v₁ : G1 K 2)⁻¹) * φ₂ (m₂ * (v₂ : G1 K 2)⁻¹) ∂ρ ∂ρ

private theorem lam_eq {K : Type} [Field K] [NumberField K] (ρ : Measure (KG K 2))
    (hρ : ∀ u : KG K 2, MeasurePreserving (· * u) ρ ρ) (Ψ : G1 K (2 + 2) → ℂ) (φ₁ φ₂ : G1 K 2 → ℂ) (m₁ m₂ u₁ u₂ : G1 K 2)
    (hu₁ : u₁ ∈ KG K 2) (hu₂ : u₂ ∈ KG K 2) (k : G1 K (2 + 2)) :
    abelian₂ ρ Ψ φ₁ φ₂ (m₁ * u₁) (m₂ * u₂) k = abelian₂ ρ Ψ φ₁ φ₂ m₁ m₂ (lv u₁ u₂ 0 * k) := by
  have hmul := (blkLaws (K := K)).2.1
  have hemb : ∀ u : KG K 2, MeasurableEmbedding (· * u) := fun u => (Homeomorph.mulRight u).measurableEmbedding
  unfold abelian₂
  refine ((hρ ⟨u₁, hu₁⟩).integral_comp (hemb _) _).symm.trans ?_
  refine integral_congr_ae (Eventually.of_forall fun v₁ => ?_)
  refine ((hρ ⟨u₂, hu₂⟩).integral_comp (hemb _) _).symm.trans ?_
  refine integral_congr_ae (Eventually.of_forall fun v₂ => ?_)
  have e1 : lv (((v₁ * ⟨u₁, hu₁⟩ : KG K 2)) : G1 K 2) (((v₂ * ⟨u₂, hu₂⟩ : KG K 2)) : G1 K 2) 0 =
      lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * lv u₁ u₂ 0 := by
    rw [hmul, add_zero]
    rfl
  have e2 : m₁ * u₁ * (((v₁ * ⟨u₁, hu₁⟩ : KG K 2)) : G1 K 2)⁻¹ = m₁ * (v₁ : G1 K 2)⁻¹ := by
    rw [Subgroup.coe_mul, _root_.mul_inv_rev]
    simp [mul_assoc]
  have e3 : m₂ * u₂ * (((v₂ * ⟨u₂, hu₂⟩ : KG K 2)) : G1 K 2)⁻¹ = m₂ * (v₂ : G1 K 2)⁻¹ := by
    rw [Subgroup.coe_mul, _root_.mul_inv_rev]
    simp [mul_assoc]
  show Ψ _ * φ₁ _ * φ₂ _ = Ψ _ * φ₁ _ * φ₂ _
  rw [e1, e2, e3, mul_assoc (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0)]

private theorem lam_un {K : Type} [Field K] [NumberField K] (ρ : Measure (KG K 2)) (Ψ : G1 K (2 + 2) → ℂ)
    (hN : ∀ X, nn X ∈ KG K (2 + 2) → ∀ k ∈ KG K (2 + 2), Ψ (nn X * k) = Ψ k) (φ₁ φ₂ : G1 K 2 → ℂ) (m₁ m₂ : G1 K 2)
    (X : UPos (2 + 2) 2 → 𝔸[K]) (hX : nn X ∈ KG K (2 + 2)) (k : G1 K (2 + 2)) (hk : k ∈ KG K (2 + 2)) :
    abelian₂ ρ Ψ φ₁ φ₂ m₁ m₂ (nn X * k) = abelian₂ ρ Ψ φ₁ φ₂ m₁ m₂ k := by
  have hlvK := (blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.1
  unfold abelian₂
  refine integral_congr_ae (Eventually.of_forall fun v₁ => ?_)
  refine integral_congr_ae (Eventually.of_forall fun v₂ => ?_)
  obtain ⟨e, he, -⟩ := adMeas (v₁ : G1 K 2) (v₂ : G1 K 2) 0
  have hl := hlvK _ v₁.2 _ v₂.2
  have e1 : nn (e.symm X) * lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 = lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * nn X := by
    rw [he, e.apply_symm_apply]
  have e2 : nn (e.symm X) ∈ KG K (2 + 2) := by
    rw [eq_mul_inv_of_mul_eq e1]
    exact (KG K (2 + 2)).mul_mem ((KG K (2 + 2)).mul_mem hl hX) ((KG K (2 + 2)).inv_mem hl)
  have e3 : lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * (nn X * k) = nn (e.symm X) * (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * k) := by
    rw [← mul_assoc, ← mul_assoc, e1]
  show Ψ _ * _ * _ = Ψ _ * _ * _
  rw [e3, hN _ e2 _ ((KG K (2 + 2)).mul_mem hl hk)]

private theorem lam_all {K : Type} [Field K] [NumberField K] (ρ : Measure (KG K 2)) [IsFiniteMeasure ρ]
    (Ψ : G1 K (2 + 2) → ℂ) (hΨ : Continuous fun k : KG K (2 + 2) => Ψ k) (φ₁ φ₂ : G1 K 2 → ℂ) (hc₁ : Continuous φ₁)
    (hc₂ : Continuous φ₂) :
    Continuous (fun p : G1 K 2 × G1 K 2 × KG K (2 + 2) => abelian₂ ρ Ψ φ₁ φ₂ p.1 p.2.1 p.2.2) ∧
      (∀ (d : G1 K 2 × G1 K 2 × KG K (2 + 2)) (v₁ : KG K 2), Integrable (fun v₂ : KG K 2 =>
        Ψ (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * (d.2.2 : G1 K (2 + 2))) * φ₁ (d.1 * (v₁ : G1 K 2)⁻¹) *
          φ₂ (d.2.1 * (v₂ : G1 K 2)⁻¹)) ρ) ∧
      ∀ d : G1 K 2 × G1 K 2 × KG K (2 + 2), Integrable (fun v₁ : KG K 2 => ∫ v₂ : KG K 2,
        Ψ (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * (d.2.2 : G1 K (2 + 2))) * φ₁ (d.1 * (v₁ : G1 K 2)⁻¹) *
          φ₂ (d.2.1 * (v₂ : G1 K 2)⁻¹) ∂ρ) ρ := by
  haveI : CompactSpace (KG K 2) := isCompact_iff_compactSpace.1 ((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 2).1
  exact dbl ρ (fun (d : G1 K 2 × G1 K 2 × KG K (2 + 2)) (v₁ v₂ : KG K 2) =>
      Ψ (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * (d.2.2 : G1 K (2 + 2))) * φ₁ (d.1 * (v₁ : G1 K 2)⁻¹) *
        φ₂ (d.2.1 * (v₂ : G1 K 2)⁻¹))
    (cont_A _ (psi_cont Ψ hΨ) (fun v : KG K 2 => (v : G1 K 2)) continuous_subtype_val φ₁ φ₂ hc₁ hc₂)

private theorem lam_bd {K : Type} [Field K] [NumberField K] (ρ : Measure (KG K 2)) [IsProbabilityMeasure ρ]
    (Ψ : G1 K (2 + 2) → ℂ) (hΨ : Continuous fun k : KG K (2 + 2) => Ψ k) (φ₁ φ₂ : G1 K 2 → ℂ)
    (hb₁ : ∃ B : ℝ, ∀ m, ‖φ₁ m‖ ≤ B) (hb₂ : ∃ B : ℝ, ∀ m, ‖φ₂ m‖ ≤ B) :
    ∃ C : ℝ, ∀ m₁ m₂, ∀ k ∈ KG K (2 + 2), ‖abelian₂ ρ Ψ φ₁ φ₂ m₁ m₂ k‖ ≤ C := by
  have hlvK := (blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.1
  haveI : CompactSpace (KG K (2 + 2)) :=
    isCompact_iff_compactSpace.1 ((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 (2 + 2)).1
  obtain ⟨B₁, hB₁⟩ := hb₁
  obtain ⟨B₂, hB₂⟩ := hb₂
  obtain ⟨C, hC'⟩ := (isCompact_range hΨ).isBounded.exists_norm_le
  have hC₀ : 0 ≤ C := (norm_nonneg _).trans (hC' _ ⟨1, rfl⟩)
  have hB₁₀ : 0 ≤ B₁ := (norm_nonneg _).trans (hB₁ 1)
  refine ⟨C * B₁ * B₂, fun m₁ m₂ k hk => ?_⟩
  have hv : ∀ v₁ v₂ : KG K 2, ‖Ψ (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * k) * φ₁ (m₁ * (v₁ : G1 K 2)⁻¹) *
      φ₂ (m₂ * (v₂ : G1 K 2)⁻¹)‖ ≤ C * B₁ * B₂ := by
    intro v₁ v₂
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul (hC' _ ⟨⟨_, (KG K (2 + 2)).mul_mem (hlvK _ v₁.2 _ v₂.2) hk⟩, rfl⟩) (hB₁ _) (norm_nonneg _) hC₀)
      (hB₂ _) (norm_nonneg _) (mul_nonneg hC₀ hB₁₀)
  have h1 : ∀ v₁ : KG K 2, ‖∫ v₂ : KG K 2, Ψ (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * k) * φ₁ (m₁ * (v₁ : G1 K 2)⁻¹) *
      φ₂ (m₂ * (v₂ : G1 K 2)⁻¹) ∂ρ‖ ≤ C * B₁ * B₂ := by
    intro v₁
    have := norm_integral_le_of_norm_le_const (μ := ρ) (Eventually.of_forall (hv v₁))
    simpa using this
  have := norm_integral_le_of_norm_le_const (μ := ρ) (Eventually.of_forall h1)
  simpa [abelian₂] using this

private theorem lam_mem₁ {K : Type} [Field K] [NumberField K] (ρ : Measure (KG K 2)) [IsFiniteMeasure ρ]
    (Ψ : G1 K (2 + 2) → ℂ) (hΨ : Continuous fun k : KG K (2 + 2) => Ψ k) (φ₁ φ₂ : G1 K 2 → ℂ) (hc₁ : Continuous φ₁)
    (hc₂ : Continuous φ₂) (hf₁ : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : KG K 2 => fun m => φ₁ (m * k))))
    (w : G1 K 2) (k : KG K (2 + 2)) :
    (fun m => abelian₂ ρ Ψ φ₁ φ₂ m w k) ∈ Submodule.span ℂ (Set.range fun k : KG K 2 => fun m => φ₁ (m * k)) := by
  obtain ⟨-, hI₂, hI₁⟩ := lam_all ρ Ψ hΨ φ₁ φ₂ hc₁ hc₂
  refine avg_mem _ ρ (fun v₁ m => ∫ v₂ : KG K 2, Ψ (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * (k : G1 K (2 + 2))) *
    φ₁ (m * (v₁ : G1 K 2)⁻¹) * φ₂ (w * (v₂ : G1 K 2)⁻¹) ∂ρ) (fun v₁ => ?_) fun m => hI₁ (m, w, k)
  refine avg_mem _ ρ (fun v₂ m => Ψ (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * (k : G1 K (2 + 2))) *
    φ₁ (m * (v₁ : G1 K 2)⁻¹) * φ₂ (w * (v₂ : G1 K 2)⁻¹)) (fun v₂ => ?_) fun m => hI₂ (m, w, k) v₁
  have : (fun m => Ψ (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * (k : G1 K (2 + 2))) *
      φ₁ (m * (v₁ : G1 K 2)⁻¹) * φ₂ (w * (v₂ : G1 K 2)⁻¹)) =
      (Ψ (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * (k : G1 K (2 + 2))) * φ₂ (w * (v₂ : G1 K 2)⁻¹)) •
        fun m => φ₁ (m * ((v₁⁻¹ : KG K 2) : G1 K 2)) := by
    funext m
    simp only [Pi.smul_apply, smul_eq_mul, Subgroup.coe_inv]
    ring
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v₁⁻¹, rfl⟩)

private theorem lam_mem₂ {K : Type} [Field K] [NumberField K] (ρ : Measure (KG K 2)) [IsFiniteMeasure ρ]
    (Ψ : G1 K (2 + 2) → ℂ) (hΨ : Continuous fun k : KG K (2 + 2) => Ψ k) (φ₁ φ₂ : G1 K 2 → ℂ) (hc₁ : Continuous φ₁)
    (hc₂ : Continuous φ₂) (hf₂ : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : KG K 2 => fun m => φ₂ (m * k))))
    (w : G1 K 2) (k : KG K (2 + 2)) :
    (fun m => abelian₂ ρ Ψ φ₁ φ₂ w m k) ∈ Submodule.span ℂ (Set.range fun k : KG K 2 => fun m => φ₂ (m * k)) := by
  obtain ⟨-, hI₂, hI₁⟩ := lam_all ρ Ψ hΨ φ₁ φ₂ hc₁ hc₂
  refine avg_mem _ ρ (fun v₁ m => ∫ v₂ : KG K 2, Ψ (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * (k : G1 K (2 + 2))) *
    φ₁ (w * (v₁ : G1 K 2)⁻¹) * φ₂ (m * (v₂ : G1 K 2)⁻¹) ∂ρ) (fun v₁ => ?_) fun m => hI₁ (w, m, k)
  refine avg_mem _ ρ (fun v₂ m => Ψ (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * (k : G1 K (2 + 2))) *
    φ₁ (w * (v₁ : G1 K 2)⁻¹) * φ₂ (m * (v₂ : G1 K 2)⁻¹)) (fun v₂ => ?_) fun m => hI₂ (w, m, k) v₁
  have : (fun m => Ψ (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * (k : G1 K (2 + 2))) *
      φ₁ (w * (v₁ : G1 K 2)⁻¹) * φ₂ (m * (v₂ : G1 K 2)⁻¹)) =
      (Ψ (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * (k : G1 K (2 + 2))) * φ₁ (w * (v₁ : G1 K 2)⁻¹)) •
        fun m => φ₂ (m * ((v₂⁻¹ : KG K 2) : G1 K 2)) := by
    funext m
    simp only [Pi.smul_apply, smul_eq_mul, Subgroup.coe_inv]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v₂⁻¹, rfl⟩)

private theorem sec_red {K : Type} [Field K] [NumberField K] (Λ : G1 K 2 → G1 K 2 → G1 K (2 + 2) → ℂ) (f : G1 K (2 + 2) → ℂ)
    (hfv : ∀ X m₁ m₂ t, ∀ k ∈ KG K (2 + 2), f (nn X * lv m₁ m₂ t * k) = Λ m₁ m₂ k) (g : G1 K (2 + 2)) :
    ∃ n₁ n₂, ∃ k : KG K (2 + 2), ∀ m₁ m₂, f (lv m₁ m₂ 0 * g) = Λ (m₁ * n₁) (m₂ * n₂) k := by
  have hmul := (blkLaws (K := K)).2.1
  obtain ⟨X, n₁, n₂, t, k, hk, rfl⟩ := iwa g
  refine ⟨n₁, n₂, ⟨k, hk⟩, fun m₁ m₂ => ?_⟩
  obtain ⟨e, he, -⟩ := adMeas m₁ m₂ 0
  have e1 : lv m₁ m₂ 0 * nn X = nn (e.symm X) * lv m₁ m₂ 0 := by rw [he, e.apply_symm_apply]
  have e2 : lv m₁ m₂ 0 * (nn X * lv n₁ n₂ t * k) = nn (e.symm X) * lv (m₁ * n₁) (m₂ * n₂) (0 + t) * k := by
    rw [← hmul, ← mul_assoc, ← mul_assoc, e1]
    simp only [mul_assoc]
  rw [e2, hfv _ _ _ _ _ hk]

private theorem sec_unip {K : Type} [Field K] [NumberField K] (Λ : G1 K 2 → G1 K 2 → G1 K (2 + 2) → ℂ) (f : G1 K (2 + 2) → ℂ)
    (hfv : ∀ X m₁ m₂ t, ∀ k ∈ KG K (2 + 2), f (nn X * lv m₁ m₂ t * k) = Λ m₁ m₂ k) (X : UPos (2 + 2) 2 → 𝔸[K])
    (g : G1 K (2 + 2)) : f (nn X * g) = f g := by
  obtain ⟨Y, m₁, m₂, t, k, hk, rfl⟩ := iwa g
  have e1 : nn X * (nn Y * lv m₁ m₂ t * k) = nn (X + Y) * lv m₁ m₂ t * k := by
    have hadd : nn (X + Y) = nn X * nn Y := unipOne_add 2 X Y
    rw [hadd]
    simp only [mul_assoc]
  rw [e1, hfv _ _ _ _ _ hk, hfv _ _ _ _ _ hk]

private theorem sec_ray {K : Type} [Field K] [NumberField K] (Λ : G1 K 2 → G1 K 2 → G1 K (2 + 2) → ℂ) (f : G1 K (2 + 2) → ℂ)
    (hfv : ∀ X m₁ m₂ t, ∀ k ∈ KG K (2 + 2), f (nn X * lv m₁ m₂ t * k) = Λ m₁ m₂ k) (t : ℝ)
    (g : G1 K (2 + 2)) : f (lv 1 1 t * g) = f g := by
  have hmul := (blkLaws (K := K)).2.1
  obtain ⟨Y, m₁, m₂, s, k, hk, rfl⟩ := iwa g
  obtain ⟨e, he, -⟩ := adMeas (1 : G1 K 2) 1 t
  have e1 : lv (1 : G1 K 2) 1 t * nn Y = nn (e.symm Y) * lv (1 : G1 K 2) 1 t := by rw [he, e.apply_symm_apply]
  have e2 : lv (1 : G1 K 2) 1 t * (nn Y * lv m₁ m₂ s * k) = nn (e.symm Y) * lv (1 * m₁) (1 * m₂) (t + s) * k := by
    rw [← hmul, ← mul_assoc, ← mul_assoc, e1]
    simp only [mul_assoc]
  rw [e2, hfv _ _ _ _ _ hk, hfv _ _ _ _ _ hk, one_mul, one_mul]

theorem UpperTheory.exists_cuspidal_section_from_levi_average :
    ∀ {K : Type} [Field K] [NumberField K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)), CuspIrr μ₂ τ₁ → CuspIrr μ₂ τ₂ → ∀ ρ : Measure (KG K 2), IsProbabilityMeasure ρ → (∀ u : KG K 2, MeasurePreserving (· * u) ρ ρ) → ∀ Ψ : G1 K (2 + 2) → ℂ, (Continuous fun k : KG K (2 + 2) => Ψ k) → (∀ X, nn X ∈ KG K (2 + 2) → ∀ k ∈ KG K (2 + 2), Ψ (nn X * k) = Ψ k) → ∀ φ₁ φ₂ : G1 K 2 → ℂ, Continuous φ₁ → Continuous φ₂ → (∃ B : ℝ, ∀ m, ‖φ₁ m‖ ≤ B) → (∃ B : ℝ, ∀ m, ‖φ₂ m‖ ≤ B) → (∃ v ∈ τ₁, Reps μ₂ v φ₁) → (∃ v ∈ τ₂, Reps μ₂ v φ₂) → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : KG K 2 => fun m => φ₁ (m * k))) → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : KG K 2 => fun m => φ₂ (m * k))) → ∃ f : G1 K (2 + 2) → ℂ, Continuous f ∧ (∃ C : ℝ, ∀ g, ‖f g‖ ≤ C) ∧ (∀ X g, f (nn X * g) = f g) ∧ (∀ t g, f (lv 1 1 t * g) = f g) ∧ Slices τ₁ τ₂ f ∧ ∀ X m₁ m₂ t, ∀ k ∈ KG K (2 + 2), f (nn X * lv m₁ m₂ t * k) = ∫ v₁ : KG K 2, ∫ v₂ : KG K 2, Ψ (lv (v₁ : G1 K 2) (v₂ : G1 K 2) 0 * k) * φ₁ (m₁ * (v₁ : G1 K 2)⁻¹) * φ₂ (m₂ * (v₂ : G1 K 2)⁻¹) ∂ρ ∂ρ := by
  intro K _ _ μ₂ _ τ₁ τ₂ h₁ h₂ ρ hp hρ Ψ hΨ hN φ₁ φ₂ hc₁ hc₂ hb₁ hb₂ hr₁ hr₂ hf₁ hf₂
  haveI := hp
  obtain ⟨f, hf, hfv⟩ := mkSec K (abelian₂ ρ Ψ φ₁ φ₂) (lam_all ρ Ψ hΨ φ₁ φ₂ hc₁ hc₂).1
    (fun m₁ m₂ u₁ hu₁ u₂ hu₂ k _ => lam_eq ρ hρ Ψ φ₁ φ₂ m₁ m₂ u₁ u₂ hu₁ hu₂ k)
    (fun m₁ m₂ X hX k hk => lam_un ρ Ψ hN φ₁ φ₂ m₁ m₂ X hX k hk)
  refine ⟨f, hf, ?_, sec_unip _ f hfv, sec_ray _ f hfv, fun g => ?_, hfv⟩
  · obtain ⟨C, hC⟩ := lam_bd ρ Ψ hΨ φ₁ φ₂ hb₁ hb₂
    refine ⟨C, fun g => ?_⟩
    obtain ⟨X, m₁, m₂, t, k, hk, rfl⟩ := iwa g
    rw [hfv _ _ _ _ _ hk]
    exact hC _ _ _ hk
  · obtain ⟨n₁, n₂, k, hk⟩ := sec_red _ f hfv g
    refine ⟨fun m₂ => ?_, fun m₁ => ?_⟩
    · obtain ⟨v, hv, hq⟩ := span_le_rep μ₂ τ₁ h₁ (KG K 2) hr₁ (lam_mem₁ ρ Ψ hΨ φ₁ φ₂ hc₁ hc₂ hf₁ (m₂ * n₂) k)
      refine ⟨_, h₁.inv n₁ v hv, ?_⟩
      have := reps_tr μ₂ hq n₁
      simpa only [hk] using this
    · obtain ⟨v, hv, hq⟩ := span_le_rep μ₂ τ₂ h₂ (KG K 2) hr₂ (lam_mem₂ ρ Ψ hΨ φ₁ φ₂ hc₁ hc₂ hf₂ (m₁ * n₁) k)
      refine ⟨_, h₂.inv n₂ v hv, ?_⟩
      have := reps_tr μ₂ hq n₂
      simpa only [hk] using this
