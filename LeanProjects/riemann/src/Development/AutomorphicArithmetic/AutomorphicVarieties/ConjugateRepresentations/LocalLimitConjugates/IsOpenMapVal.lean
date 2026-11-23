import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LocInt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericFiniteByInduction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieSkewAdjointL2
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

open scoped ContDiff

section General

variable {P Q α : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [TopologicalSpace α]

private def Loc (Q : Type) [NormedAddCommGroup Q] [NormedSpace ℝ Q] {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (H : P → α → V) (x : P) (y : α) : Prop :=
  ∃ (h : P × Q → V) (A : α → Q), ContinuousAt A y ∧ ContDiffAt ℝ ∞ h (x, A y) ∧
    ∀ᶠ p : P × α in 𝓝 (x, y), H p.1 p.2 = h (p.1, A p.2)

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {H : P → α → V} {x : P} {y : α}

private theorem Loc.cont (h : Loc Q H x y) : ContinuousAt (fun p : P × α => H p.1 p.2) (x, y) := by
  obtain ⟨h, A, hA, hh, e⟩ := h
  refine ContinuousAt.congr ?_ (EventuallyEq.symm e)
  exact ContinuousAt.comp (f := fun p : P × α => (p.1, A p.2)) hh.continuousAt
    (continuousAt_fst.prodMk (ContinuousAt.comp (f := Prod.snd) hA continuousAt_snd))

private theorem Loc.diff (h : Loc Q H x y) : DifferentiableAt ℝ (fun x => H x y) x := by
  obtain ⟨h, A, -, hh, e⟩ := h
  have e' : (fun x => H x y) =ᶠ[𝓝 x] fun x => h (x, A y) :=
    (Continuous.prodMk_left y).continuousAt.eventually e
  exact DifferentiableAt.congr_of_eventuallyEq
    ((hh.differentiableAt (by simp)).comp x (differentiableAt_id.prodMk (differentiableAt_const _))) e'

private theorem Loc.fderiv (h : Loc Q H x y) : Loc Q (fun x y => fderiv ℝ (fun x => H x y) x) x y := by
  obtain ⟨h, A, hA, hh, e⟩ := h
  refine ⟨fun q => (_root_.fderiv ℝ h q).comp (ContinuousLinearMap.inl ℝ P Q), A, hA,
    (hh.fderiv_right (by simp)).clm_comp contDiffAt_const, ?_⟩
  have hc : ContinuousAt (fun p : P × α => (p.1, A p.2)) (x, y) :=
    continuousAt_fst.prodMk (ContinuousAt.comp (f := Prod.snd) hA continuousAt_snd)
  have hd : ∀ᶠ q in 𝓝 (x, A y), ContDiffAt ℝ 1 h q := (hh.of_le (by simp)).eventually (by simp)
  filter_upwards [e.eventually_nhds, hc.eventually hd] with p hp hq
  have e' : (fun x => H x p.2) =ᶠ[𝓝 p.1] fun x => h (x, A p.2) :=
    (Continuous.prodMk_left p.2).continuousAt.eventually hp
  rw [e'.fderiv_eq]
  exact ((hq.differentiableAt (by simp)).hasFDerivAt.comp p.1 (hasFDerivAt_prodMk_left p.1 (A p.2))).fderiv

variable [FiniteDimensional ℝ P] [T2Space α] [SecondCountableTopology α] [MeasurableSpace α] [OpensMeasurableSpace α]
  {μ : Measure α} {f : α → ℂ} {S : Set P}

omit [FiniteDimensional ℝ P] [T2Space α] [SecondCountableTopology α] [MeasurableSpace α] [OpensMeasurableSpace α] in
private theorem supp_fderiv (hs : ∃ C : Set α, IsCompact C ∧ ∀ᶠ x' in 𝓝 x, ∀ y ∉ C, H x' y = 0) :
    ∃ C : Set α, IsCompact C ∧ ∀ᶠ x' in 𝓝 x, ∀ y ∉ C, fderiv ℝ (fun x => H x y) x' = 0 := by
  obtain ⟨C, hC, h⟩ := hs
  refine ⟨C, hC, h.eventually_nhds.mono fun x' hx' y hy => ?_⟩
  have e : (fun x => H x y) =ᶠ[𝓝 x'] fun _ => 0 := hx'.mono fun z hz => hz y hy
  rw [e.fderiv_eq, fderiv_fun_const]
  rfl

private theorem dom [NormedSpace ℂ V] (hf : LocallyIntegrable f μ) (hS : IsOpen S) (hx : x ∈ S)
    (hH : ∀ x ∈ S, ∀ y, Loc Q H x y) (hs : ∃ C : Set α, IsCompact C ∧ ∀ᶠ x' in 𝓝 x, ∀ y ∉ C, H x' y = 0) :
    ∃ b : α → ℝ, Integrable b μ ∧ ∀ᶠ x' in 𝓝 x, AEStronglyMeasurable (fun y => f y • H x' y) μ ∧
      ∀ y, ‖f y • H x' y‖ ≤ b y := by
  obtain ⟨C, hC, h⟩ := hs
  obtain ⟨K, hK, hKS, hKc⟩ := local_compact_nhds (hS.mem_nhds hx)
  obtain ⟨M, hM⟩ := (hKc.prod hC).exists_bound_of_continuousOn (f := fun p : P × α => H p.1 p.2)
    fun p hp => (hH p.1 (hKS hp.1) p.2).cont.continuousWithinAt
  refine ⟨C.indicator fun y => ‖f y‖ * M,
    (integrable_indicator_iff hC.measurableSet).2 ((hf.integrableOn_isCompact hC).norm.mul_const M), ?_⟩
  filter_upwards [h, hK] with x' h1 h2
  refine ⟨hf.aestronglyMeasurable.smul (Continuous.aestronglyMeasurable (continuous_iff_continuousAt.2 fun y => ?_)),
    fun y => ?_⟩
  · exact ContinuousAt.comp (f := fun y => (x', y)) (hH x' (hKS h2) y).cont (Continuous.prodMk_right x').continuousAt
  · by_cases hy : y ∈ C
    · rw [Set.indicator_of_mem hy, norm_smul]
      exact mul_le_mul_of_nonneg_left (hM (x', y) ⟨h2, hy⟩) (norm_nonneg _)
    · rw [Set.indicator_of_notMem hy, h1 y hy, smul_zero, norm_zero]

private theorem hasFD [NormedSpace ℂ V] [SMulCommClass ℝ ℂ V] (hf : LocallyIntegrable f μ) (hS : IsOpen S) (hx : x ∈ S)
    (hH : ∀ x ∈ S, ∀ y, Loc Q H x y) (hs : ∃ C : Set α, IsCompact C ∧ ∀ᶠ x' in 𝓝 x, ∀ y ∉ C, H x' y = 0) :
    HasFDerivAt (fun x => ∫ y, f y • H x y ∂μ) (∫ y, f y • fderiv ℝ (fun x => H x y) x ∂μ) x := by
  obtain ⟨b, hb, h⟩ := dom hf hS hx hH hs
  obtain ⟨b', hb', h'⟩ := dom hf hS hx (fun x hx y => (hH x hx y).fderiv) (supp_fderiv hs)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := b')
    (F' := fun x y => f y • fderiv ℝ (fun x => H x y) x) (h'.and (hS.eventually_mem hx)) (h.mono fun _ h => h.1)
    (hb.mono' h.self_of_nhds.1 (.of_forall h.self_of_nhds.2)) h'.self_of_nhds.1
    (.of_forall fun y x' hx' => hx'.1.2 y) hb' (.of_forall fun y x' hx' => ?_)
  exact (hH x' hx'.2 y).diff.hasFDerivAt.const_smul (f y)

private theorem smooth_nat (hf : LocallyIntegrable f μ) (hS : IsOpen S) (n : ℕ) :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V] [SMulCommClass ℝ ℂ V] (H : P → α → V),
      (∀ x ∈ S, ∀ y, Loc Q H x y) → (∀ x ∈ S, ∃ C : Set α, IsCompact C ∧ ∀ᶠ x' in 𝓝 x, ∀ y ∉ C, H x' y = 0) →
      ContDiffOn ℝ n (fun x => ∫ y, f y • H x y ∂μ) S := by
  induction n with
  | zero =>
    intro V _ _ _ _ H hH hs
    exact contDiffOn_zero.2 fun x hx => (hasFD hf hS hx hH (hs x hx)).continuousAt.continuousWithinAt
  | succ n ih =>
    intro V _ _ _ _ H hH hs
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hS]
    refine ⟨fun x hx => (hasFD hf hS hx hH (hs x hx)).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact (ih _ _ (fun x hx y => (hH x hx y).fderiv) fun x hx => supp_fderiv (hs x hx)).congr
      fun x hx => (hasFD hf hS hx hH (hs x hx)).fderiv

end General

section Adelic

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [IsTotallyComplex E] in
private theorem contDiff_mulL :
    ContDiff ℝ ∞ fun q : Lie E a × Lie E a => toL (Matrix.of q.2 * Matrix.of q.1) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  change ContDiff ℝ ∞ fun q : Lie E a × Lie E a => ∑ k, q.2 i k * q.1 k j
  refine ContDiff.sum fun k _ => ContDiff.mul ?_ ?_
  · exact contDiff_pi.1 (contDiff_pi.1 contDiff_snd i) k
  · exact contDiff_pi.1 (contDiff_pi.1 contDiff_fst k) j

private theorem loc_chart {ψ : Sm E a} (hψ : HasLev ψ) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) (y : GA E a) :
    Loc (Lie E a) (fun x y => chart ψ.1 (y⁻¹ * g) x) x y := by
  have hc : Continuous fun w : GA E a => (y⁻¹ * g)⁻¹ * (w⁻¹ * g) :=
    continuous_const.mul (continuous_inv.mul continuous_const)
  have hA : Continuous fun w : GA E a => (GeneralLinearGroup.map (pInf E) ((y⁻¹ * g)⁻¹ * (w⁻¹ * g))).val :=
    Units.continuous_val.comp (GlobalTheory.CompanionTheory.AffglAssembly.continuous_mapInf.comp hc)
  refine ⟨fun q => chart ψ.1 (y⁻¹ * g) (toL (Matrix.of q.2 * Matrix.of q.1)),
    fun w => toL (GeneralLinearGroup.map (pInf E) ((y⁻¹ * g)⁻¹ * (w⁻¹ * g))).val, hA.continuousAt, ?_, ?_⟩
  · refine ContDiffAt.comp _ (contDiffAt_chart ψ.2 _ ?_) contDiff_mulL.contDiffAt
    exact IsUnit.mul (Units.isUnit _) hx
  · have h1 : ∀ᶠ w in 𝓝 y, act (.fin (GeneralLinearGroup.map (pFin E) ((y⁻¹ * g)⁻¹ * (w⁻¹ * g)))) ψ = ψ :=
      (GlobalTheory.CompanionTheory.AffglAssembly.continuous_mapFin.comp hc).continuousAt.eventually_mem (hψ.mem_nhds (by
        change finRep E a _ ψ = ψ
        simp))
    rw [nhds_prod_eq]
    filter_upwards [prod_mem_prod (isOpen_invSet.mem_nhds hx) h1]
    rintro ⟨x', w⟩ ⟨⟨u, hu⟩, hw⟩
    obtain rfl : x' = toL u.val := hu.symm
    set t := (y⁻¹ * g)⁻¹ * (w⁻¹ * g) with ht
    have e1 := congrFun (congrArg Subtype.val hw) (y⁻¹ * g * infGL E a (GeneralLinearGroup.map (pInf E) t * u))
    change ψ.1 (_ * finGL E a _) = _ at e1
    change chart ψ.1 (w⁻¹ * g) (toL u.val) = chart ψ.1 (y⁻¹ * g) (toL (GeneralLinearGroup.map (pInf E) t * u).val)
    rw [chart_val, chart_val, ← e1, map_mul, mul_assoc (y⁻¹ * g), mul_assoc (infGL E a _), infGL_comm u,
      ← mul_assoc (infGL E a _), infGL_mul_finGL, ← mul_assoc (y⁻¹ * g), ht, mul_inv_cancel_left]

open scoped Matrix.Norms.Operator in
omit [IsTotallyComplex E] in
private theorem isOpenMap_val : IsOpenMap fun u : GL (Fin a) (Cinf E) => toL u.val :=
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  (Units.isOpenEmbedding_val (R := Matrix (Fin a) (Fin a) (Cinf E))).isOpenMap

open scoped Matrix.Norms.Operator in
omit [IsTotallyComplex E] in
private theorem locCpt : LocallyCompactSpace (GL (Fin a) (Cinf E)) :=
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  haveI : ProperSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.proper ℝ _
  (Units.isOpenEmbedding_val (R := Matrix (Fin a) (Fin a) (Cinf E))).locallyCompactSpace

private theorem supp_chart {ψ : GA E a → ℂ} (hψ : HasCompactSupport ψ) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    ∃ C : Set (GA E a), IsCompact C ∧ ∀ᶠ x' in 𝓝 x, ∀ y ∉ C, chart ψ (y⁻¹ * g) x' = 0 := by
  obtain ⟨u, hu⟩ := hx
  obtain rfl : x = toL u.val := hu.symm
  haveI := locCpt (E := E) (a := a)
  obtain ⟨K, hKc, hK⟩ := exists_compact_mem_nhds u
  have hc : Continuous fun p : GL (Fin a) (Cinf E) × GA E a => g * infGL E a p.1 * p.2⁻¹ :=
    (continuous_const.mul ((GlobalTheory.CompanionTheory.LieSkew.continuous_infGL_map E a).comp continuous_fst)).mul continuous_snd.inv
  refine ⟨_, (hKc.prod hψ.isCompact).image hc, ?_⟩
  filter_upwards [isOpenMap_val.image_mem_nhds hK]
  rintro _ ⟨v, hv, rfl⟩ y hy
  rw [chart_val]
  by_contra h
  exact hy ⟨(v, y⁻¹ * g * infGL E a v), ⟨hv, subset_tsupport _ h⟩, by simp only; group⟩

end Adelic

theorem UpperTheory.V.Cj.H.cvSm :
    UpperTheory.V.Cj.H.CvSm := by
  intro E _ _ _ a μ _ _ ψ hψ F g
  have hf := (UpperTheory.V.Cj.H.locInt (GA E a) (latticeGL E a) μ).1 F
  have h : ContDiffOn ℝ ∞ (fun x => ∫ y, GlobalTheory.AutomorphicL2Unitary.lift _ F y • chart ψ.1 (y⁻¹ * g) x ∂μ) (invSet E a) :=
    contDiffOn_infty.2 fun n => smooth_nat hf isOpen_invSet n ℂ _ (fun _ hx y => loc_chart hψ.2 g hx y)
      fun _ hx => supp_chart hψ.1 g hx
  refine h.congr ?_
  rintro x ⟨u, hu⟩
  obtain rfl : x = toL u.val := hu.symm
  simp only [chart_val, cv, mul_assoc, smul_eq_mul]
