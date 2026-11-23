import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArFunRestrictInl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralLeadingMinorFlagDensityPosDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleSmoothRelativeDimensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullDimSmoothSurjectiveTotalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProjectionSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMatrixIsFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottChernMatrixIsFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMatLinearCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticVarietyPartitionDensityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalisationGenericSmoothCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChartLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChartMetricCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMatrixPullbackChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobianDensityHermitianMetricsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VandermondeWeightedRootProductSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VandermondeBoundaryTermSumIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobiDensityWeightedThetaIntegralZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagHeightPairingPullbackDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDensityPushforwardIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentFlagsHeightComparisonStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

namespace GlobalTheory.FlagCmp

section Total

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D E : ℕ}

theorem total_sum (hX : IsArithVar p E) (hR : Nonempty (AnRead p σ D)) {I : Type} [Fintype I] (a : I → ℝ)
    {τ : I → AlgChart p σ D → CxPts p σ → ℝ} (h : ∀ j, IsDens (τ j)) :
    total (fun c y => ∑ j, a j * τ j c y) = ∑ j, a j * total (τ j) := by
  have := hX.compactSpace σ
  have := CxPts.secondCountableTopology_of_isProjOver σ hX.isProjOver
  have := CxPts.t2Space_cxPts_of_isProjOver σ hX.isProjOver
  obtain ⟨ν, w, _, -, -, -, h₁, h₂⟩ := T.arithmetic_variety_partition_density k X p σ D hR
  choose g hg e using fun j => h₁ _ (h j)
  have i (j) := (hg j).integrable_of_hasCompactSupport (μ := ν) (HasCompactSupport.of_compactSpace _)
  rw [(h₂ _ (fun y => ∑ j, a j * g j y) (continuous_finsetSum _ fun j _ => continuous_const.mul (hg j))
    fun c y hy => by simp only [Finset.sum_mul, e _ c y hy, mul_assoc]).2,
    integral_finsetSum _ fun j _ => (i j).const_mul _]
  exact Finset.sum_congr rfl fun j _ => by rw [integral_const_mul, (h₂ _ _ (hg j) (e j)).2]

theorem isDens_flagDens {F : X.Modules} {r : ℕ} {h : VMetric p F r} (H : h.IsCInf) (fl : Vert.Flag F r) (N : HermLB p)
    (d : ℕ) (σ : k →+* ℂ) : IsDens (flagDens h fl N d σ) :=
  (T.chern_matrix_is_form k X p σ (d + 1) _ _ (N.cInf σ)).isDens_mix (IsForm.sum Finset.univ fun i =>
    T.bott_chern_matrix_is_form k X p σ (d + 1) _ _ _ _ _ _ _ (H.restrict (fl.isSubbundle i.succ) (fl.isVB i.succ) σ))

end Total

section Chain

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {d : ℕ} {E : X.Modules} {r : ℕ}
  {h : VMetric p E r} {H : h.IsCInf} {f₁ f₂ f₃ : Vert.Flag E r}

theorem rename_inl_lin {κ κ' : Type} [Fintype κ] [Fintype κ'] (n : κ → ℤ) :
    MvPolynomial.rename (Sum.inl : κ → κ ⊕ κ') (lin fun j => (n j : ℝ)) =
      lin fun j => ((Sum.elim n (fun _ => 0) j : ℤ) : ℝ) := by
  simp [lin, Fintype.sum_sum_type]

omit [IsIntegral X] in

theorem isometric_comb_inl {κ κ' : Type} [Fintype κ] [Fintype κ'] (L : κ → HermLB p) (M : κ' → HermLB p) (n : κ → ℤ) :
    (comb (Sum.elim L M) (Sum.elim n fun _ => 0)).Isometric (comb L n) :=
  HermLB.icls_eq_iff.1 (by simp [icls_comb, Fintype.sum_sum_type])

theorem compare_trans (hC : Published.ArCalc) (hX : IsArithVar p (d + 1)) (h₁ : Compare H d f₁ f₂)
    (h₂ : Compare H d f₂ f₃) : Compare H d f₁ f₃ := by
  intro κ _ L Φ hΦ x x' hx hx' n
  obtain ⟨Ψ, hΨ⟩ := ((hC.arExists k X p _ hX).2 (κ ⊕ Fin r) (Sum.elim L fun i => VMetric.grLB f₂ i H)).1
  have e₁ := h₁ _ _ Ψ hΨ (fun i => .inl (x i)) .inr hx (fun _ => .refl _) (Sum.elim n fun _ => 0)
  have e₂ := h₂ _ _ Ψ hΨ .inr (fun i => .inl (x' i)) (fun _ => .refl _) hx' (Sum.elim n fun _ => 0)
  simp only [bcPair_congr _ _ (isometric_comb_inl L _ n)] at e₁ e₂
  rw [← isArFun_restrict_inl hC.arIso hX L _ hΦ hΨ, ← sub_add_sub_cancel _ (bcPair h f₂ (comb L n) d), ← e₁, ← e₂,
    ← map_add, map_mul, map_pow, rename_inl_lin]
  congr 1
  simp only [map_sub, map_sum, map_pow, MvPolynomial.rename_X]
  ring

theorem compare (hC : Published.ArCalc) (hP : Published.Principalisation) (hX : IsArithVar p (d + 1)) (H : h.IsCInf)
    (f₁ f₂ : Vert.Flag E r) : Compare H d f₁ f₂ := by
  obtain ⟨Y, ρ, _, hρ, hJ⟩ := FlagChain.exists_cov_joined hX f₁ f₂
  obtain ⟨Z, τ, _, hτ, hs⟩ := T.principalisation_generic_smooth_cover hP k Y (ρ ≫ p) _ hρ.1
  have hc := hρ.comp hτ
  have hJ' := (hJ.pull τ).pull_comp
  rw [← Category.assoc] at hs
  generalize τ ≫ ρ = u at hc hJ' hs
  have key : ∀ g, FlagChain.Joined (f₁.pull u) g → Compare (H.pull u rfl) d (f₁.pull u) g := fun g hg => by
    induction hg with
    | refl => exact T.adjacent_flags_height_comparison hC k Z _ d hc.1 hs _ r _ _ _ _ (Vert.Flag.adjacent_refl _)
    | tail _ ha ih => exact compare_trans hC hc.1 ih (T.adjacent_flags_height_comparison hC k Z _ d hc.1 hs _ r _ _ _ _ ha)
  intro κ _ L Φ hΦ x x' hx hx' n
  have e := key _ hJ' κ _ _ ((hC.arProj k X Z p _ _ hX hc.1 u rfl hc.2.1 hc.2.2).2 κ L Φ hΦ) x x'
    (fun i => ((hx i).pull u rfl).trans (VMetric.isometric_grLB_pull k X Z p _ E r h H f₁ u rfl i).symm)
    (fun i => ((hx' i).pull u rfl).trans (VMetric.isometric_grLB_pull k X Z p _ E r h H f₂ u rfl i).symm) n
  simp only [bcPair_congr _ _ (isometric_comb_pull L n u rfl), T.flag_height_pairing_pullback_degree k X Z p d u hX hc E r h H] at e
  rw [LinearMap.smul_apply, smul_eq_mul, ← mul_sub] at e
  exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hc.2.2) e

end Chain

theorem exists_sum_pow {κ : Type} [Fintype κ] {d : ℕ} {P : MvPolynomial κ ℝ} (hP : P.IsHomogeneous d) :
    ∃ (I : Type) (_ : Fintype I) (c : I → ℝ) (n : I → κ → ℤ), ∑ j, c j • lin (fun x => (n j x : ℝ)) ^ d = P := by
  have : P ∈ Submodule.span ℝ (Set.range fun n : κ → ℤ => lin (fun x => (n x : ℝ)) ^ d) := by
    by_contra hn
    obtain ⟨f, hf, hf'⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
    have h0 := GlobalTheory.ArInt.Model.eq_zero_of_pow d (f ∘ₗ MvPolynomial.homogeneousComponent d) (fun n => by
      have hh : (lin (fun x => (n x : ℝ)) ^ d).IsHomogeneous d := by simpa using (isHomogeneous_lin _).pow d
      rw [LinearMap.comp_apply, MvPolynomial.homogeneousComponent_eq_self hh]
      exact (Submodule.mem_bot ℝ).1 (hf' ▸ Submodule.mem_map_of_mem (Submodule.subset_span ⟨n, rfl⟩)))
      fun Q e he hQ => by
        rw [LinearMap.comp_apply, MvPolynomial.homogeneousComponent_of_mem hQ, if_neg (Ne.symm he), map_zero]
    have := LinearMap.congr_fun h0 P
    rw [LinearMap.comp_apply, MvPolynomial.homogeneousComponent_eq_self hP] at this
    exact hf this
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 this
  exact ⟨c.support, inferInstance, fun j => c j, fun j => j, (Finset.sum_coe_sort c.support
    fun n => c n • lin (fun x => (n x : ℝ)) ^ d).trans hc⟩

theorem card_low (m : ℕ) : Fintype.card (Low m) = ∑ i : Fin m, (Finset.Ioi i).card ∧
    Fintype.card (Low m) = m * (m - 1) / 2 := by
  have h₁ : Fintype.card (Low m) = ∑ i : Fin m, (Finset.Ioi i).card := by
    rw [← Finset.card_sigma, ← Finset.card_univ]
    refine Finset.card_bij' (fun s _ => ⟨s.1.2, s.1.1⟩) (fun t ht => ⟨(t.2, t.1), by simpa using ht⟩) ?_ ?_ ?_ ?_ <;>
      simp
  refine ⟨h₁, h₁.trans ?_⟩
  simp only [Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range (fun i => m - 1 - i), Finset.sum_range_reflect (fun i => i), Finset.sum_range_id]

theorem isHomogeneous_vdm {ι : Type} [Fintype ι] (r : ι → ℕ) :
    (vdm r).IsHomogeneous (Fintype.card (Σ a, Low (r a))) := by
  rw [Fintype.card_sigma]
  refine MvPolynomial.IsHomogeneous.prod _ _ _ fun a _ => ?_
  rw [(card_low _).1]
  refine MvPolynomial.IsHomogeneous.prod _ _ _ fun i _ => ?_
  rw [Finset.card_eq_sum_ones]
  exact MvPolynomial.IsHomogeneous.prod _ _ _ fun i' _ =>
    (MvPolynomial.isHomogeneous_X _ _).sub (MvPolynomial.isHomogeneous_X _ _)

theorem mix_chg_diagonal {d : ℕ} {α : Type} [Fintype α] [DecidableEq α] (e : Fin (d + 1) ≃ α) (J : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (a m : α → ℝ) : mix d (chg J (diagonal fun j => (a (e j) : ℂ))) (chg J (diagonal fun j => (m (e j) : ℂ))) =
      ‖J.det‖ ^ 2 / Real.pi ^ (d + 1) * (d.factorial * ∑ s, m s * ∏ s' ∈ Finset.univ.erase s, a s') := by
  rw [mix_chg, mix_diagonal (fun j => a (e j)) fun j => m (e j), ← e.sum_comp]
  have (j : Fin (d + 1)) : ∏ l ∈ Finset.univ.erase j, a (e l) = ∏ s' ∈ Finset.univ.erase (e j), a s' :=
    Finset.prod_equiv e (by simp) fun _ _ => rfl
  simp only [this]
  ring

theorem integral_jacDens {m : ℕ} {G : Matrix (Fin m) (Fin m) ℂ} (hG : G.PosDef) :
    ∫ n, jacDens G n = Real.pi ^ Fintype.card (Low m) / ∏ l ∈ Finset.range m, (l.factorial : ℝ) := by
  have h₁ := GlobalTheory.FlagFibre.FlagInt.lintegral_dens m Gᵀ hG.transpose
  have hd := det_re_pos hG
  have hc : GlobalTheory.TrueCx.flagConst m = (∏ l ∈ Finset.range m, (l.factorial : ℝ)) / Real.pi ^ Fintype.card (Low m) := by
    rw [(card_low m).2, ← Finset.sum_range_id, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_div_distrib]
    rfl
  have hp : 0 < ∏ l ∈ Finset.range m, (l.factorial : ℝ) := Finset.prod_pos fun _ _ => by positivity
  simp only [jacDens]
  rw [integral_mul_const, integral_eq_lintegral_of_nonneg_ae (.of_forall (FlagFibre.dens_nonneg _))
    (FlagFibre.measurable_dens _).aestronglyMeasurable, h₁, det_transpose, hc,
    ENNReal.toReal_ofReal (by positivity)]
  have e : G.det.re ^ (1 - (m : ℤ)) * G.det.re ^ (m - 1) = 1 := by
    cases m with
    | zero => simp
    | succ m =>
      rw [Nat.add_sub_cancel, ← zpow_natCast, ← zpow_add₀ hd.ne']
      simp
  rw [div_mul_eq_mul_div, e]
  simp

section Fibre

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} [IsIntegral Y] {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {π : Y ⟶ B}
  {w : π ≫ q = p} {ι : Type} [Fintype ι] {E : ι → B.Modules} {r : ι → ℕ} {h : ∀ a, VMetric q (E a) (r a)}
  (H : ∀ a, (h a).IsCInf) {fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)} {d : ℕ}
  (e : Fin (d + 1) ≃ Option (Σ a, Low (r a))) {σ : k →+* ℂ}

omit [IsIntegral Y] in

theorem cell_forms {c : AlgChart q σ 1} {cE : ∀ a, Chart (E a) (r a)} {c' : AlgChart p σ (d + 1)}
    (hE : ∀ a, c.e.source ⊆ ptsIn q σ (cE a).U) (hc : IsCell e π w c c')
    (hf : ∀ a, IsCellFrame e π w c' a (h a) (fl a) (cE a)) {z : V 1} (hz : z ∈ c.e.target) :
    ∃ G K : ∀ a, Matrix (Fin (r a)) (Fin (r a)) ℂ, (∀ a, (G a).PosDef) ∧ (∀ a, (K a).IsHermitian) ∧
      ∀ u : ∀ a, Low (r a) → ℂ, c'.e.symm (pt e z u) ∈ c'.e.source ∧
        PtsOver.map π w (spMap σ) (c'.e.symm (pt e z u)) = c.e.symm z ∧
        ∃ J : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ, ‖J.det‖ ^ 2 = ∏ a, jacDens (G a) (u a) ∧
          (∀ n : (Σ a, Fin (r a)) → ℤ,
            chernMat ((comb (fun x : Σ a, Fin (r a) => VMetric.grLB (fl x.1) x.2 ((H x.1).pull π w)) n).φ σ) c'
              (c'.e.symm (pt e z u)) = chg J (diagonal fun j =>
                ((∑ x, (n x : ℝ) * rootDiag (fun x => theta (G x.1) (K x.1) (u x.1) x.2) x (e j) : ℝ) : ℂ))) ∧
          (∀ a, flagMat ((h a).pull π w) (fl a) σ c' (c'.e.symm (pt e z u)) =
            chg J (diagonal fun j => (bcDiag a (e j) : ℂ))) ∧
          chg J (diagonal fun j => (baseDiag (e j) : ℂ)) = diagonal fun j => (baseDiag (e j) : ℂ) := by
  have hy := c.e.map_target hz
  have hpos (a) : ∀ᶠ u in 𝓝 z, (((h a).met σ).G (cE a) (c.e.symm u)).PosDef :=
    Filter.eventually_of_mem (c.e.open_target.mem_nhds hz) fun u hu =>
      ((h a).met σ).posDef _ _ (hE a (c.e.map_target hu))
  obtain ⟨K, hK, hJ⟩ := T.jacobian_density_hermitian_metrics ι r d e (fun a u => ((h a).met σ).G (cE a) (c.e.symm u)) z (fun a => by
    have := (H a σ (cE a) _ (hE a hy)).mContDiffAt c hy
    rwa [c.e.right_inv hz] at this) hpos
  refine ⟨_, K, fun a => (hpos a).self_of_nhds, hK, fun u => ?_⟩
  have ht : pt e z u ∈ c'.e.target := by
    rw [hc.2.1]
    simpa only [Set.mem_setOf_eq, base_pt] using hz
  have hs := c'.e.map_target ht
  obtain ⟨J, h₁, h₂, h₃, h₄⟩ := hJ u
  obtain ⟨b₁, b₂⟩ := T.flag_bundle_chart_metric_compat k B Y q p π w ι r d e σ E h H fl c cE c' hc hf _ hs
  rw [c'.e.right_inv ht] at b₁ b₂
  refine ⟨hs, ?_, J, h₁, fun n => ?_, fun a => (b₂ a).trans (h₃ a), h₄⟩
  · have := hc.2.2 _ hs
    rw [c'.e.right_inv ht, base_pt] at this
    exact (c.e.left_inv (hc.1.le hs).1).symm.trans (congrArg c.e.symm this.symm)
  · rw [T.chernMat_linear_combination k Y p σ (d + 1) _ _ n c' _ hs]
    simp only [b₁, h₂, ← chg_smul]
    rw [chg, ← Finset.sum_congr rfl fun _ _ => rfl]
    simp only [chg, ← Matrix.sum_mul, ← Matrix.mul_sum]
    congr 2
    ext i j
    by_cases hij : i = j <;> simp [Matrix.sum_apply, diagonal_apply, hij]

variable (hq : IsRegSurf q) (hp : IsArithVar p (d + 1)) (hs : GenSmooth p (d + 1)) (hfl : IsFlagBundle π E r fl)
  (hd : d = Fintype.card (Σ a, Low (r a))) {I : Type} [Fintype I] {c : I → ℝ} {n : I → (Σ a, Fin (r a)) → ℤ}
  (hV : ∑ j, c j • lin (fun x => (n j x : ℝ)) ^ d = vdm r)
include e hq hp hs hfl hd hV

theorem sum_bcPair_taut (a : ι) : ∑ j, c j * bcPair ((h a).pull π w) (fl a)
    (comb (fun x : Σ a, Fin (r a) => VMetric.grLB (fl x.1) x.2 ((H x.1).pull π w)) (n j)) d = 0 := by
  subst hd
  have := hp.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  simp only [bcPair, finsum_eq_sum_of_fintype, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun σ _ => ?_
  have hR := (RegGenSmooth.genSmooth_of_isRegSurf k B q hq).1 σ
  have hD (j) := isDens_flagDens ((H a).pull π w) (fl a)
    (comb (fun x : Σ a, Fin (r a) => VMetric.grLB (fl x.1) x.2 ((H x.1).pull π w)) (n j))
      (Fintype.card (Σ a, Low (r a))) σ
  rw [← total_sum hp (hs σ) c hD, ← total_zero (p := q) (σ := σ) (D := 1)]
  refine T.arithmetic_density_pushforward_integral k B Y q p π w ι r _ e σ hq.toIsArithVar hp hR (hs σ) _ _
    (IsDens.sum _ fun j => (hD j).mul continuous_const) isDens_zero fun y => ?_
  obtain ⟨R⟩ := hR
  obtain ⟨i, hi⟩ := R.cover y
  obtain ⟨c₁, cE, c', hy, hE, hc, hf⟩ := T.flag_bundle_chart_lift k B Y q p π w ι r _ e σ E h fl hfl _ y hi
  refine ⟨c₁, c', hy, hc, fun z hz => ?_⟩
  obtain ⟨G, K, hG, hK, hu⟩ := cell_forms H e hE hc hf hz
  obtain ⟨κ, hκ⟩ := T.vandermonde_boundary_term_sum_identity ι r a
  have key (u : ∀ a, Low (r a) → ℂ) : ∑ j, c j * flagDens ((h a).pull π w) (fl a)
      (comb (fun x : Σ a, Fin (r a) => VMetric.grLB (fl x.1) x.2 ((H x.1).pull π w)) (n j)) _ σ c'
        (c'.e.symm (pt e z u)) = κ / Real.pi ^ (Fintype.card (Σ a, Low (r a)) + 1) * ∏ b, (jacDens (G b) (u b) *
          if b = a then ∑ i : Fin (r b), ((r b : ℝ) - 1 - 2 * (i : ℕ)) * theta (G b) (K b) (u b) i else 1) := by
    obtain ⟨-, -, J, h₁, h₂, h₃, -⟩ := hu u
    have hm (j) := mix_chg_diagonal e J
      (fun s => ∑ x, (n j x : ℝ) * rootDiag (fun x => theta (G x.1) (K x.1) (u x.1) x.2) x s) (bcDiag a)
    simp only [flagDens, h₂, h₃, hm, mul_left_comm (c _) (_ / _)]
    rw [← Finset.mul_sum, hκ I c n hV, h₁, Finset.prod_mul_distrib, Finset.prod_ite_eq', if_pos (Finset.mem_univ _)]
    ring
  simp only [key]
  rw [integral_const_mul, integral_fintype_prod_volume_eq_prod fun b (x : Low (r b) → ℂ) => jacDens (G b) x *
    if b = a then ∑ i : Fin (r b), ((r b : ℝ) - 1 - 2 * (i : ℕ)) * theta (G b) (K b) x i else 1,
    Finset.prod_eq_zero (Finset.mem_univ a), mul_zero]
  simp only [if_true]
  exact T.jacobi_density_weighted_theta_integral_zero _ _ _ (hG a) (hK a)

theorem sum_bcPair_pull {F : B.Modules} {s : ℕ} {g : VMetric q F s} (Hg : g.IsCInf) (m : Vert.Flag F s) :
    ∑ j, c j * bcPair (g.pull π w) (m.pull π)
      (comb (fun x : Σ a, Fin (r a) => VMetric.grLB (fl x.1) x.2 ((H x.1).pull π w)) (n j)) d =
      (∏ a, ((r a).factorial : ℝ)) * g.flagBc m := by
  subst hd
  have := hp.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  simp only [bcPair, VMetric.flagBc, VMetric.bcInt, finsum_eq_sum_of_fintype, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ (α := Fin s))]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hR := (RegGenSmooth.genSmooth_of_isRegSurf k B q hq).1 σ
  have hD (j) := isDens_flagDens (Hg.pull π w) (m.pull π)
    (comb (fun x : Σ a, Fin (r a) => VMetric.grLB (fl x.1) x.2 ((H x.1).pull π w)) (n j))
      (Fintype.card (Σ a, Low (r a))) σ
  have hS (i : Fin s) : ((g.stepMet m i).met σ).IsCInf := Hg.restrict (m.isSubbundle i.succ) (m.isVB i.succ) σ
  have hB (i : Fin s) : IsDens fun (c : AlgChart q σ 1) y => ((g.stepMet m i).met σ).bcDens
      (VMetric.stepSeq_shortExact m i) (m.isVB i.castSucc) (m.isVB_gr i) c y := CurveDens.isDens_bcDens _ _ _ (hS i)
  simp only [← CurveDens.total_bcDens _ _ _ (hS _), ← (total_eq_curve _).2.1]
  rw [← total_sum hp (hs σ) c hD, ← total_sum hq.toIsArithVar hR (fun _ => ∏ a, ((r a).factorial : ℝ)) hB]
  refine T.arithmetic_density_pushforward_integral k B Y q p π w ι r _ e σ hq.toIsArithVar hp hR (hs σ) _ _
    (IsDens.sum _ fun j => (hD j).mul continuous_const) (IsDens.sum _ fun j => (hB j).mul continuous_const) fun y => ?_
  obtain ⟨R⟩ := hR
  obtain ⟨i, hi⟩ := R.cover y
  obtain ⟨c₁, cE, c', hy, hE, hc, hf⟩ := T.flag_bundle_chart_lift k B Y q p π w ι r _ e σ E h fl hfl _ y hi
  refine ⟨c₁, c', hy, hc, fun z hz => ?_⟩
  obtain ⟨G, K, hG, hK, hu⟩ := cell_forms H e hE hc hf hz
  rw [← Finset.mul_sum]
  set t := ∑ i, ((g.stepMet m i).met σ).bcDens (VMetric.stepSeq_shortExact m i) (m.isVB i.castSucc) (m.isVB_gr i) c₁
    (c₁.e.symm z) with ht
  have key (u : ∀ a, Low (r a) → ℂ) : ∑ j, c j * flagDens (g.pull π w) (m.pull π)
      (comb (fun x : Σ a, Fin (r a) => VMetric.grLB (fl x.1) x.2 ((H x.1).pull π w)) (n j)) _ σ c'
        (c'.e.symm (pt e z u)) = (t / Real.pi ^ Fintype.card (Σ a, Low (r a)) *
          ∏ a, ∏ l ∈ Finset.range (r a + 1), (l.factorial : ℝ)) * ∏ b, jacDens (G b) (u b) := by
    obtain ⟨h₀, h₀', J, h₁, h₂, -, h₃⟩ := hu u
    have e₁ (f : Option (Σ a, Low (r a)) → ℝ) :
        ∑ s, baseDiag s * ∏ s' ∈ Finset.univ.erase s, f s' = ∏ s, f (some s) := by
      rw [Fintype.sum_option]
      simp only [baseDiag, Option.elim, zero_mul, Finset.sum_const_zero, add_zero, one_mul]
      exact (Finset.prod_bij (fun s _ => some s) (by simp) (by simp) (by rintro (_ | s) <;> simp) fun _ _ => rfl).symm
    simp only [flagDens, h₂, T.flag_matrix_pullback_chart k B Y q p π w ι r _ e σ F s g Hg m c₁ c' hc _ h₀, h₀', ← ht, mix_smul]
    rw [← h₃]
    have hm (j) := mix_chg_diagonal e J
      (fun s => ∑ x, (n j x : ℝ) * rootDiag (fun x => theta (G x.1) (K x.1) (u x.1) x.2) x s) baseDiag
    simp only [hm, e₁, mul_left_comm (c _) (_ * t), mul_left_comm (c _) (_ / _)]
    rw [← Finset.mul_sum, ← Finset.mul_sum, T.vandermonde_weighted_root_product_sum ι r I c n hV, h₁]
    have := Real.pi_ne_zero
    rw [pow_succ Real.pi]
    field_simp
  simp only [key]
  rw [integral_const_mul, integral_fintype_prod_volume_eq_prod fun b (x : Low (r b) → ℂ) => jacDens (G b) x]
  simp only [integral_jacDens (hG _), Finset.prod_range_succ, Finset.prod_mul_distrib, Finset.prod_div_distrib,
    Finset.prod_pow_eq_pow_sum, Fintype.card_sigma]
  have := Real.pi_ne_zero
  have : ∏ a, ∏ l ∈ Finset.range (r a), (l.factorial : ℝ) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun _ _ => Finset.prod_ne_zero_iff.2 fun _ _ => by positivity
  field_simp

end Fibre

theorem dim_genSmooth {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {D : ℕ} (hq : IsRegSurf q)
    (hp : IsArithVar p D) {π : Y ⟶ B} (w : π ≫ q = p) {ι : Type} [Fintype ι] {E : ι → B.Modules} {r : ι → ℕ}
    (hE : ∀ a, IsVB (E a) (r a)) {fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)}
    (hfl : IsFlagBundle π E r fl) :
    D = Fintype.card (Σ a, Low (r a)) + 1 ∧ GenSmooth p (Fintype.card (Σ a, Low (r a)) + 1) := by
  have hc : Fintype.card (Σ a, Low (r a)) = ∑ a, r a * (r a - 1) / 2 := by
    rw [Fintype.card_sigma]
    exact Finset.sum_congr rfl fun a _ => (card_low _).2
  have hs := T.flag_bundle_smooth_relative_dimension B Y π ι E r fl hE hfl
  rw [← hc] at hs
  have := hq.toIsArithVar.isLocallyNoetherian
  refine ⟨?_, fun σ => ⟨⟨AlgChart p σ _, id, fun y => ?_⟩⟩⟩
  · have h₁ := (T.krull_dim_smooth_surjective_total B Y π (Fintype.card (Σ a, Low (r a))) 1 (T.flag_bundle_projection_surjective B Y π ι E r fl hE hfl) hq.toIsArithVar.dim_eq).symm.trans hp.dim_eq
    have h₂ : 1 + Fintype.card (Σ a, Low (r a)) + 1 = D + 1 := by exact_mod_cast h₁
    omega
  · obtain ⟨U, hU, _⟩ := (RegGenSmooth.genSmooth_of_isRegSurf k B q hq).2 σ (PtsOver.map π w _ y)
    have : SmoothOfRelativeDimension (Fintype.card (Σ a, Low (r a))) (π ∣_ U) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (isPullback_morphismRestrict π U).flip hs
    have : SmoothOfRelativeDimension (Fintype.card (Σ a, Low (r a)) + 1) ((π ⁻¹ᵁ U).ι ≫ p) := by
      rw [← w, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]
      infer_instance
    obtain ⟨W, x, hW, hz, hx⟩ := ModelCharts.exists_etale_coords_of_opens p (Fintype.card (Σ a, Low (r a)) + 1) (π ⁻¹ᵁ U)
      (mem_ptsIn.1 (show y ∈ ptsIn p σ (π ⁻¹ᵁ U) from hU))
    obtain ⟨c, hc, -⟩ := AlgChart.exists_of_etale hW x hx (mem_ptsIn.2 hz)
    exact ⟨c, hc⟩

open MvPolynomial GlobalTheory.CovTop in

theorem taut_eq_pull_sub : Hypotheses2 → ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (D : ℕ), IsRegSurf q → IsArithVar p D → ∀ (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (h : ∀ a, VMetric q (E a) (r a)) (H : ∀ a, (h a).IsCInf) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → ∀ m : ∀ a, Vert.Flag (E a) (r a), (∀ a, (h a).FlagBcFinite (m a)) → ∀ Φ : MvPolynomial (Σ a, Fin (r a)) ℝ →ₗ[ℝ] ℝ, IsArFun (fun z : Σ a, Fin (r a) => VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w)) D Φ → ∀ Ψ : MvPolynomial ((Σ a, Fin (r a)) ⊕ (Σ a, Fin (r a))) ℝ →ₗ[ℝ] ℝ, IsArFun (Sum.elim (fun z : Σ a, Fin (r a) => VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w)) (fun z : Σ a, Fin (r a) => (VMetric.grLB (m z.1) z.2 (H z.1)).pull π w)) D Ψ → Φ ((∑ z : Σ a, Fin (r a), MvPolynomial.X z ^ 2) * (∏ a, ∏ i : Fin (r a), ∏ i' ∈ Finset.Ioi i, (MvPolynomial.X (⟨a, i'⟩ : Σ a, Fin (r a)) - MvPolynomial.X ⟨a, i⟩))) = Ψ (rename Sum.inr (∑ z : Σ a, Fin (r a), MvPolynomial.X z ^ 2) * rename Sum.inl (∏ a, ∏ i : Fin (r a), ∏ i' ∈ Finset.Ioi i, (MvPolynomial.X (⟨a, i'⟩ : Σ a, Fin (r a)) - MvPolynomial.X ⟨a, i⟩))) - (∏ a, ((r a).factorial : ℝ)) * ∑ a, (h a).flagBc (m a) := by
  intro HP k _ B Y _ _ q p D hq hp π w ι _ E r h H fl hfl m _ Φ hΦ Ψ hΨ
  obtain ⟨rfl, hs⟩ := dim_genSmooth hq hp w (fun a => (h a).isVB) hfl
  obtain ⟨I, _, c, n, hV⟩ := exists_sum_pow (isHomogeneous_vdm r)
  let e : Fin (Fintype.card (Σ a, Low (r a)) + 1) ≃ Option (Σ a, Low (r a)) :=
    (Fintype.equivFinOfCardEq Fintype.card_option).symm
  have key (a : ι) (j : I) := compare HP.p4 HP.q16 hp ((H a).pull π w) (fl a) ((m a).pull π) _ _ Ψ hΨ
    (fun i => .inl ⟨a, i⟩) (fun i => .inr ⟨a, i⟩) (fun _ => .refl _)
    (fun i => (VMetric.isometric_grLB_pull k B Y q p _ _ (h a) (H a) (m a) π w i).symm) (Sum.elim (n j) fun _ => 0)
  simp only [bcPair_congr _ _ (isometric_comb_inl _ _ _), ← rename_inl_lin] at key
  have e₁ (a : ι) := (Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => congrArg (c j * ·) (key a j))
  simp only [mul_sub, Finset.sum_sub_distrib, sum_bcPair_taut H e hq hp hs hfl rfl hV,
    sum_bcPair_pull H e hq hp hs hfl rfl hV (H _), zero_sub] at e₁
  have e₂ : Ψ ((rename Sum.inl (∑ z : Σ a, Fin (r a), MvPolynomial.X z ^ 2) -
      rename Sum.inr (∑ z : Σ a, Fin (r a), MvPolynomial.X z ^ 2)) * rename Sum.inl (vdm r)) =
      -((∏ a, ((r a).factorial : ℝ)) * ∑ a, (h a).flagBc (m a)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_congr rfl fun a _ => e₁ a, ← hV]
    simp only [← smul_eq_mul (α := ℝ), ← map_smul, ← map_sum Ψ]
    congr 1
    rw [Finset.sum_comm, map_sum (rename _) (fun j => c j • _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.smul_sum, ← Finset.sum_mul, map_smul, mul_smul_comm, map_pow]
    simp only [map_sum, map_pow, rename_X, Fintype.sum_sigma, Finset.sum_sub_distrib]
  rw [sub_mul, map_sub, ← map_mul, isArFun_restrict_inl HP.p4.arIso hp _ _ hΦ hΨ] at e₂
  exact (sub_eq_iff_eq_add'.1 e₂).trans (sub_eq_add_neg _ _).symm

end GlobalTheory.FlagCmp
