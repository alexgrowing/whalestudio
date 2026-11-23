import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOnRegularFlagged
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingEverywhereOfRegularAlteration
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineSpaceCoveredSmoothOfRelativeDimensionAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChartBigCellStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleBigCellMetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIntegrationDensitiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJacobianBlockDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMixedDiscriminantFunctionalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedDiscriminantBigCellStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationMixedCoefficientStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

namespace GlobalTheory.BigCell

theorem smooth_chart {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {n : ℕ}
    (c : AlgChart p σ n) : SmoothOfRelativeDimension n (c.U.ι ≫ p) := by
  have := σ.domain_nontrivial
  have h₁ : RingHom.IsStandardSmoothOfRelativeDimension n (algebraMap k (MvPolynomial (Fin n) k)) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).2 (FlagBundle.affSmooth_mvPolynomial k n)
  have h₂ := (RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero.1 c.etale).comp h₁
  have h₃ := (RingHom.IsStandardSmoothOfRelativeDimension.equiv c.U.topIso.symm.commRingCatIsoToRingEquiv).comp
    (h₂.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv))
  have : IsAffine c.U.toScheme := c.affine
  refine ⟨fun x => ⟨⊤, isAffineOpen_top _, ⊤, isAffineOpen_top _, trivial, le_top, ?_⟩⟩
  simp only [zero_add, add_zero] at h₃
  convert h₃ using 1
  rw [← Scheme.Hom.appLE_comp_appLE c.U.ι p ⊤ c.U ⊤ le_top (by simp)]
  ext a
  simp only [DVR.FlatBC.algX, Scheme.Opens.ι_appLE, RingHom.comp_apply, MvPolynomial.algebraMap_eq,
    MvPolynomial.eval₂Hom_C, CommRingCat.hom_comp]
  erw [Iso.hom_inv_id_apply]
  rfl

theorem theta_herm {m : ℕ} {G : Matrix (Fin m) (Fin m) ℂ} (hG : G.IsHermitian) (K : Matrix (Fin m) (Fin m) ℂ)
    (u : Low m → ℂ) (i : Fin m) : theta G ((1 / 2 : ℂ) • (K + Kᴴ)) u i = theta G K u i := by
  have hc (M : Matrix (Fin m) (Fin m) ℂ) : chg (uni u) Mᴴ = (chg (uni u) M)ᴴ := by
    simp only [chg, conjTranspose_mul, Matrix.mul_assoc]
    congr 1
    ext
    simp
  have key (j : Fin (m + 1)) : logMinorDer G ((1 / 2 : ℂ) • (K + Kᴴ)) u j = logMinorDer G K u j := by
    unfold logMinorDer
    set f := Fin.castLE (Nat.le_of_lt_succ j.isLt)
    have hA : ((chg (uni u) G).submatrix f f)⁻¹ᴴ = ((chg (uni u) G).submatrix f f)⁻¹ := by
      rw [conjTranspose_nonsing_inv, conjTranspose_submatrix, ← hc, hG.eq]
    have e : (chg (uni u) ((1 / 2 : ℂ) • (K + Kᴴ))).submatrix f f =
        (1 / 2 : ℂ) • ((chg (uni u) K).submatrix f f + ((chg (uni u) K).submatrix f f)ᴴ) := by
      rw [conjTranspose_submatrix, ← hc]
      simp only [chg, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]
      rfl
    rw [e]
    generalize (chg (uni u) K).submatrix f f = X at *
    generalize ((chg (uni u) G).submatrix f f)⁻¹ = A at *
    have e₂ : (A * Xᴴ).trace = star (A * X).trace := by
      rw [← trace_conjTranspose, conjTranspose_mul, hA, trace_mul_comm]
    rw [Matrix.mul_smul, Matrix.mul_add, trace_smul, trace_add, e₂]
    simp
    ring
  simp only [theta, key]

theorem integral_theta {m : ℕ} {G : Matrix (Fin m) (Fin m) ℂ} (hG : G.PosDef) (K : Matrix (Fin m) (Fin m) ℂ) :
    ∫ u : Low m → ℂ, jacDens G u * ∑ i : Fin m, ((m : ℝ) - 1 - 2 * (i : ℕ)) * theta G K u i = 0 := by
  simp only [← theta_herm hG.isHermitian K]
  refine T.jacobi_density_weighted_theta_integral_zero _ _ _ hG ?_
  simp [IsHermitian, conjTranspose_smul, add_comm]

open MvPolynomial in

theorem rename_lin {α κ : Type} [Fintype α] [Fintype κ] (f : α → κ) (n : α → ℝ) :
    rename f (lin n) = lin fun i => ∑ s with f s = i, n s := by
  simp only [lin, map_sum, map_mul, rename_C, rename_X, Finset.sum_mul]
  rw [← Finset.sum_fiberwise Finset.univ f]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s hs => by rw [(Finset.mem_filter.1 hs).2]

variable {ι : Type} [Fintype ι] {r : ι → ℕ}

omit [Fintype ι] in

theorem sum_smul_blk {n D : ℕ} (ε : Fin D ≃ Fin n ⊕ (Σ a, Low (r a))) {α : Type} [Fintype α] (t : α → ℝ)
    (N : α → Matrix (Fin n) (Fin n) ℂ) (δ : α → (Σ a, Low (r a)) → ℝ) :
    ∑ x, (t x : ℂ) • blk ε (N x) (δ x) = blk ε (∑ x, (t x : ℂ) • N x) fun s => ∑ x, t x * δ x s := by
  ext i j
  simp only [blk, Matrix.sum_apply, Matrix.smul_apply, submatrix_apply]
  rcases ε i with a | a <;> rcases ε j with b | b
  · simp [Matrix.sum_apply]
  · simp
  · simp
  · by_cases h : a = b <;> simp [diagonal_apply, h]

open MvPolynomial in

theorem sum_mix {μ : Type} [Fintype μ] {e D : ℕ} (ε : Fin (D + 1) ≃ Fin (e + 1) ⊕ (Σ a, Low (r a))) (a : ι)
    {P : MvPolynomial μ ℝ} (hP : P.IsHomogeneous e) (N : μ → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) :
    ∃ W : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ, ∀ {κ : Type} [Fintype κ] {x : (Σ a, Fin (r a)) → κ} {y : μ → κ}
      {I : Type} [Fintype I] {c : I → ℝ} {n : I → κ → ℤ},
      ∑ j, c j • lin (fun i => (n j i : ℝ)) ^ D = rename x (vdm r) * rename y P →
      ∀ (C : κ → Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ) (J : Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ)
        (Θ : (Σ a, Fin (r a)) → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ),
        (∀ z, C (x z) = chg J (blk ε (Θ z) fun t => rootDiag 0 z (some t))) → (∀ m, C (y m) = chg J (blk ε (N m) 0)) →
        ∑ j, c j * mix D (∑ i, (n j i : ℂ) • C i) (chg J (blk ε 0 fun t => bcDiag a (some t))) =
          ‖J.det‖ ^ 2 * ∑ i : Fin (r a), ((r a : ℝ) - 1 - 2 * (i : ℕ)) * (W * Θ ⟨a, i⟩).trace.re := by
  obtain ⟨f, hf⟩ : ∃ f, Fintype.card (Σ a, Low (r a)) = f := ⟨_, rfl⟩
  obtain rfl : D = f + e := by
    have := Fintype.card_congr ε
    simp only [Fintype.card_fin, Fintype.card_sum] at this
    omega
  obtain ⟨I₁, _, c₁, n₁, h₁⟩ := FlagCmp.exists_sum_pow (FlagCmp.isHomogeneous_vdm r)
  obtain ⟨I₂, _, c₂, n₂, h₂⟩ := FlagCmp.exists_sum_pow hP
  obtain ⟨κ₀, hκ⟩ := T.vandermonde_boundary_term_sum_identity ι r a
  replace hκ := hκ I₁ c₁ n₁ h₁
  rw [hf] at h₁ hκ
  let s : ℝ := ((f + e).factorial : ℝ) / Real.pi ^ (f + e + 1) / ((f + e).choose e : ℝ) / f.factorial
  refine ⟨∑ l, ((c₂ l * s * κ₀ : ℝ) : ℂ) • (∑ m, ((n₂ l m : ℝ) : ℂ) • N m).adjugate, ?_⟩
  intro κ _ x y I _ c n hV C J Θ hx hy
  obtain ⟨Λ, hΛ⟩ := T.exists_mixed_discriminant_functional κ (f + e) C (chg J (blk ε 0 fun t => bcDiag a (some t)))
  have e₁ (j : I) := hΛ fun i => (n j i : ℝ)
  simp only [Complex.ofReal_intCast] at e₁
  have e₀ : ∑ j, c j * mix (f + e) (∑ i, (n j i : ℂ) • C i) (chg J (blk ε 0 fun t => bcDiag a (some t))) =
      Λ (rename x (vdm r) * rename y P) := by
    simp only [← hV, ← e₁, map_sum, map_smul, smul_eq_mul]
  rw [e₀, ← h₁, ← h₂]
  have key (j : I₁) (l : I₂) : Λ (rename x (lin fun z => (n₁ j z : ℝ)) ^ f * rename y (lin fun m => (n₂ l m : ℝ)) ^ e) =
      ‖J.det‖ ^ 2 * s * (f.factorial * ∑ t : Option (Σ a, Low (r a)), bcDiag a t * ∏ t' ∈ Finset.univ.erase t,
        ∑ z, (n₁ j z : ℝ) * rootDiag (fun z => ((∑ m, ((n₂ l m : ℝ) : ℂ) • N m).adjugate * Θ z).trace.re) z t') := by
    have h := T.polarization_mixed_coefficient _ Λ (rename x (lin fun z => (n₁ j z : ℝ))) (rename y (lin fun m => (n₂ l m : ℝ))) f e
      (∑ z, ((n₁ j z : ℝ) : ℂ) • Θ z) (∑ m, ((n₂ l m : ℝ) : ℂ) • N m)
      (‖J.det‖ ^ 2 * (((f + e).factorial : ℝ) / Real.pi ^ (f + e + 1)) * ∑ t, bcDiag a (some t) *
        ∏ t' ∈ Finset.univ.erase t, VdmCoef.root (fun z => (n₁ j z : ℝ)) t') fun t => by
        have e₂ : rename x (lin fun z => (n₁ j z : ℝ)) + t • rename y (lin fun m => (n₂ l m : ℝ)) =
            rename (Sum.elim x y) (lin (Sum.elim (fun z => (n₁ j z : ℝ)) fun m => t * n₂ l m)) := by
          simp [lin, Fintype.sum_sum_type, Finset.mul_sum, smul_eq_C_mul, mul_assoc, -map_intCast]
        have e₃ (v : (Σ a, Fin (r a)) ⊕ μ → ℝ) : ∑ i, ((∑ s with Sum.elim x y s = i, v s : ℝ) : ℂ) • C i =
            ∑ s, (v s : ℂ) • C (Sum.elim x y s) := by
          simp only [Complex.ofReal_sum, Finset.sum_smul]
          rw [← Finset.sum_fiberwise Finset.univ (Sum.elim x y)]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s hs => by rw [(Finset.mem_filter.1 hs).2]
        have e₄ (s : (Σ a, Fin (r a)) ⊕ μ) : C (Sum.elim x y s) = chg J (blk ε (Sum.elim Θ N s)
            (Sum.elim (fun z t => rootDiag 0 z (some t)) (fun _ => 0) s)) := by
          rcases s with z | m
          exacts [hx z, hy m]
        have e₅ (v : (Σ a, Fin (r a)) ⊕ μ → ℂ) (M : (Σ a, Fin (r a)) ⊕ μ → Matrix (Fin (f + e + 1)) (Fin (f + e + 1)) ℂ) :
            ∑ s, v s • chg J (M s) = chg J (∑ s, v s • M s) := by
          simp only [chg, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
        rw [e₂, rename_lin, hΛ, e₃]
        simp only [e₄]
        rw [e₅, sum_smul_blk, mix_chg, T.mixed_discriminant_big_cell]
        simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
          add_zero, VdmCoef.pair_rootDiag, Complex.ofReal_mul, mul_smul, ← Finset.smul_sum]
        ring
    have hc : ((f + e).choose e : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.choose_pos (by omega)).ne'
    have hf' : (f.factorial : ℝ) ≠ 0 := by positivity
    rw [Fintype.sum_option, show bcDiag a (none : Option (Σ a, Low (r a))) = 0 from rfl, zero_mul, zero_add]
    simp only [VdmCoef.prod_erase_some, mul_left_comm (bcDiag _ _), ← Finset.mul_sum]
    rw [eq_div_of_mul_eq hc ((mul_comm _ _).trans h)]
    simp only [s, Matrix.mul_sum, Matrix.mul_smul, trace_sum, trace_smul, smul_eq_mul, Complex.re_sum,
      Complex.re_ofReal_mul]
    field_simp
  simp only [map_sum, map_smul, map_pow, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, smul_eq_mul, Matrix.sum_mul,
    Matrix.smul_mul, trace_sum, trace_smul, Complex.re_sum, Complex.re_ofReal_mul]
  rw [Finset.sum_comm (s := Finset.univ (α := Fin (r a)))]
  refine Finset.sum_congr rfl fun l _ => ?_
  have h := hκ fun z => ((∑ m, ((n₂ l m : ℝ) : ℂ) • N m).adjugate * Θ z).trace.re
  simp only [key]
  calc _ = c₂ l * (‖J.det‖ ^ 2 * s) * _ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = c₂ l * (‖J.det‖ ^ 2 * s) * _ := congrArg _ h
    _ = _ := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring

section Fibre

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {π : Y ⟶ B}
  {E : ι → B.Modules} {fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)}

theorem dim_genSmooth {n D : ℕ} (hq : IsArithVar q n) (hs : GenSmooth q n) (hp : IsArithVar p D) (w : π ≫ q = p)
    (hE : ∀ a, IsVB (E a) (r a)) (hfl : IsFlagBundle π E r fl) :
    D = n + Fintype.card (Σ a, Low (r a)) ∧ GenSmooth p D := by
  have hc : Fintype.card (Σ a, Low (r a)) = ∑ a, r a * (r a - 1) / 2 := by
    rw [Fintype.card_sigma]
    exact Finset.sum_congr rfl fun a _ => (FlagCmp.card_low _).2
  have hπ := T.flag_bundle_smooth_relative_dimension B Y π ι E r fl hE hfl
  rw [← hc] at hπ
  have := hq.isLocallyNoetherian
  have hD : D = n + Fintype.card (Σ a, Low (r a)) := by
    have h₁ := (T.krull_dim_smooth_surjective_total B Y π (Fintype.card (Σ a, Low (r a))) n (T.flag_bundle_projection_surjective B Y π ι E r fl hE hfl)
      hq.dim_eq).symm.trans hp.dim_eq
    have h₂ : n + Fintype.card (Σ a, Low (r a)) + 1 = D + 1 := by exact_mod_cast h₁
    omega
  refine ⟨hD, fun σ => ⟨⟨AlgChart p σ _, id, fun y => ?_⟩⟩⟩
  obtain ⟨R⟩ := hs σ
  obtain ⟨i, hi⟩ := R.cover (PtsOver.map π w _ y)
  have := smooth_chart (R.chart i)
  have hU := (R.chart i).source_subset hi
  generalize (R.chart i).U = U at this hU
  have : SmoothOfRelativeDimension (Fintype.card (Σ a, Low (r a))) (π ∣_ U) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (isPullback_morphismRestrict π U).flip hπ
  have : SmoothOfRelativeDimension D ((π ⁻¹ᵁ U).ι ≫ p) := by
    rw [hD, add_comm, ← w, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    infer_instance
  obtain ⟨W, x, hW, hz, hx⟩ := ModelCharts.exists_etale_coords_of_opens p D (π ⁻¹ᵁ U)
    (mem_ptsIn.1 (show y ∈ ptsIn p σ (π ⁻¹ᵁ U) from hU))
  obtain ⟨c, hc, -⟩ := AlgChart.exists_of_etale hW x hx (mem_ptsIn.2 hz)
  exact ⟨c, hc⟩

open MvPolynomial in

theorem sum_bcPair_of_genSmooth [IsIntegral Y] {e D : ℕ} (hq : IsArithVar q (e + 1)) (hs : GenSmooth q (e + 1))
    (hp : IsArithVar p (D + 1)) (w : π ≫ q = p) {h : ∀ a, VMetric q (E a) (r a)} (H : ∀ a, (h a).IsCInf)
    (hfl : IsFlagBundle π E r fl) {κ μ : Type} [Fintype κ] [Fintype μ] {L : κ → HermLB p} {A : μ → HermLB q}
    {x : (Σ a, Fin (r a)) → κ} {y : μ → κ}
    (hx : ∀ z, (L (x z)).Isometric (VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w)))
    (hy : ∀ m, (L (y m)).Isometric ((A m).pull π w)) {P : MvPolynomial μ ℝ} (hP : P.IsHomogeneous e)
    {I : Type} [Fintype I] {c : I → ℝ} {n : I → κ → ℤ}
    (hV : ∑ j, c j • lin (fun i => (n j i : ℝ)) ^ D = rename x (vdm r) * rename y P) (a : ι) :
    ∑ j, c j * bcPair ((h a).pull π w) (fl a) (comb L (n j)) D = 0 := by
  obtain ⟨hD, hs'⟩ := dim_genSmooth hq hs hp w (fun a => (h a).isVB) hfl
  let ε : Fin (D + 1) ≃ Fin (e + 1) ⊕ (Σ a, Low (r a)) :=
    (Fintype.equivFinOfCardEq (by rw [Fintype.card_sum, Fintype.card_fin, hD])).symm
  have := hp.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  simp only [bcPair, finsum_eq_sum_of_fintype, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun σ _ => ?_
  have hd (j) := FlagCmp.isDens_flagDens ((H a).pull π w) (fl a) (comb L (n j)) D σ
  rw [← FlagCmp.total_sum hp (hs' σ) c hd, ← total_zero (p := q) (σ := σ) (D := e + 1)]
  refine T.fibre_integration_densities k B Y q p π w ι r _ _ ε σ hq hp (hs σ) (hs' σ) _ _
    (IsDens.sum _ fun j => (hd j).mul continuous_const) isDens_zero fun b => ?_
  obtain ⟨R⟩ := hs σ
  obtain ⟨i, hi⟩ := R.cover b
  obtain ⟨c₁, cE, c', hb, hE, hc, hf⟩ := T.flag_bundle_chart_big_cell k B Y q p π w ι r _ _ ε σ E h fl hfl _ b hi
  refine ⟨c₁, c', hb, hc, fun z hz => ?_⟩
  have hz' := c₁.e.map_target hz
  have hpos (a) : ∀ᶠ u in 𝓝 z, (((h a).met σ).G (cE a) (c₁.e.symm u)).PosDef :=
    Filter.eventually_of_mem (c₁.e.open_target.mem_nhds hz) fun u hu =>
      ((h a).met σ).posDef _ _ (hE a (c₁.e.map_target hu))
  obtain ⟨F, hJ⟩ := T.exists_jacobian_block_decomposition ι r _ _ ε (fun a u => ((h a).met σ).G (cE a) (c₁.e.symm u)) z (fun a => by
    have := (H a σ (cE a) _ (hE a hz')).mContDiffAt c₁ hz'
    rwa [c₁.e.right_inv hz] at this) hpos
  obtain ⟨W, hW⟩ := sum_mix ε a hP fun m => chernMat ((A m).φ σ) c₁ (c₁.e.symm z)
  set G := fun a => ((h a).met σ).G (cE a) (c₁.e.symm z) with hG
  have key (u : ∀ a, Low (r a) → ℂ) : ∑ j, c j * flagDens ((h a).pull π w) (fl a) (comb L (n j)) D σ c'
        (c'.e.symm (pt ε z u)) = ∏ b, (jacDens (G b) (u b) * if b = a then
          ∑ i : Fin (r b), ((r b : ℝ) - 1 - 2 * (i : ℕ)) * theta (G b) (∑ j, ∑ l, W l j • F b j l) (u b) i else 1) := by
    have ht : pt ε z u ∈ c'.e.target := by
      rw [hc.2.1]
      simpa only [Set.mem_setOf_eq, base_pt] using hz
    have hs := c'.e.map_target ht
    obtain ⟨J, Θ, h₁, h₂, h₃, h₄, h₅⟩ := hJ u
    obtain ⟨b₁, b₂, b₃⟩ := T.flag_bundle_big_cell_metric k B Y q p π w ι r _ _ ε σ E h H fl c₁ cE c' hc hf _ hs
    rw [c'.e.right_inv ht] at b₁ b₂
    have e₁ : PtsOver.map π w (spMap σ) (c'.e.symm (pt ε z u)) = c₁.e.symm z := by
      have := hc.2.2 _ hs
      rw [c'.e.right_inv ht, base_pt] at this
      exact (c₁.e.left_inv (hc.1.le hs).1).symm.trans (congrArg c₁.e.symm this.symm)
    simp only [flagDens, T.chernMat_linear_combination k Y p σ (D + 1) _ _ _ c' _ hs, (b₂ a).trans (h₄ a)]
    rw [hW hV _ J Θ (fun z => by rw [chernMat_congr (hx z) c' hs, b₁, h₃])
      (fun m => by rw [chernMat_congr (hy m) c' hs, b₃, h₅, e₁]), h₁, Finset.prod_mul_distrib, Finset.prod_ite_eq',
      if_pos (Finset.mem_univ _)]
    simp only [h₂, G]
  simp only [key]
  rw [integral_fintype_prod_volume_eq_prod fun b (x : Low (r b) → ℂ) => jacDens (G b) x * if b = a then
      ∑ i : Fin (r b), ((r b : ℝ) - 1 - 2 * (i : ℕ)) * theta (G b) (∑ j, ∑ l, W l j • F b j l) x i else 1,
    Finset.prod_eq_zero (Finset.mem_univ a)]
  simp only [if_true]
  exact integral_theta (hpos a).self_of_nhds _

end Fibre

open MvPolynomial GlobalTheory.CovTop Limits in

theorem sum_bcPair_vdm_eq_zero : Hypotheses2 → ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (e D : ℕ), IsArithVar q (e + 1) → IsArithVar p (D + 1) → ∀ (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (h : ∀ a, VMetric q (E a) (r a)) (H : ∀ a, (h a).IsCInf) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → ∀ (κ μ : Type) [Fintype κ] [Fintype μ] (L : κ → HermLB p) (A : μ → HermLB q) (x : (Σ a, Fin (r a)) → κ) (y : μ → κ), (∀ z, (L (x z)).Isometric (VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w))) → (∀ m, (L (y m)).Isometric ((A m).pull π w)) → ∀ P : MvPolynomial μ ℝ, P.IsHomogeneous e → ∀ (I : Type) [Fintype I] (c : I → ℝ) (n : I → κ → ℤ), ∑ j, c j • lin (fun i => (n j i : ℝ)) ^ D = rename x (vdm r) * rename y P → ∀ a, ∑ j, c j * bcPair ((h a).pull π w) (fl a) (comb L (n j)) D = 0 := by
  intro HP k _ B Y _ _ q p e D hq hp π w ι _ E r h H fl hfl κ μ _ _ L A x y hx hy P hP I _ c n hV a
  subst w
  obtain ⟨B₁, g, _, hg, hs⟩ := T.principalisation_generic_smooth_cover HP.q16 k B q _ hq
  obtain ⟨_, hf⟩ := TwoLat.Gen.isCov_pullback_fst hq hp hg (fun a => (h a).isVB) hfl
  have w₁ : pullback.snd π g ≫ g ≫ q = pullback.fst π g ≫ π ≫ q := (pullback.condition_assoc q).symm
  have hI (a) := TwoLat.Gen.isIsometry_sqIso pullback.condition (h a) rfl rfl rfl w₁
  have key := sum_bcPair_of_genSmooth hg.1 hs hf.1 w₁ (fun a => (H a).pull g rfl)
    (FlagBaseChange.isFlagBundle_pullFlag B Y B₁ π g ι E r fl hfl) (L := fun i => (L i).pull (pullback.fst π g) rfl)
    (A := fun m => (A m).pull g rfl)
    (fun z => ((hx z).pull _ rfl).trans (TwoLat.Gen.isometric_grLB_pull_ofIso _ _ rfl (hI z.1) (fl z.1) z.2))
    (fun m => ((hy m).pull _ rfl).trans (TwoLat.Gen.isometric_sq pullback.condition _ rfl rfl rfl w₁)) hP hV a
  have e₁ (N : HermLB (pullback.fst π g ≫ π ≫ q)) := TwoLat.bcPair_eq_of_compat (((H a).pull g rfl).pull _ w₁) (hI a)
    (fl := (fl a).pull (pullback.fst π g)) (fl' := FlagBaseChange.pullFlag π g (fl a)) (fun i => ⟨𝟙 _, Category.id_comp _⟩) N D
  simp only [← e₁, bcPair_congr _ _ (isometric_comb_pull L _ (pullback.fst π g) rfl),
    T.flag_height_pairing_pullback_degree k Y _ _ D _ hp hf _ _ _ ((H a).pull π rfl), mul_left_comm (c _), ← Finset.mul_sum] at key
  exact (mul_eq_zero.1 key).resolve_left (Nat.cast_ne_zero.2 hf.2.2)

end GlobalTheory.BigCell
