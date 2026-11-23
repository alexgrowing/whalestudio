import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelGramPosSemidef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodReductionStatementHoldsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareFormStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InterpolationCurvatureBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightNormSqSmoothPosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPolydiscExistsAtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryPotentialSmoothOffDivisorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagComponentProjectionSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncComponentsLocalSncStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSncPullbackSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorNormPullbackComponentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncatedPotentialSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulPowLeRpow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRootDivisorRelation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LetterConjugation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorBoundaryPotentialsExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormBoundConnectionDifferenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormBoundConnectionTransferStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalModelChartFlagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLocalConjOfNotGoodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootGeneratorsGenerateAdaptedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorGeneratesChartEstimateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLocalOfGoodEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockModelPosFrameBoundStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCEqZeroOfEventuallyEqZero
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.CurvInterp
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CurvInterp

open Filter Topology
open scoped ContDiff

section Pure

open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram

theorem levi_mul {ι : Type} [Fintype ι] {f : (ι → ℂ) → ℝ} {z : ι → ℂ} (c : ℝ) (hf : ContDiffAt ℝ 2 f z) (w : ι → ℂ) :
    levi (fun y => c * f y) z w = c * levi f z w := by
  have h := levi_add_smul c (contDiffAt_const (c := (0 : ℝ))) hf w
  simpa [levi] using h

theorem levi_sub_const {ι : Type} [Fintype ι] {f : (ι → ℂ) → ℝ} {z : ι → ℂ} (c : ℝ) (w : ι → ℂ) :
    levi (fun y => f y - c) z w = levi f z w := by
  have : fderiv ℝ (fun y => f y - c) = fderiv ℝ f := funext fun y => fderiv_sub_const c
  simp only [levi, this]

theorem levi_lower_of_data {e : ℕ} {T : Type} [Fintype T] {p q : T → ℕ} {U : Set (Fin e → ℂ)} (hU : IsOpen U)
    {H₀W HW : ∀ τ, (Fin e → ℂ) → Matrix (Fin (p τ)) (Fin (p τ)) ℂ}
    {H₀ω Hω : ∀ τ, (Fin e → ℂ) → Matrix (Fin (q τ)) (Fin (q τ)) ℂ} {r : (Fin e → ℂ) → ℝ}
    {G : (Fin e → ℂ) → Matrix (Fin e) (Fin e) ℂ} {Cμ C₀ C₂ C₃ CP κ : ℝ} {χ : ℝ → ℝ} (hκ : 2 * Cμ + 2 < κ)
    (hχ : IsCutoff χ) (hW : ∀ τ, IsData Cμ C₀ C₂ C₃ CP U (H₀W τ) (HW τ) r G)
    (hω : ∀ τ, IsData Cμ C₀ C₂ C₃ CP U (H₀ω τ) (Hω τ) r G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 2 ≤ R → ∀ lam : ∀ τ, Fin (p τ + q τ) → ℝ,
      (∀ τ, Antitone fun i => lam τ (Fin.castAdd (q τ) i)) → (∀ τ, Antitone fun i => lam τ (Fin.natAdd (p τ) i)) →
      ∀ z ∈ U, ∀ w, -(C * ∑ τ, ∑ i, |lam τ i|) * (form (G z) w w).re ≤
        levi (fun v => -(1 / 2) * Real.log (pairWeightNormSq
          (fun τ => interp (H₀W τ) (HW τ) fun x => 1 * cutWeight χ κ R r x)
          (fun τ => interp (H₀ω τ) (Hω τ) fun x => 1 * cutWeight χ κ R r x) id (fun _ _ => 1) (fun _ _ => 1) lam v)) z w := by
  obtain ⟨C, hC⟩ := GlobalTheory.T.interpolation_curvature_bound Cμ C₀ C₂ C₃ CP κ χ hκ hχ
  refine ⟨max C 0 / 2, by positivity, fun R hR lam h1 h2 z hz w => ?_⟩
  have hs : IsWeight χ κ r fun x => 1 * cutWeight χ κ R r x := Or.inr ⟨1, ⟨zero_le_one, le_rfl⟩, R, hR, rfl⟩
  have aW := fun τ => (hC _ _ U _ _ r G (hW τ)).1 _ hs
  have aω := fun τ => (hC _ _ U _ _ r G (hω τ)).1 _ hs
  have hF : ∀ n : ℕ, IsFlagFamily U U id (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) := fun n =>
    ⟨hU, contDiffOn_id, fun _ h => h, fun _ _ => contDiffOn_const, fun _ _ => by simp⟩
  have key := GlobalTheory.T.good_reduction_statement_holds.2.1 (Fin e → ℂ) (Fin e) T p q U _ _ U id (fun _ _ => 1) (fun _ _ => 1) G (max C 0)
    (fun τ => (aW τ).1) (fun τ => (aω τ).1) (fun _ => hF _) (fun _ => hF _)
    (fun τ => (aW τ).2.1.mono (le_max_left _ _)) (fun τ => (aω τ).2.1.mono (le_max_left _ _)) lam h1 h2 z hz w
  set F := pairWeightNormSq (fun τ => interp (H₀W τ) (HW τ) fun x => 1 * cutWeight χ κ R r x)
    (fun τ => interp (H₀ω τ) (Hω τ) fun x => 1 * cutWeight χ κ R r x) id (fun _ _ => 1) (fun _ _ => 1) lam with hFdef
  have bW := fun τ => GlobalTheory.T.weight_norm_sq_smooth_pos _ _ _ U _ U id _ (aW τ).1 (hF _) z hz fun i => lam τ (Fin.castAdd (q τ) i)
  have bω := fun τ => GlobalTheory.T.weight_norm_sq_smooth_pos _ _ _ U _ U id _ (aω τ).1 (hF _) z hz fun i => lam τ (Fin.natAdd (p τ) i)
  have hF2 : ContDiffAt ℝ 2 F z := contDiffAt_prod fun τ _ => (bW τ).1.mul (bω τ).1
  have hF0 : 0 < F z := Finset.prod_pos fun τ _ => mul_pos (bW τ).2 (bω τ).2
  have hlog : ContDiffAt ℝ 2 (fun x => Real.log (F x)) z := hF2.log hF0.ne'
  have e1 : diagVal (lineChern F z) w = -(levi (fun x => Real.log (F x)) z w / (2 * Real.pi)) := by
    rw [← diagVal_ddc hlog w]
    simp only [diagVal, lineChern]
    rw [chernOne_line (f := F) hF2 hF0.ne' (Filter.Eventually.of_forall fun x => rfl)]
    simp
  have e2 : ∀ c : ℝ, diagVal (fun ξ η => (c : ℂ) * pullForm G id z ξ η) w = c * (form (G z) w w).re := fun c => by
    rw [← diagVal_formOf, diagVal, diagVal, mul_left_comm, Complex.re_ofReal_mul]
    simp [pullForm]
  rw [e1, e2] at key
  rw [levi_mul _ hlog]
  have hπ := Real.pi_pos
  have := mul_le_mul_of_nonneg_left key hπ.le
  refine le_of_eq_of_le ?_ (this.trans_eq ?_) <;> field_simp

theorem diagVal_gradForm {e : ℕ} {r : (Fin e → ℂ) → ℝ} {z : Fin e → ℂ} (hr : DifferentiableAt ℝ r z) (ξ : Fin e → ℂ) :
    diagVal (fun ξ η => gradForm r z ξ η / ((r z : ℂ) ^ 2)) ξ =
      1 / Real.pi * (((fderiv ℝ r z ξ) ^ 2 + (fderiv ℝ r z (Complex.I • ξ)) ^ 2) / 4) / r z ^ 2 / 2 := by
  have hd : ∀ v, fderiv ℝ (fun x => (r x : ℂ)) z v = fderiv ℝ r z v := fun v => by
    exact DFunLike.congr_fun (Complex.ofRealCLM.hasFDerivAt.comp z hr.hasFDerivAt).fderiv v
  have h4 : -Complex.I * (gradForm r z ξ ξ / ((r z : ℂ) ^ 2)) =
      ((1 / Real.pi * (((fderiv ℝ r z ξ) ^ 2 + (fderiv ℝ r z (Complex.I • ξ)) ^ 2) / 4) / r z ^ 2 / 2 : ℝ) : ℂ) := by
    rw [gradForm, del_apply, dbar_apply, hd, hd, kappa]
    push_cast
    simp only [smul_eq_mul]
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    generalize ((r z : ℝ) : ℂ) ^ 2 = s
    field_simp
    ring_nf
    simp only [Complex.I_sq, Complex.I_pow_four]
    ring
  rw [diagVal, h4, Complex.ofReal_re]

end Pure

section Man

open GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}

theorem isCompatChart_chart (A : FinHolAtlas e X) (j : Fin A.n) : IsCompatChart A (A.chart j) :=
  fun k => ⟨A.holo k j, A.holo j k⟩

theorem contDiffAt_two_compat {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} (hψ : IsCompatChart A ψ) {U : Set X} (hU : IsOpen U)
    {f : X → ℝ} (hf : A.SmoothOn U f) {z : Fin e → ℂ} (hz : z ∈ ψ.target) (hx : ψ.symm z ∈ U) :
    ContDiffAt ℝ 2 (f ∘ ψ.symm) z :=
  ((ReciprocityTheory.AnForm.M.PLAux.contDiffOn_compat hψ hU hf).contDiffAt
    ((ψ.isOpen_inter_preimage_symm hU).mem_nhds ⟨hz, hx⟩)).of_le (WithTop.coe_le_coe.2 le_top)

theorem levi_chart_eq {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} (hψ : IsCompatChart A ψ) {f : X → ℝ} (j : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) (hx : (A.chart j).symm y ∈ ψ.source)
    (hf : ContDiffAt ℝ 2 (f ∘ ψ.symm) (ψ ((A.chart j).symm y))) (w : Fin e → ℂ) :
    levi (f ∘ (A.chart j).symm) y w =
      levi (f ∘ ψ.symm) (ψ ((A.chart j).symm y)) (fderiv ℂ (ψ ∘ (A.chart j).symm) y w) := by
  have hT : AnalyticAt ℂ (ψ ∘ (A.chart j).symm) y := (hψ j).1 y ⟨hy, hx⟩
  have hev : (f ∘ (A.chart j).symm) =ᶠ[𝓝 y] ((f ∘ ψ.symm) ∘ (ψ ∘ (A.chart j).symm)) := by
    filter_upwards [((A.chart j).isOpen_inter_preimage_symm ψ.open_source).mem_nhds ⟨hy, hx⟩] with u hu
    simp [ψ.left_inv hu.2]
  rw [levi_congr hev, levi_comp w hT hf]
  rfl

theorem exists_pshOff_of_local [CompactSpace X] {Z : Set X} (hZ : IsClosed Z) {r : X → ℝ} {b : LocPot X} {p : X → ℝ}
    (hP : IsPoin A Z r b p) {ι : Type} (Θ : ι → LocPot X) (g : ι → X → ℝ) (ν : ι → ℝ) (hν : ∀ i, 0 ≤ ν i)
    (hΘ : ∀ i, IsPotential A (Θ i)) (hg : ∀ i, A.Smooth (g i))
    (hloc : ∀ x₀, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (N : Set X) (C : ℝ), IsCompatChart A ψ ∧ IsOpen N ∧ x₀ ∈ N ∧
      N ⊆ ψ.source ∧ ∀ i, ∀ x ∈ N, x ∉ Z → ∀ w, -(C * ν i) * levi ((b + LocPot.ofFun p).φ x ∘ ψ.symm) (ψ x) w ≤
        levi ((Θ i + LocPot.ofFun (g i)).φ x ∘ ψ.symm) (ψ x) w) :
    ∃ C : ℝ, ∀ C' : ℝ, C ≤ C' → ∀ i, PshOff A Z (Θ i + LocPot.ofFun (g i) + (b + LocPot.ofFun p).rsmul (C' * ν i)) := by
  choose ψ N C hψ hN hx hs hb using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover N hN fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩
  refine ⟨∑ x ∈ t, |C x|, fun C' hC' i j y hy hyZ w => ?_⟩
  set x := (A.chart j).symm y with hxdef
  obtain ⟨x₀, hx₀, hxN⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  have hCC : C x₀ ≤ C' := ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun x => |C x|) (fun _ _ => abs_nonneg _) hx₀)).trans hC'
  have d1 : ∀ {φ : OpenPartialHomeomorph X (Fin e → ℂ)}, IsCompatChart A φ → x ∈ φ.source →
      ContDiffAt ℝ 2 ((b + LocPot.ofFun p).φ x ∘ φ.symm) (φ x) := fun {φ} hφ h =>
    (contDiffAt_two_compat hφ (b.isOpen_U x) (hP.1.1 x) (φ.map_source h) (by rw [φ.left_inv h]; exact b.mem_U x)).add
      (contDiffAt_two_compat hφ hZ.isOpen_compl hP.2.1 (φ.map_source h) (by rw [φ.left_inv h]; exact hyZ))
  have d2 : ∀ {φ : OpenPartialHomeomorph X (Fin e → ℂ)}, IsCompatChart A φ → x ∈ φ.source →
      ContDiffAt ℝ 2 ((Θ i + LocPot.ofFun (g i)).φ x ∘ φ.symm) (φ x) := fun {φ} hφ h =>
    (contDiffAt_two_compat hφ ((Θ i).isOpen_U x) ((hΘ i).1 x) (φ.map_source h)
      (by rw [φ.left_inv h]; exact (Θ i).mem_U x)).add
      (contDiffAt_two_compat hφ isOpen_univ (hg i) (φ.map_source h) trivial)
  have hxj : x ∈ (A.chart j).source := (A.chart j).map_target hy
  have hjx : A.chart j x = y := (A.chart j).right_inv hy
  have e1 := levi_add_smul (C' * ν i) (hjx ▸ d2 (isCompatChart_chart A j) hxj) (hjx ▸ d1 (isCompatChart_chart A j) hxj) w
  have h0 : 0 ≤ levi ((b + LocPot.ofFun p).φ x ∘ (A.chart j).symm) y w := hP.2.2.2 j y hy hyZ w
  have h1 := hb x₀ i x hxN hyZ (fderiv ℂ (ψ x₀ ∘ (A.chart j).symm) y w)
  rw [← levi_chart_eq (hψ x₀) j hy (hs x₀ hxN) (d1 (hψ x₀) (hs x₀ hxN)),
    ← levi_chart_eq (hψ x₀) j hy (hs x₀ hxN) (d2 (hψ x₀) (hs x₀ hxN))] at h1
  refine le_of_le_of_eq ?_ e1.symm
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC (hν i)) h0
  linarith

variable {m : ℕ} {L : Fin m → LocPot X} {s : Fin m → X → X → ℂ} {D : Fin m → Set X} {K : LocPot X} {c : ℝ}

def poinFun (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (c : ℝ) (y : X) : ℝ :=
  -(c / 2) * ∑ i, Real.log (rComp L s i y) - 1

theorem levi_poinFun (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (z w : Fin e → ℂ) :
    levi ((K + LocPot.ofFun (poinFun L s c)).φ (ψ.symm z) ∘ ψ.symm) z w =
      Real.pi / 2 * formAt ψ (poincarePot K L s c) z w := by
  have e1 : (K + LocPot.ofFun (poinFun L s c)).φ (ψ.symm z) ∘ ψ.symm =
      fun v => ((poincarePot K L s c).φ (ψ.symm z) ∘ ψ.symm) v - 1 := funext fun v => (add_sub_assoc _ _ _).symm
  have hπ := Real.pi_pos
  rw [e1, levi_sub_const, formAt]
  field_simp

theorem isPoin_poinFun (hB : IsBoundary A L s D) (hK : IsPotential A K) (hKp : IsPosPot A K) (hc : 0 < c)
    (hS : ScalarBounds L s D) (hT : TwoSided A K L s D c) {Z : Set X} {r : X → ℝ} (hZ : Z = ⋃ i, D i)
    (hr : ∀ x, x ∉ Z → r x = rTot L s x) (he : ∀ x, x ∉ Z → Real.exp 1 ≤ r x) : IsPoin A Z r K (poinFun L s c) := by
  subst hZ
  have hπ := Real.pi_pos
  refine ⟨hK, fun j y hy => ?_, ⟨min (c / 2) 1, c / 2 * m + 1, lt_min (half_pos hc) one_pos, fun x hx => ?_⟩,
    fun j y hy hyZ w => ?_⟩
  · refine ContDiffAt.contDiffWithinAt ?_
    refine (contDiffAt_const.mul (ContDiffAt.sum fun i _ => ?_)).sub contDiffAt_const
    exact (GlobalTheory.T.boundary_potential_smooth_off_divisor A L s D hB i _ (isCompatChart_chart A j) y hy.1 fun h => hy.2 (Set.mem_iUnion.2 ⟨i, h⟩)).log
      ((Real.exp_pos 1).trans_le ((hS _ hy.2).1 i)).ne'
  · have h1 : 1 ≤ Real.log (r x) := (Real.le_log_iff_exp_le ((Real.exp_pos 1).trans_le (he x hx))).2 (he x hx)
    have hm := min_le_left (c / 2) 1
    have hm' := min_le_right (c / 2) 1
    have hm0 := lt_min (half_pos hc) one_pos
    rw [poinFun]
    rcases Nat.eq_zero_or_pos m with rfl | hm1
    · have : r x = Real.exp 1 := (hr x hx).trans (rTot_zero L s x)
      simp [this]
    · obtain ⟨h2, h3⟩ := (hS x hx).2.2.2 hm1
      rw [← hr x hx] at h2 h3
      constructor <;> nlinarith
  · have h1 := (hT _ (isCompatChart_chart A j) y hy hyZ w).1
    have h2 : 0 ≤ formAt (A.chart j) K y w := by
      refine mul_nonneg (by positivity) ?_
      by_cases hw : w = 0
      · rw [hw, levi_zero]
      · exact (hKp _ j y ⟨hy, K.mem_U _⟩ w hw).le
    have h3 : 0 ≤ c * ∑ i, gradSqAt (A.chart j) (rComp L s i) y w / rComp L s i ((A.chart j).symm y) ^ 2 :=
      mul_nonneg hc.le (Finset.sum_nonneg fun i _ => div_nonneg (gradSqAt_nonneg _ _ _ _) (sq_nonneg _))
    rw [leviAt, levi_poinFun]
    exact mul_nonneg (by positivity) (by linarith)

end Man

section Data

open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation

variable {e m : ℕ}

theorem isPosFrame_mono {n : Type} [Fintype n] [DecidableEq n] {U V : Set (Fin e → ℂ)} {H : (Fin e → ℂ) → Matrix n n ℂ}
    (h : IsPosFrame U H) (hV : IsOpen V) (hVU : V ⊆ U) : IsPosFrame V H :=
  ⟨hV, fun a b => (h.smooth a b).mono hVU, fun z hz => h.posDef z (hVU hz)⟩

theorem IsBlockModel.mono {ι : Type} [Fintype ι] {μ : ι → ℕ} {ρ ρ' : ℝ} {U : Set (Fin e → ℂ)}
    {H : ∀ τ, (Fin e → ℂ) → Matrix (Fin (μ τ)) (Fin (μ τ)) ℂ} (h : IsBlockModel ρ U H) (hρ : ρ' ≤ ρ) :
    IsBlockModel ρ' U H := by
  obtain ⟨n, k, hk, g, rk, τ₀, B, φ, Q, κ, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  have hs := Metric.ball_subset_ball (x := (0 : Fin e → ℂ)) hρ
  exact ⟨n, k, hk, g, rk, τ₀, B, φ, Q, κ, h1, h2.mono hs, h3, fun z hz => h4 z (hs hz), fun τ i l => (h5 τ i l).mono hs,
    h6, h7, h8, fun z hz => h9 z (hs hz)⟩

theorem contDiffOn_modelGram (σ : Fin m → Option (Fin e)) {ρ : ℝ} (hρ : ρ ≤ 1) (k l : Fin e) :
    ContDiffOn ℝ ∞ (fun x => modelGram σ x k l) (punct σ ρ) := by
  classical
  by_cases hkl : k = l
  · subst hkl
    simp only [modelGram, diagonal_apply_eq]
    by_cases h : ∃ i, σ i = some k
    · simp only [if_pos h]
      refine Complex.ofRealCLM.contDiff.comp_contDiffOn ?_
      obtain ⟨i, hi⟩ := h
      intro z hz
      have h0 : z k ≠ 0 := hz.2 i k hi
      have h1 : ‖z k‖ < 1 := ((norm_le_pi_norm z k).trans_lt (mem_ball_zero_iff.1 hz.1)).trans_le hρ
      have hn : ContDiffAt ℝ ∞ (fun x : Fin e → ℂ => ‖x k‖) z := (contDiff_apply ℝ ℂ k).contDiffAt.norm ℂ h0
      have ht : 0 < GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.tOf (z k) := GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog_pos h0 h1
      have hn0 := norm_pos_iff.2 h0
      exact (contDiffAt_const.div ((hn.pow 2).mul (((hn.log hn0.ne').neg.div_const _).pow 2))
        (by positivity)).contDiffWithinAt
    · simp only [if_neg h]
      exact contDiffOn_const
  · simp only [modelGram, diagonal_apply_ne _ hkl]
    exact contDiffOn_const

theorem exists_isData (σ : Fin m → Option (Fin e)) {ι : Type} [Fintype ι] {μ : ι → ℕ} {ρ Cμ CP : ℝ} {U : Set (Fin e → ℂ)}
    {H₀ H : ∀ τ, (Fin e → ℂ) → Matrix (Fin (μ τ)) (Fin (μ τ)) ℂ} {r : (Fin e → ℂ) → ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hU : punct σ ρ ⊆ U) (hH : IsBlockModel ρ U H) (hH₀ : ∀ τ, IsPosFrame (Metric.ball 0 ρ) (H₀ τ))
    (hr : ContDiffOn ℝ ∞ r (punct σ ρ)) (he : ∀ z ∈ punct σ ρ, Real.exp 1 ≤ r z)
    (hc : ∀ τ, PowComparable (punct σ ρ) r Cμ (H₀ τ) (H τ))
    (hg : ∀ z ∈ punct σ ρ, FormLe (fun ξ η => gradForm r z ξ η / ((r z : ℂ) ^ 2)) fun ξ η => CP * formOf (modelGram σ z) ξ η)
    (hl : ∀ z ∈ punct σ ρ, FormAbsLe (ddc (fun x => Real.log (r x)) z) CP (formOf (modelGram σ z))) :
    ∃ ρ' C : ℝ, 0 < ρ' ∧ ρ' ≤ ρ ∧ ∀ τ, IsData Cμ C C C CP (punct σ ρ') (H₀ τ) (H τ) r (modelGram σ) ∧
      IsData Cμ C C C CP (punct σ ρ') (fun z => dualRev (H₀ τ z)) (fun z => dualRev (H τ z)) r (modelGram σ) := by
  obtain ⟨ρ₁, C₁, h₁, h₁', hb⟩ := GlobalTheory.T.block_model_pos_frame_bound e m σ ι μ ρ U H hρ hU hH
  have hs := Metric.ball_subset_ball (x := (0 : Fin e → ℂ)) h₁'
  have h0 := fun τ => isPosFrame_mono (hH₀ τ) Metric.isOpen_ball hs
  have d0 := fun τ => (GlobalTheory.T.one_form_bound_connection_transfer e _ _ _ (h0 τ)).1
  have d1 := fun τ => GlobalTheory.T.one_form_bound_connection_transfer e _ _ _ (hb τ).1
  choose ρ₂ C₂ h₂ h₂' b₂ c₂ using fun τ => GlobalTheory.T.one_form_bound_connection_difference e m _ σ ρ₁ C₁ (H₀ τ) (H τ) h₁ (h0 τ) (hb τ).2.1
  choose ρ₃ C₃ h₃ h₃' b₃ c₃ using fun τ => GlobalTheory.T.one_form_bound_connection_difference e m _ σ ρ₁ C₁ _ _ h₁ (d0 τ) ((d1 τ).2.1 _ _ (hb τ).2.1)
  obtain ⟨ρ', p0, p1, p2, p3⟩ : ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ≤ ρ₁ ∧ (∀ τ, ρ' ≤ ρ₂ τ) ∧ ∀ τ, ρ' ≤ ρ₃ τ := by
    have : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s ∧ s ≤ ρ₁ ∧ (∀ τ, s ≤ ρ₂ τ) ∧ ∀ τ, s ≤ ρ₃ τ := by
      refine eventually_mem_nhdsWithin.and (Eventually.filter_mono nhdsWithin_le_nhds ?_)
      exact (eventually_le_nhds h₁).and ((eventually_all.2 fun τ => eventually_le_nhds (h₂ τ)).and
        (eventually_all.2 fun τ => eventually_le_nhds (h₃ τ)))
    exact this.exists
  obtain ⟨C, q1, q2, q3⟩ : ∃ C : ℝ, C₁ ≤ C ∧ (∀ τ, C₂ τ ≤ C) ∧ ∀ τ, C₃ τ ≤ C :=
    ((eventually_ge_atTop C₁).and ((eventually_all.2 fun τ => eventually_ge_atTop (C₂ τ)).and
      (eventually_all.2 fun τ => eventually_ge_atTop (C₃ τ)))).exists
  have s1 := punct_mono σ p1
  have s0 := punct_mono σ (p1.trans h₁')
  have sb : punct σ ρ' ⊆ Metric.ball 0 ρ₁ := fun z hz => (s1 hz).1
  have ho := isOpen_punct σ ρ'
  have hG := contDiffOn_modelGram σ ((p1.trans h₁').trans hρ1)
  refine ⟨ρ', C, p0, p1.trans h₁', fun τ => ⟨⟨isPosFrame_mono (h0 τ) ho sb, isPosFrame_mono (hb τ).1 ho s1, hr.mono s0,
    fun z hz => he z (s0 hz), hG, fun z _ => modelGram_posSemidef σ z, fun z hz => hc τ z (s0 hz),
    fun z hz => (b₂ τ).mono (q2 τ) z (punct_mono σ (p2 τ) hz), fun z hz => (hb τ).2.2.mono q1 z (s1 hz),
    fun z hz => (c₂ τ).mono (q2 τ) z (punct_mono σ (p2 τ) hz), fun z hz => hg z (s0 hz), fun z hz => hl z (s0 hz)⟩,
    ⟨isPosFrame_mono (d0 τ) ho sb, isPosFrame_mono (d1 τ).1 ho s1, hr.mono s0,
    fun z hz => he z (s0 hz), hG, fun z _ => modelGram_posSemidef σ z, fun z hz => ?_,
    fun z hz => (b₃ τ).mono (q3 τ) z (punct_mono σ (p3 τ) hz), fun z hz => ((d1 τ).2.2.1 _ _ (hb τ).2.2).mono q1 z (s1 hz),
    fun z hz => (c₃ τ).mono (q3 τ) z (punct_mono σ (p3 τ) hz), fun z hz => hg z (s0 hz), fun z hz => hl z (s0 hz)⟩⟩⟩
  have s2 := punct_mono σ h₁'
  exact (d1 τ).2.2.2 (H₀ τ) r Cμ (fun z hz => (h0 τ).posDef z hz.1) (fun z hz => (Real.exp_pos 1).trans_le (he z (s2 hz)))
    (fun z hz => hc τ z (s2 hz)) z (s1 hz)

end Data

section Obj

open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms GlobalTheory.GradedNorm

theorem form_transpose_self {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    form Mᵀ v v = star v ⬝ᵥ M *ᵥ v := by
  rw [form, mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]

theorem hodgeLocal {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (x : ToroidalCompactificationData s)
    (σ : κ.c.F →+* ℂ) : HodgeLocal x σ := by
  by_cases h : Formalism.L2.PjFree.GoodEmb κ.c σ
  · exact GlobalTheory.T.hodge_local_of_good_embedding D A N j S κ s x σ h
  · refine GlobalTheory.T.hodge_local_conj_of_not_good D A N j S κ s x σ h (GlobalTheory.T.hodge_local_of_good_embedding D A N j S κ s x _ ?_)
    have h' : ¬ GoodEmb κ.c σ := h
    have h1 : GoodEmb κ.c ((starRingEnd ℂ).comp σ) := by simpa only [goodOf, if_neg h'] using goodEmb_goodOf κ.c σ
    exact h1

theorem antitone_of_domL {ι : Type} {N j : ℕ} {u : ι → Fin N → ℝ} (hu : DomL j u) (τ : ι) {n : ℕ} (f : Fin n → Fin N) (a : ℕ)
    (hf : ∀ i, (f i : ℕ) = a + i) (hj : ∀ i : Fin n, 0 < (i : ℕ) → a + i ≠ j) : Antitone fun i => u τ (f i) := by
  cases n with
  | zero => exact fun i => i.elim0
  | succ n =>
    refine Fin.antitone_iff_succ_le.2 fun i => hu τ _ _ ?_ ?_
    · rw [hf, hf]; simp [add_assoc]
    · rw [hf]; exact hj _ (by simp)

theorem interp_gram_eq {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (x : ToroidalCompactificationData s)
    {σ : κ.c.F →+* ℂ} (R : ℝ) (y : CxPts (genStr s.T.Z) σ) (g : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)) (τ : D.what₂.Tau)
    (a : ℝ) (hw : x.wt σ R y = a) :
    ((x.eigMetAt σ (some R)).gram y g (DV.tauEmb D τ))ᵀ = ((1 - a : ℝ) : ℂ) • ((x.eigMet σ).gram y g (DV.tauEmb D τ))ᵀ +
      (a : ℂ) • ((x.hodge σ).gram y g (DV.tauEmb D τ))ᵀ ∧
    dualRev ((x.eigMetAt σ (some R)).gram y g (conjEmb (DV.tauEmb D τ)))ᵀ =
      ((1 - a : ℝ) : ℂ) • dualRev ((x.eigMet σ).gram y g (conjEmb (DV.tauEmb D τ)))ᵀ +
        (a : ℂ) • dualRev ((x.hodge σ).gram y g (conjEmb (DV.tauEmb D τ)))ᵀ := by
  subst hw
  constructor
  · rw [ToroidalCompactificationData.eigMetAt, EigMet.interp_gram _ (A.cm τ), mix, transpose_add, transpose_smul, transpose_smul]
  · have e := EigMet.dualGram_interp_gram (hs := x.wt_mem R) (G₀ := x.eigMet σ) (G := x.hodge σ) g
      (GlobalTheory.RootSum.conj_tau_ne τ)
    have e2 : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ), dualRev Mᵀ = (GlobalTheory.LieMet.dualGram M)ᵀ.submatrix Fin.rev Fin.rev :=
      fun M => by rw [dualRev, GlobalTheory.HermFrame.dualGram, GlobalTheory.LieMet.dualGram, ← transpose_nonsing_inv]
    rw [ToroidalCompactificationData.eigMetAt, e2, e, e2, e2, mix, transpose_add, transpose_smul, transpose_smul]
    rfl

end Obj

open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms GlobalTheory.GradedNorm in

theorem curv_interp_lower : Hypotheses2 → HypothesesH → OnObj fun _ O _ T _ _ => ∀ c σ, ∃ (b : ReciprocityTheory.AnForm.M.LocPot ((T.M c).X σ)) (p : (T.M c).X σ → ℝ), IsPoin ((T.M c).A σ) ((T.M c).Z σ) ((T.M c).r σ) b p ∧ ∃ C : ℝ, ∀ C' : ℝ, C ≤ C' → ∀ u (R : ℝ), 2 ≤ R → DomL O.Y.j u → PshOff ((T.M c).A σ) ((T.M c).Z σ) ((T.F c).th u σ + ReciprocityTheory.AnForm.M.LocPot.ofFun ((T.F c).phR R u σ) + (b + ReciprocityTheory.AnForm.M.LocPot.ofFun p).rsmul (C' * ‖u‖)) := by
  intro hP hH D O hO hN A T H h c a
  obtain ⟨x, P, hW⟩ := id hO

  have hπ := GlobalTheory.T.flag_component_projection_smooth D _ _ _ _ _ O.s O.Φ c
  have : Smooth (genStr O.s.T.Z) := SmoothOfRelativeDimension.smooth O.S.Dw.dim _
  have : IsLocallyNoetherian (gen O.s.T.Z : Scheme.{0}) := LocallyOfFiniteType.isLocallyNoetherian (genStr O.s.T.Z)
  have := isProper_genStr O.s.T.Z
  have : CompactSpace (gen O.s.T.Z : Scheme.{0}) := QuasiCompact.compactSpace_of_compactSpace (genStr O.s.T.Z)
  have : IsNoetherian (gen O.s.T.Z : Scheme.{0}) := {}
  obtain ⟨L, s, hB, hn⟩ := GlobalTheory.T.divisor_boundary_potentials_exist _ (O.var c) _ (T.M c) (h.man c) a x.m
    (fun i => (x.cpt i).preimage (O.Φ.C c).π.continuous) (fun i z => x.nrm _ i ((O.Φ.C c).down z)) (O.dim_eq c)
    (fun y => GlobalTheory.T.local_snc_pullback_smooth _ _ _ (genStr O.s.T.Z) _ _ _ y (GlobalTheory.T.snc_components_local_snc _ _ _ _ O.s.T.snc x.cpt_list _))
    (fun i => GlobalTheory.T.divisor_norm_pullback_component D _ _ _ _ _ O.s O.Φ c _ _ _ hπ (x.nrm_div _ i))
  set Dv : Fin x.m → Set ((T.M c).X a) :=
    fun i => {z | under ((h.man c).pt a z) ∈ (x.cpt i).preimage (O.Φ.C c).π.continuous} with hDv
  have hZi : ∀ z, z ∈ (T.M c).Z a ↔ LiesIn ((O.Φ.C c).down ((h.man c).pt a z)) (genBd O.s.T.Z) := (h.an c).Z a
  have hZ : (T.M c).Z a = ⋃ i, Dv i := Set.ext fun z =>
    ((hZi z).trans (x.liesIn_genBd_iff _)).trans (Set.mem_iUnion (s := Dv) (x := z)).symm
  have hrx : ∀ z, rTot L s z = x.r _ ((O.Φ.C c).down ((h.man c).pt a z)) := fun z => by
    simp only [rTot, hn, OddPrimesWithRootsOfUnity.r]
  have hr : ∀ z, z ∉ (T.M c).Z a → (T.M c).r a z = rTot L s z := fun z hz =>
    ((h.an c).r a z hz).trans (by rw [hW.r_eq, hrx]; rfl)
  have hbd := (T.M c).bd a
  letI : MeasurableSpace ((T.M c).X a) := borel _
  haveI : BorelSpace ((T.M c).X a) := ⟨rfl⟩
  obtain ⟨cs, hcs, -, hS, hall, hmod⟩ := GlobalTheory.T.poincare_form_statement _ _ ((T.M c).A a) ((T.M c).Om a) hbd.2.2.1 hbd.2.2.2.1 _ L s Dv hB
  obtain ⟨-, hT, ⟨Cg, hCg, hG⟩, -⟩ := hall cs hcs le_rfl
  have hPo := isPoin_poinFun hB hbd.2.2.1 hbd.2.2.2.1 hcs hS hT hZ hr hbd.2.2.2.2.2.1
  refine ⟨_, _, hPo, ?_⟩
  suffices hs : ∃ C : ℝ, ∀ C' : ℝ, C ≤ C' → ∀ i : {q : (D.what₂.Tau → Fin O.Y.N → ℝ) × ℝ // 2 ≤ q.2 ∧ DomL O.Y.j q.1},
      PshOff ((T.M c).A a) ((T.M c).Z a) ((T.F c).th i.1.1 a + LocPot.ofFun ((T.F c).phR i.1.2 i.1.1 a) +
        ((T.M c).Om a + LocPot.ofFun (poinFun L s cs)).rsmul (C' * ‖i.1.1‖)) from
    hs.imp fun C hC C' hC' u R hR hu => hC C' hC' ⟨(u, R), hR, hu⟩
  refine exists_pshOff_of_local hbd.1 hPo _ _ _ (fun _ => norm_nonneg _) (fun i => T.th_pot c _ a)
    (fun i => ?_) fun x₀ => ?_
  · exact GlobalTheory.InterpChgSmooth.smooth_phR hP hH D O hO hN A T H h c _ a _ i.2.1

  obtain ⟨ψ, σ, hψ, hx₀, h0⟩ := GlobalTheory.T.adapted_polydisc_exists_at _ L s Dv hB x₀
  obtain ⟨ρP, hρP, hρP2, -, hcmp⟩ := hmod ψ σ hψ
  obtain ⟨Cm, hCm, hcmp⟩ := hcmp cs hcs le_rfl
  obtain ⟨ρ₁, t, g, hρ₁, hb₁, hAd, hHol, hcont, hsm⟩ := GlobalTheory.T.toroidal_model_chart_flag _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e (O.Φ.C c) _ (T.M c)
    (h.man c) a ψ hψ.1 (h0 ▸ ψ.map_source hx₀)
  obtain ⟨ρ₂, hρ₂, hb₂, hblk⟩ := hodgeLocal x _ _ _ _ Metric.isOpen_ball (Metric.mem_ball_self hρ₁) hHol hcont
  set ρ := min ρ₂ ρP with hρdef
  have hρ : 0 < ρ := lt_min hρ₂ hρP
  have hρ1 : ρ ≤ 1 := (min_le_right _ _).trans (hρP2.trans (by norm_num))
  have hb : Metric.ball (0 : Fin (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) → ℂ) ρ ⊆ Metric.ball 0 ρ₁ :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans hb₂
  have hpz : ∀ {ρ' : ℝ}, ρ' ≤ 1 → ∀ z ∈ Metric.ball (0 : Fin (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) → ℂ) ρ',
      (ψ.symm z ∉ (T.M c).Z a ↔ z ∈ punct σ ρ') := fun h1 z hz => by
    have := hψ.2.2.2 z (Metric.ball_subset_ball h1 hz)
    simp only [hZ, Set.mem_iUnion, this, punct, Set.mem_setOf_eq, hz, true_and, not_exists, not_and, ne_eq]
  have hpZ : ∀ z ∈ punct σ ρ, ψ.symm z ∉ (T.M c).Z a := fun z hz => (hpz hρ1 z hz.1).2 hz
  have hpt : ∀ z ∈ punct σ ρ, z ∈ ψ.target := fun z hz => hb₁ (hb hz.1)
  have hpD : ∀ z ∈ punct σ ρ, ψ.symm z ∉ ⋃ i, Dv i := fun z hz => hZ ▸ hpZ z hz
  have hfm : ∀ z ∈ punct σ ρ, ∀ w, Cm⁻¹ * modelAt σ z w ≤ formAt ψ (poincarePot ((T.M c).Om a) L s cs) z w ∧
      formAt ψ (poincarePot ((T.M c).Om a) L s cs) z w ≤ Cm * modelAt σ z w := fun z hz =>
    hcmp z (Metric.ball_subset_ball (min_le_right _ _) hz.1) (hpD z hz)
  have hrs : ContDiffOn ℝ ∞ (rTot L s ∘ ψ.symm) (punct σ ρ) :=
    ((ReciprocityTheory.AnForm.M.PLAux.contDiffOn_compat hψ.1 hbd.1.isOpen_compl hbd.2.2.2.2.1).mono
      fun z hz => ⟨hpt z hz, hpZ z hz⟩).congr fun z hz => (hr _ (hpZ z hz)).symm
  have hre : ∀ z ∈ punct σ ρ, Real.exp 1 ≤ (rTot L s ∘ ψ.symm) z := fun z _ => by
    rw [Function.comp_apply, hrx]; exact x.exp_le_r _ _
  have hr2 : ∀ z ∈ punct σ ρ, ContDiffAt ℝ 2 (rTot L s ∘ ψ.symm) z := fun z hz =>
    (hrs.contDiffAt ((isOpen_punct σ ρ).mem_nhds hz)).of_le (WithTop.coe_le_coe.2 le_top)
  obtain ⟨-, hmu⟩ := x.isMuExp_muExp (ToroidalCompactificationData.exists_isMuExp x)
  obtain ⟨ρ', C, hρ', hρ'ρ, hdat⟩ := exists_isData σ (Cμ := x.muExp) (CP := Cg * Cm / 2)
    (H₀ := fun τ z => ((x.eigMet _).gram ((O.Φ.C c).down ((h.man c).pt a (ψ.symm z))) (g z) τ)ᵀ) hρ hρ1
    (fun z hz => (hZi _).not.1 (hpZ z hz)) (hblk.mono (min_le_left _ _))
    (fun τ => isPosFrame_mono (hsm _ (x.smoothOn_eigMet _) τ) Metric.isOpen_ball hb) hrs hre
    (fun τ z hz v => by
      simp only [form_transpose_self, Function.comp_apply, hrx]
      exact hmu _ _ ((hZi _).not.1 (hpZ z hz)) (g z) τ v)
    (fun z hz ξ => by
      have h1 := (hG ψ hψ.1 z (hpt z hz) (hpD z hz) ξ).1
      have h2 := mul_le_mul_of_nonneg_left (hfm z hz ξ).2 hCg.le
      rw [diagVal_gradForm ((hr2 z hz).differentiableAt two_ne_zero)]
      have e : diagVal (fun ξ η => ((Cg * Cm / 2 : ℝ) : ℂ) * formOf (modelGram σ z) ξ η) ξ = Cg * Cm / 2 * modelAt σ z ξ := by
        rw [← form_modelGram, ← diagVal_formOf, diagVal, diagVal, mul_left_comm, Complex.re_ofReal_mul]
      rw [e]
      simp only [gradSqAt] at h1
      simp only [Function.comp_apply]
      linarith)
    (fun z hz => formAbsLe_iff.2 fun ξ => by
      have h1 := (hG ψ hψ.1 z (hpt z hz) (hpD z hz) ξ).2.1
      have h2 := mul_le_mul_of_nonneg_left (hfm z hz ξ).2 hCg.le
      rw [diagVal_ddc ((hr2 z hz).log ((Real.exp_pos 1).trans_le (hre z hz)).ne'), diagVal_formOf, form_modelGram]
      have e : levi (fun v => Real.log ((rTot L s ∘ ψ.symm) v)) z ξ / (2 * Real.pi) =
          ddcAt ψ (fun y => Real.log (rTot L s y)) z ξ / 2 := by
        rw [ddcAt]; field_simp; rfl
      rw [e, abs_div, abs_two]
      linarith)
  obtain ⟨C₁, hC₁, hlow⟩ := levi_lower_of_data (T := D.what₂.Tau) (isOpen_punct σ ρ') x.lt_kap isCutoff_sq
    (fun τ => (hdat (DV.tauEmb D τ)).1) fun τ => (hdat (conjEmb (DV.tauEmb D τ))).2
  have hmul : ∀ τ, O.S.Dw.mult (DV.tauEmb D τ) + O.S.Dw.mult (conjEmb (DV.tauEmb D τ)) = O.N := fun τ =>
    (GlobalTheory.Proof.LetterConjugation.mult_add O.S.Dw _).trans O.S.rank_eq
  have hmj : ∀ τ, O.S.Dw.mult (DV.tauEmb D τ) = O.j := fun τ => (GlobalTheory.RootSum.mult_tau O.S τ).trans O.S.p_eq
  refine ⟨ψ, ψ.source ∩ ψ ⁻¹' Metric.ball 0 ρ', C₁ * (Fintype.card D.what₂.Tau * O.N) * Cm * (2 / Real.pi), hψ.1,
    ψ.isOpen_inter_preimage Metric.isOpen_ball, ⟨hx₀, by simpa [h0] using hρ'⟩, Set.inter_subset_left, ?_⟩
  rintro ⟨⟨u, R⟩, hR, hu⟩ y ⟨hys, hyb⟩ hyZ w
  dsimp only at hR hu ⊢
  obtain ⟨z, rfl, hz⟩ : ∃ z, y = ψ.symm z ∧ z ∈ punct σ ρ' :=
    ⟨ψ y, (ψ.left_inv hys).symm, (hpz (hρ'ρ.trans hρ1) _ hyb).1 (by rwa [ψ.left_inv hys])⟩
  have hs := punct_mono σ hρ'ρ
  rw [ψ.right_inv (hpt z (hs hz))]
  let lam : ∀ τ : D.what₂.Tau, Fin (O.S.Dw.mult (DV.tauEmb D τ) + O.S.Dw.mult (conjEmb (DV.tauEmb D τ))) → ℝ :=
    fun τ i => u τ (Fin.cast (hmul τ) i)
  have hlam : ∀ τ (i : Fin (O.S.Dw.mult (DV.tauEmb D τ) + O.S.Dw.mult (conjEmb (DV.tauEmb D τ)))) (i' : Fin O.N),
      (i : ℕ) = i' → lam τ i = u τ i' := fun τ i i' e => congrArg (u τ) (Fin.ext e)
  have key := hlow R hR lam
    (fun τ => antitone_of_domL hu τ (fun i => Fin.cast (hmul τ) (Fin.castAdd _ i)) 0 (fun i => (Nat.zero_add _).symm)
      fun i _ => by have := i.2; have := hmj τ; change 0 + (i : ℕ) ≠ O.j; omega)
    (fun τ => antitone_of_domL hu τ (fun i => Fin.cast (hmul τ) (Fin.natAdd _ i)) O.j (fun i => congrArg (· + (i : ℕ)) (hmj τ))
      fun i hi => by change O.j + (i : ℕ) ≠ O.j; omega) z hz w
  have hroot := fun v (hv : v ∈ punct σ ρ') => GlobalTheory.T.root_generators_generate_adapted D O c _ (x.eigMetAt _ (some R)) _ t (g v) (hAd v (hb (hs hv).1))
  rw [GlobalTheory.T.divisor_generates_chart_estimate hP hH D O hO hN A T H h c a ψ hψ.1 z (hpt z (hs hz)) R hR u (rootGen O c t) (hroot z hz).1 w,
    levi_poinFun]
  refine le_trans ?_ (key.trans_eq (levi_congr ?_ w))
  · have h1 : ∑ τ, ∑ i, |lam τ i| ≤ Fintype.card D.what₂.Tau * O.N * ‖u‖ := by
      have : ∀ τ, ∑ i, |lam τ i| ≤ O.N * ‖u‖ := fun τ => by
        refine (Finset.sum_le_card_nsmul _ _ ‖u‖ fun i _ => ?_).trans (by simp [hmul τ])
        exact (norm_le_pi_norm (u τ) _).trans (norm_le_pi_norm u τ)
      refine (Finset.sum_le_card_nsmul _ _ _ fun τ _ => this τ).trans_eq ?_
      simp [mul_assoc]
    rw [form_modelGram]
    have h2 := (hfm z (hs hz) w).1
    rw [inv_mul_le_iff₀ hCm] at h2
    have h3 : 0 ≤ modelAt σ z w := by
      rw [← form_modelGram, ← gnorm_sq (modelGram_posSemidef σ z)]; positivity
    have h4 := mul_le_mul (mul_le_mul_of_nonneg_left h1 hC₁) h2 h3 (by positivity)
    have hπ := Real.pi_pos
    rw [neg_mul, neg_mul, neg_le_neg_iff]
    refine h4.trans_eq ?_
    field_simp
  · filter_upwards [(isOpen_punct σ ρ').mem_nhds hz] with v hv
    have hvZ := (hZi _).not.1 (hpZ v (hs hv))
    have hw : x.wt _ R ((O.Φ.C c).down ((h.man c).pt a (ψ.symm v))) =
        1 * cutWeight (fun y => Real.smoothTransition (3 - y) ^ 2) x.kap R (rTot L s ∘ ψ.symm) v := by
      rw [x.wt_eq hR hvZ, one_mul, ← hrx]; rfl
    rw [hW.hm_eq]
    exact ((hroot v hv).2 u lam hlam _ _ _ v (fun τ => (interp_gram_eq x R _ (g v) τ _ hw).1.symm)
      fun τ => (interp_gram_eq x R _ (g v) τ _ hw).2.symm).symm

end GlobalTheory.CurvInterp
