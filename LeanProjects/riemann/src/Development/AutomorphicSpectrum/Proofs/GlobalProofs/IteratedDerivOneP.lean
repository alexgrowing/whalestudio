import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IoInjective
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SkewOfCommute
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivativeSkewAdjointCuspFormsStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieAlgebraSpannedByCompactAndFrameStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteCoefficientSpaceAnnihilatingPolynomialStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SkewOperatorBoundedByPolynomialRootsStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CuspTranslateBoundedByDerivativeStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanNeighbourhoodExpSurjectiveStatement
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct Topology InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

namespace GlobalTheory.CompanionTheory.HCCusp

open GlobalTheory.Cusp GlobalTheory.Mem.AutSpace GlobalTheory.Published.AutFin GlobalTheory.SmoothForms

variable {D : D7} {θ : GlobalTheory.Mem.Th.InfF D} {V : HSp D}

theorem smooth_of_mem (φ : Mc θ V) : φ.1 ∈ SmFun θ V := (mem_Mc_iff.1 φ.2).1.smooth

theorem der_congr (hθ : IsInfFam θ) {τ : D.what₂.Tau} {X Y : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (hY : Y ∈ lieAt V τ) (h : X = Y) : der hθ τ hX = der hθ τ hY := by
  subst h; rfl

theorem der_comb (hθ : IsInfFam θ) {τ : D.what₂.Tau} {X Y : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (hY : Y ∈ lieAt V τ) (r s : ℝ) (h : r • X + s • Y ∈ lieAt V τ) :
    der hθ τ h = (r : ℂ) • der hθ τ hX + (s : ℂ) • der hθ τ hY :=
  LinearMap.ext fun φ => Subtype.ext (GlobalTheory.Mem.RealTranslate.Rder_comb hθ (smooth_of_mem φ) hX hY r s)

def Bd (μ : Measure (GA D V)) [μ.IsHaarMeasure] (hθ : IsInfFam θ) (E : Set (Mc θ V))
    (T : Module.End ℂ (Mc θ V)) : Prop :=
  ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ φ ∈ E, ‖io μ hθ (T φ)‖ ≤ Λ * ‖io μ hθ φ‖

section Bd

variable {μ : Measure (GA D V)} [μ.IsHaarMeasure] {hθ : IsInfFam θ} {E : Set (Mc θ V)}

theorem Bd.add {S T : Module.End ℂ (Mc θ V)} (hS : Bd μ hθ E S) (hT : Bd μ hθ E T) : Bd μ hθ E (S + T) := by
  obtain ⟨a, ha, h⟩ := hS
  obtain ⟨b, hb, k⟩ := hT
  refine ⟨a + b, add_nonneg ha hb, fun φ hφ => ?_⟩
  rw [LinearMap.add_apply, map_add, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (h φ hφ) (k φ hφ))

theorem Bd.smul {T : Module.End ℂ (Mc θ V)} (c : ℂ) (hT : Bd μ hθ E T) : Bd μ hθ E (c • T) := by
  obtain ⟨a, ha, h⟩ := hT
  refine ⟨‖c‖ * a, mul_nonneg (norm_nonneg _) ha, fun φ hφ => ?_⟩
  rw [LinearMap.smul_apply, map_smul, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h φ hφ) (norm_nonneg _)

theorem Bd.sum {ι : Type} (s : Finset ι) {T : ι → Module.End ℂ (Mc θ V)} (hT : ∀ i ∈ s, Bd μ hθ E (T i)) :
    Bd μ hθ E (∑ i ∈ s, T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, le_rfl, fun φ _ => by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hT a (Finset.mem_insert_self _ _)).add (ih fun i hi => hT i (Finset.mem_insert_of_mem hi))

end Bd

theorem inner_der_der (μ : Measure (GA D V)) [μ.IsHaarMeasure] (hθ : IsInfFam θ) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (φ : Mc θ V) :
    ⟪io μ hθ φ, io μ hθ (der hθ τ hX (der hθ τ hX φ))⟫_ℂ = -((‖io μ hθ (der hθ τ hX φ)‖ ^ 2 : ℝ) : ℂ) := by
  have h := GlobalTheory.T.derivative_skew_adjoint_cusp_forms D θ hθ V μ τ X hX φ (der hθ τ hX φ)
  have h' : ⟪io μ hθ φ, io μ hθ (der hθ τ hX (der hθ τ hX φ))⟫_ℂ =
      -⟪io μ hθ (der hθ τ hX φ), io μ hθ (der hθ τ hX φ)⟫_ℂ := by rw [h, neg_neg]
  rw [h', inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

theorem bd_of_casimir (μ : Measure (GA D V)) [μ.IsHaarMeasure] (hθ : IsInfFam θ) {τ : D.what₂.Tau}
    (E : Set (Mc θ V)) {n₁ n₂ : ℕ} {X : Fin n₁ → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {Y : Fin n₂ → Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : ∀ a, X a ∈ lieAt V τ) (hY : ∀ b, Y b ∈ lieAt V τ)
    (c : ℂ) (hE : ∀ φ ∈ E, c • φ = ∑ a, der hθ τ (hX a) (der hθ τ (hX a) φ) -
      ∑ b, der hθ τ (hY b) (der hθ τ (hY b) φ))
    (hK : ∀ b, Bd μ hθ E (der hθ τ (hY b))) (a : Fin n₁) : Bd μ hθ E (der hθ τ (hX a)) := by
  choose κ hκ0 hκ using hK
  set B : ℝ := ‖c‖ + ∑ b, κ b ^ 2 with hB
  have hB0 : 0 ≤ B := add_nonneg (norm_nonneg _) (Finset.sum_nonneg fun b _ => sq_nonneg _)
  refine ⟨Real.sqrt B, Real.sqrt_nonneg _, fun φ hφ => ?_⟩
  have h2 := congrArg (fun w => ⟪io μ hθ φ, io μ hθ w⟫_ℂ) (hE φ hφ)
  simp only [map_smul, map_sub, map_sum, inner_smul_right, inner_sub_right, inner_sum, inner_der_der,
    inner_self_eq_norm_sq_to_K] at h2
  have e : ((‖io μ hθ φ‖ : ℂ) ^ 2) = ((‖io μ hθ φ‖ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [show ((RCLike.ofReal ‖io μ hθ φ‖ : ℂ) ^ 2) = ((‖io μ hθ φ‖ ^ 2 : ℝ) : ℂ) from e] at h2
  have h3 := congrArg Complex.re h2
  simp only [Complex.sub_re, Complex.re_sum, Complex.neg_re, Complex.ofReal_re, Complex.re_mul_ofReal,
    Finset.sum_neg_distrib, sub_neg_eq_add, Complex.add_re] at h3
  have h4 : ‖io μ hθ (der hθ τ (hX a) φ)‖ ^ 2 ≤ ∑ x, ‖io μ hθ (der hθ τ (hX x) φ)‖ ^ 2 :=
    Finset.single_le_sum (f := fun x => ‖io μ hθ (der hθ τ (hX x) φ)‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ a)
  have h5 : ∑ b, ‖io μ hθ (der hθ τ (hY b) φ)‖ ^ 2 ≤ (∑ b, κ b ^ 2) * ‖io μ hθ φ‖ ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hκ b φ hφ) 2
  have h6 : -(c.re * ‖io μ hθ φ‖ ^ 2) ≤ ‖c‖ * ‖io μ hθ φ‖ ^ 2 := by
    rw [← neg_mul]
    exact mul_le_mul_of_nonneg_right ((neg_le_abs _).trans (Complex.abs_re_le_norm c)) (sq_nonneg _)
  have h7 : ‖io μ hθ (der hθ τ (hX a) φ)‖ ^ 2 ≤ B * ‖io μ hθ φ‖ ^ 2 := by
    rw [hB, add_mul]
    linarith
  have h8 := Real.sqrt_le_sqrt h7
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hB0, Real.sqrt_sq (norm_nonneg _)] at h8

theorem bd_span (μ : Measure (GA D V)) [μ.IsHaarMeasure] (hθ : IsInfFam θ) {τ : D.what₂.Tau}
    (E : Set (Mc θ V)) (S : Set (Matrix (Fin V.rank) (Fin V.rank) ℂ))
    (hS : ∀ Z ∈ S, ∃ h : Z ∈ lieAt V τ, Bd μ hθ E (der hθ τ h))
    {Z : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hZ : Z ∈ Submodule.span ℝ S) :
    ∃ h : Z ∈ lieAt V τ, Bd μ hθ E (der hθ τ h) := by
  have h0 : (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ lieAt V τ :=
    (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU (gramAt D V τ)).zero_mem
  induction hZ using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero =>
    refine ⟨h0, ?_⟩
    have e : der hθ τ h0 = 0 := by
      have h00 : (0 : ℝ) • (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ) + (0 : ℝ) • 0 ∈ lieAt V τ := by
        simpa using h0
      rw [der_congr hθ h0 h00 (by simp), der_comb hθ h0 h0 0 0 h00]
      simp
    rw [e]
    exact ⟨0, le_rfl, fun φ _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨h1, b1⟩ := hx
    obtain ⟨h2, b2⟩ := hy
    have h12 : x + y ∈ lieAt V τ := (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU (gramAt D V τ)).add_mem h1 h2
    have h12' : (1 : ℝ) • x + (1 : ℝ) • y ∈ lieAt V τ := by simpa using h12
    refine ⟨h12, ?_⟩
    rw [der_congr hθ h12 h12' (by simp), der_comb hθ h1 h2 1 1 h12']
    exact (b1.smul _).add (b2.smul _)
  | smul r x _ hx =>
    obtain ⟨h1, b1⟩ := hx
    have h12 : r • x ∈ lieAt V τ := (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU (gramAt D V τ)).smul_mem r h1
    have h12' : r • x + (0 : ℝ) • x ∈ lieAt V τ := by simpa using h12
    refine ⟨h12, ?_⟩
    rw [der_congr hθ h12 h12' (by simp), der_comb hθ h1 h1 r 0 h12']
    simpa using b1.smul (r : ℂ)

theorem iteratedDeriv_oneP (hθ : IsInfFam θ) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (j : ℕ) (φ : Mc θ V) (x : GA D V) :
    iteratedDeriv j (fun t : ℝ => φ.1 (x * oneP θ V τ X t)) =
      fun t => ((der hθ τ hX ^ j) φ).1 (x * oneP θ V τ X t) := by
  induction j generalizing φ with
  | zero => simp
  | succ j ih =>
    have e : deriv (fun t : ℝ => φ.1 (x * oneP θ V τ X t)) =
        fun t => (der hθ τ hX φ).1 (x * oneP θ V τ X t) := funext fun t =>
      (GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (GlobalTheory.Mem.Lift.hasDerivAt_Rder (smooth_of_mem φ) hX) x t).deriv
    rw [iteratedDeriv_succ', e, ih (der hθ τ hX φ), pow_succ]
    rfl

theorem exists_oneParam {n : ℕ} {e : Fin n → Bool} {y : Matrix (Fin n) (Fin n) ℂ} (hy : IsKLie e y) :
    ∃ s : ℝ → Formalism.REAL.KG e, Continuous s ∧ s 0 = 1 ∧ (∀ a b, s (a + b) = s a * s b) ∧
      ∀ t, Formalism.REAL.toMK (s t) = NormedSpace.exp (t • y) := by
  have hin : y ∈ GlobalTheory.SmoothGlob.lieSet e := by
    change yᴴ * Formalism.REAL.Jm e + Formalism.REAL.Jm e * y = 0
    rw [hy.1, Matrix.neg_mul, hy.2, neg_add_cancel]
  have hm : ∀ t : ℝ, Formalism.REAL.toM (Formalism.REAL.expG e y t) = NormedSpace.exp (t • y) := fun t => by
    rw [Formalism.REAL.toM_expG e y t hin, Complex.coe_smul]
  let s : ℝ → Formalism.REAL.KG e := fun t => ⟨Formalism.REAL.expG e y t, by
    rw [Formalism.REAL.mem_KG, hm]
    exact GlobalTheory.CompanionTheory.Hypotheses₂.KStable.exp_mem_Kset hin hy.2 t⟩
  have hs : ∀ t, Formalism.REAL.toMK (s t) = NormedSpace.exp (t • y) := hm
  have hemb : Topology.IsEmbedding (fun k : Formalism.REAL.KG e => Formalism.REAL.toMK k) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n e).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  refine ⟨s, hemb.continuous_iff.2 ?_, hemb.injective ?_, fun a b => hemb.injective ?_, hs⟩
  · change Continuous fun t => Formalism.REAL.toMK (s t)
    simp only [hs]
    open scoped Matrix.Norms.Operator in
    exact continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp_smul_const (𝕂 := ℝ) y t).continuousAt
  · change Formalism.REAL.toMK (s 0) = 1
    rw [hs, zero_smul, NormedSpace.exp_zero]
  · change Formalism.REAL.toMK (s (a + b)) = Formalism.REAL.toMK (s a) * Formalism.REAL.toMK (s b)
    rw [hs, hs, hs, add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl y).smul_left a).smul_right b)]

theorem kAt_eq_oneP (θ : GlobalTheory.Mem.Th.InfF D) {τ : D.what₂.Tau} {e : Fin V.rank → Bool}
    {P y : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hP : IsUnit P) {k : Formalism.REAL.KG e} {t : ℝ}
    (h : Formalism.REAL.toMK k = NormedSpace.exp (t • y)) :
    kAt θ V τ e P k = oneP θ V τ (P⁻¹ * y * P) t := by
  have hu : IsUnit P⁻¹ := by
    rw [Matrix.isUnit_nonsing_inv_iff]; exact hP
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have e1 : t • (P⁻¹ * y * P) = P⁻¹ * (t • y) * (P⁻¹)⁻¹ := by
    rw [Matrix.nonsing_inv_nonsing_inv _ hd]; simp
  rw [kAt, oneP, h, e1, Matrix.exp_conj _ _ hu, Matrix.nonsing_inv_nonsing_inv _ hd]

theorem bd_ktype (μ : Measure (GA D V)) [μ.IsHaarMeasure] (hθ : IsInfFam θ) {τ : D.what₂.Tau}
    {e : Fin V.rank → Bool} {P y : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hP : IsUnit P)
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (Formalism.REAL.KG e) W) (hρ : IsContRep ρ) (hy : IsKLie e y)
    (hY : P⁻¹ * y * P ∈ lieAt V τ) :
    Bd μ hθ {φ | HasTypeAt θ V τ e P ρ φ.1} (der hθ τ hY) := by
  classical
  obtain ⟨s, hc, h0, ha, hs⟩ := exists_oneParam hy
  obtain ⟨m, hm0, hm⟩ := GlobalTheory.T.finite_coefficient_space_annihilating_polynomial (Formalism.REAL.KG e) W ρ hρ s hc h0 ha
  have hκ0 : 0 ≤ ∑ r ∈ m.roots.toFinset, ‖r‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨_, hκ0, fun φ hφ => GlobalTheory.T.skew_operator_bounded_by_polynomial_roots _ _ (io μ hθ) (io_injective μ hθ) (der hθ τ hY)
    (fun a b => GlobalTheory.T.derivative_skew_adjoint_cusp_forms D θ hθ V μ τ _ hY a b) m hm0 _ hκ0
    (fun r hr => Finset.single_le_sum (f := fun r : ℂ => ‖r‖) (fun _ _ => norm_nonneg _)
      (Multiset.mem_toFinset.2 hr)) φ ?_⟩
  refine Subtype.ext (funext fun x => ?_)
  have h1 := hm _ (hφ x) 1
  rw [Polynomial.aeval_eq_sum_range]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Submodule.coe_sum, Finset.sum_apply]
  refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h1
  have e2 : (fun t : ℝ => φ.1 (x * kAt θ V τ e P (1 * s t))) = fun t => φ.1 (x * oneP θ V τ (P⁻¹ * y * P) t) :=
    funext fun t => by rw [one_mul, kAt_eq_oneP θ hP (hs t)]
  rw [e2, iteratedDeriv_oneP hθ hY j φ x]
  have : oneP θ V τ (P⁻¹ * y * P) 0 = 1 := GlobalTheory.Mem.Lift.oneP_zero hθ
  simp [this]

theorem Bd.mono {μ : Measure (GA D V)} [μ.IsHaarMeasure] {hθ : IsInfFam θ} {E E' : Set (Mc θ V)}
    {T : Module.End ℂ (Mc θ V)} (hT : Bd μ hθ E' T) (h : E ⊆ E') : Bd μ hθ E T :=
  let ⟨a, ha, k⟩ := hT
  ⟨a, ha, fun φ hφ => k φ (h hφ)⟩

theorem derInf_add (hθ : IsInfFam θ) (X Y : LieN V) : derInf hθ (X + Y) = derInf hθ X + derInf hθ Y := by
  rw [derInf, derInf, derInf, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h12 : (1 : ℝ) • (X τ).1 + (1 : ℝ) • (Y τ).1 ∈ lieAt V τ := by
    simp only [one_smul]
    exact (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU (gramAt D V τ)).add_mem (X τ).2 (Y τ).2
  rw [der_congr hθ ((X + Y) τ).2 h12 (by simp only [one_smul]; rfl), der_comb hθ (X τ).2 (Y τ).2 1 1 h12]
  simp

theorem derInf_smul (hθ : IsInfFam θ) (r : ℝ) (X : LieN V) : derInf hθ (r • X) = (r : ℂ) • derInf hθ X := by
  rw [derInf, derInf, Finset.smul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h12 : r • (X τ).1 + (0 : ℝ) • (X τ).1 ∈ lieAt V τ := by
    simp only [zero_smul, add_zero]
    exact (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU (gramAt D V τ)).smul_mem r (X τ).2
  rw [der_congr hθ ((r • X) τ).2 h12 (by simp only [zero_smul, add_zero]; rfl), der_comb hθ (X τ).2 (X τ).2 r 0 h12]
  simp

theorem derInf_sum (hθ : IsInfFam θ) {ι : Type} (s : Finset ι) (a : ι → ℝ) (b : ι → LieN V) :
    derInf hθ (∑ i ∈ s, a i • b i) = ∑ i ∈ s, (a i : ℂ) • derInf hθ (b i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := derInf_smul hθ 0 (0 : LieN V)
    simpa using this
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, derInf_add, derInf_smul, ih]

theorem bd_inf (μ : Measure (GA D V)) [μ.IsHaarMeasure] (hθ : IsInfFam θ) (E : Set (Mc θ V))
    (h : ∀ (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hZ : Z ∈ lieAt V τ),
      Bd μ hθ E (der hθ τ hZ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : LieN V, ∀ φ ∈ E, ‖io μ hθ (derInf hθ X φ)‖ ≤ C * ‖X‖ * ‖io μ hθ φ‖ := by
  haveI : FiniteDimensional ℝ (LieN V) :=
    inferInstanceAs (FiniteDimensional ℝ (∀ τ : D.what₂.Tau, (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU (gramAt D V τ)).toSubmodule))
  let b := Module.finBasis ℝ (LieN V)
  have hb : ∀ i, Bd μ hθ E (derInf hθ (b i)) := fun i => Bd.sum _ fun τ _ => h τ _ _
  choose Λ hΛ0 hΛ using hb
  let f := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  refine ⟨∑ i, ‖f i‖ * Λ i, Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (hΛ0 i), fun X φ hφ => ?_⟩
  have e : derInf hθ X = ∑ i, ((f i X : ℝ) : ℂ) • derInf hθ (b i) := by
    conv_lhs => rw [← b.sum_repr X]
    rw [derInf_sum]
    rfl
  rw [e, LinearMap.sum_apply, map_sum, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [LinearMap.smul_apply, map_smul, norm_smul, Complex.norm_real]
  calc ‖f i X‖ * ‖io μ hθ (derInf hθ (b i) φ)‖ ≤ (‖f i‖ * ‖X‖) * (Λ i * ‖io μ hθ φ‖) :=
        mul_le_mul ((f i).le_opNorm X) (hΛ i φ hφ) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem Rcusp_io_of_fixed (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (hθ : IsInfFam θ)
    (φ : Mc θ V) (k : GA D V) (hk : ∀ g, φ.1 (g * k) = φ.1 g) : Rcusp V μ k (io μ hθ φ) = io μ hθ φ := by
  have hL : ∀ {f g : GA D V → ℂ} (hf : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GQ V) μ f) (hg : GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GQ V) μ g), f = g →
      hf.toL2 = hg.toL2 := by
    rintro f g hf hg rfl
    rfl
  have h := memL2_of_cusp_form (μ := μ) (GlobalTheory.Grow.cuspRapidDecay_of_bound GlobalTheory.CuspGeo.cuspDecayBound) hθ
    (mem_cuspForms.1 φ.2).1
  refine Subtype.ext ?_
  exact (GlobalTheory.AutomorphicL2Unitary.right_translate_toL2 h k).trans (hL _ h (funext hk))

theorem half_le_re_inner {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {u v : H} (h1 : ‖v‖ = ‖u‖)
    (h2 : ‖v - u‖ ≤ ‖u‖) : (1 / 2 : ℝ) * ‖u‖ ^ 2 ≤ (⟪u, v⟫_ℂ).re := by
  have e := norm_sub_sq (𝕜 := ℂ) v u
  have e2 : RCLike.re ⟪v, u⟫_ℂ = (⟪u, v⟫_ℂ).re := inner_re_symm (𝕜 := ℂ) v u
  rw [e2, h1] at e
  have := pow_le_pow_left₀ (norm_nonneg _) h2 2
  nlinarith

theorem lie_conj {τ : D.what₂.Tau} {e : Fin V.rank → Bool} {P y : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hP : IsUnit P)
    (hfr : Pᴴ * Formalism.REAL.Jm e * P = gramAt D V τ) (hy : IsKLie e y) : P⁻¹ * y * P ∈ lieAt V τ := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have h1 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, mul_nonsing_inv _ hd, conjTranspose_one]
  have h0 : yᴴ * Formalism.REAL.Jm e + Formalism.REAL.Jm e * y = 0 := by
    rw [hy.1, Matrix.neg_mul, hy.2, neg_add_cancel]
  change (P⁻¹ * y * P)ᴴ * gramAt D V τ + gramAt D V τ * (P⁻¹ * y * P) = 0
  calc _ = Pᴴ * (yᴴ * ((P⁻¹)ᴴ * Pᴴ) * Formalism.REAL.Jm e + Formalism.REAL.Jm e * (P * P⁻¹) * y) * P := by
        rw [← hfr]; simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.add_mul, Matrix.mul_add]
    _ = 0 := by rw [h1, mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.mul_one, h0, Matrix.mul_zero, Matrix.zero_mul]

theorem Rcusp_mul_apply (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (a b : GA D V)
    (u : L2cusp V μ) : Rcusp V μ (a * b) u = Rcusp V μ a (Rcusp V μ b u) :=
  congrArg (fun T : L2cusp V μ →L[ℂ] L2cusp V μ => T u) ((Rcusp V μ).map_mul a b)

theorem half_of_bound (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (hθ : IsInfFam θ) (φ : Mc θ V)
    (X : LieN V) (k : GA D V) (hk : ∀ g, φ.1 (g * k) = φ.1 g)
    (hb : ‖io μ hθ (derInf hθ X φ)‖ ≤ ‖io μ hθ φ‖) :
    (1 / 2 : ℝ) * ‖io μ hθ φ‖ ^ 2 ≤ (⟪io μ hθ φ, Rcusp V μ (expInf θ V X * k) (io μ hθ φ)⟫_ℂ).re := by
  have e : Rcusp V μ (expInf θ V X * k) (io μ hθ φ) = Rcusp V μ (expInf θ V X) (io μ hθ φ) :=
    (Rcusp_mul_apply μ _ _ _).trans (congrArg _ (Rcusp_io_of_fixed μ hθ φ k hk))
  rw [e]
  exact half_le_re_inner ((GlobalTheory.Cusp.isUnitaryRep_Rcusp V μ).1 _ _) ((GlobalTheory.T.cusp_translate_bounded_by_derivative D θ hθ V μ X φ).trans hb)

theorem finite_of_bound (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (hθ : IsInfFam θ)
    (U : Subgroup (GA D V)) (hU : IsOpen (U : Set (GA D V))) (E : Submodule ℂ (Mc θ V))
    (hfix : ∀ φ ∈ E, ∀ k ∈ U, k ∈ GfC V → ∀ g, φ.1 (g * k) = φ.1 g) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ X : LieN V, ∀ φ ∈ E, ‖io μ hθ (derInf hθ X φ)‖ ≤ C * ‖X‖ * ‖io μ hθ φ‖) :
    FiniteDimensional ℂ E := by
  have hδ : (0 : ℝ) < 1 / (C + 1) := by positivity
  obtain ⟨N, hN, hlog⟩ := GlobalTheory.T.archimedean_neighbourhood_exp_surjective D θ hθ V _ hδ
  have hM := GlobalTheory.CompanionTheory.CuspNbhd.real_mul_level_mem_nhds D V U hU N hN
  have hfd : FiniteDimensional ℂ (E.map (io μ hθ)) := by
    refine GlobalTheory.CompanionTheory.CuspFin.finiteDimensional_of_coercive GlobalTheory.CuspGeo.cuspDecayBound μ _ hM ?_
    intro g hg u hu
    obtain ⟨r, k, hr, hrN, hk, hkf, hgr⟩ := hg
    obtain ⟨φ, hφ, hφu⟩ := hu
    obtain ⟨X, hX, hXr⟩ := hlog r hrN hr
    rw [hgr, ← hXr, ← hφu]
    refine half_of_bound μ hθ φ X k (hfix φ hφ k hk hkf) ((hC X φ hφ).trans ?_)
    have h1 : C * ‖X‖ ≤ 1 := by
      have h2 : ‖X‖ * (C + 1) ≤ 1 := by
        have := mul_lt_mul_of_pos_right hX (show 0 < C + 1 by positivity)
        rw [one_div, inv_mul_cancel₀ (by positivity)] at this
        exact this.le
      nlinarith [norm_nonneg X]
    exact (mul_le_of_le_one_left (norm_nonneg _) h1)
  exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective (io μ hθ) (io_injective μ hθ) E).symm

theorem cuspFinite : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), GlobalTheory.Published.AutFin.IsFrameFam V ε fr → ∀ (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)), (∀ τ, GlobalTheory.Published.AutFin.IsContRep (ρ τ)) → ∀ c : D.what₂.Tau → ℕ → ℂ, FiniteDimensional ℂ (Submodule.span ℂ {φ | φ ∈ GlobalTheory.Published.AutFin.forms θ V U ε fr ρ c ∧ IsCuspFun V φ}) := by
  intro D θ hθ V U hU ε fr hfr W _ _ _ ρ hρ c
  obtain ⟨μ, -, hμ, -⟩ := PositivityTheory.MatrixIdentityOffBase.exists_meas V
  haveI := hμ
  haveI := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V μ hμ
  let E : Submodule ℂ (Mc θ V) :=
    { carrier := {φ | φ.1 ∈ forms θ V U ε fr ρ c}
      add_mem' := by
        intro f g hf hg
        obtain ⟨-, f2, f3, f4⟩ := hf
        obtain ⟨-, g2, g3, g4⟩ := hg
        refine ⟨(mem_Mc_iff.1 (f + g).2).1, fun u hu hu' x => ?_, fun τ x => ?_, fun τ k => ?_⟩
        · simp only [Submodule.coe_add, Pi.add_apply, f2 u hu hu' x, g2 u hu hu' x]
        · exact (coeffSpan (ρ τ)).add_mem (f3 τ x) (g3 τ x)
        · rw [Submodule.coe_add, (linOnSm_gelf (θ := θ) (V := V) τ k).add f.1 (smooth_of_mem f) g.1 (smooth_of_mem g),
            f4, g4, smul_add]
      zero_mem' := by
        refine ⟨(mem_Mc_iff.1 (0 : Mc θ V).2).1, fun _ _ _ _ => rfl, fun τ x => (coeffSpan (ρ τ)).zero_mem, fun τ k => ?_⟩
        have := (linOnSm_gelf (θ := θ) (V := V) τ k).smul 0 0
        simpa using this
      smul_mem' := by
        intro a f hf
        obtain ⟨-, f2, f3, f4⟩ := hf
        refine ⟨(mem_Mc_iff.1 (a • f).2).1, fun u hu hu' x => ?_, fun τ x => ?_, fun τ k => ?_⟩
        · simp only [Submodule.coe_smul, Pi.smul_apply, f2 u hu hu' x]
        · exact (coeffSpan (ρ τ)).smul_mem a (f3 τ x)
        · rw [Submodule.coe_smul, (linOnSm_gelf (θ := θ) (V := V) τ k).smul, f4, smul_comm] }
  have hgr : ∀ (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hZ : Z ∈ lieAt V τ),
      Bd μ hθ (E : Set (Mc θ V)) (der hθ τ hZ) := by
    intro τ Z hZ
    obtain ⟨hPu, hPg⟩ := hfr τ
    obtain ⟨n₁, n₂, X, y, hX, hy, hspan, hg⟩ := GlobalTheory.T.lie_algebra_spanned_by_compact_and_frame D θ hθ V τ (ε τ) (fr τ) hPu hPg
    have hYl : ∀ b, (fr τ)⁻¹ * y b * fr τ ∈ lieAt V τ := fun b => lie_conj hPu hPg (hy b)
    have bK : ∀ b, Bd μ hθ (E : Set (Mc θ V)) (der hθ τ (hYl b)) := fun b =>
      (bd_ktype μ hθ hPu (ρ τ) (hρ τ) (hy b) (hYl b)).mono fun φ hφ => hφ.2.2.1 τ
    have bX := bd_of_casimir μ hθ (E : Set (Mc θ V)) hX hYl (c τ 1) (fun φ hφ => by
      have h1 := hφ.2.2.2 τ 1
      rw [hg φ.1 (smooth_of_mem φ)] at h1
      refine Subtype.ext ?_
      rw [Submodule.coe_smul, ← h1]
      simp [Submodule.coe_sum]) bK
    obtain ⟨_, b'⟩ := bd_span μ hθ (E : Set (Mc θ V))
      (Set.range X ∪ Set.range fun b => (fr τ)⁻¹ * y b * fr τ) (by
        rintro _ (⟨a, rfl⟩ | ⟨b, rfl⟩)
        · exact ⟨hX a, bX a⟩
        · exact ⟨hYl b, bK b⟩) (hspan Z hZ)
    exact b'
  obtain ⟨C, hC0, hC⟩ := bd_inf μ hθ (E : Set (Mc θ V)) hgr
  have hfE : FiniteDimensional ℂ E := finite_of_bound μ hθ U hU E (fun φ hφ => hφ.2.1) hC0 hC
  have hle : Submodule.span ℂ {φ | φ ∈ forms θ V U ε fr ρ c ∧ IsCuspFun V φ} ≤ E.map (Mc θ V).subtype :=
    Submodule.span_le.2 fun x hx => ⟨⟨x, mem_Mc_iff.2 ⟨hx.1.1, hx.2⟩⟩, hx.1, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.CompanionTheory.HCCusp

end
