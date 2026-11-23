import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsAdaptedEmpty
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviNormalizesUnipotentVariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbedding
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IteratedDerivOneP
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
open MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.HCCusp.GenEig

open GlobalTheory.Cusp GlobalTheory.Mem.AutSpace GlobalTheory.SmoothForms

variable {D : D7} {θ : GlobalTheory.Mem.Th.InfF D} {V : HSp D}

def quad (hθ : IsInfFam θ) {τ : D.what₂.Tau} {n₁ n₂ : ℕ} {X : Fin n₁ → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {Y : Fin n₂ → Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : ∀ a, X a ∈ lieAt V τ) (hY : ∀ b, Y b ∈ lieAt V τ) :
    Module.End ℂ (Mc θ V) :=
  ∑ a, der hθ τ (hX a) * der hθ τ (hX a) - ∑ b, der hθ τ (hY b) * der hθ τ (hY b)

theorem quad_apply (hθ : IsInfFam θ) {τ : D.what₂.Tau} {n₁ n₂ : ℕ} {X : Fin n₁ → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {Y : Fin n₂ → Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : ∀ a, X a ∈ lieAt V τ) (hY : ∀ b, Y b ∈ lieAt V τ)
    (φ : Mc θ V) : quad hθ hX hY φ =
      ∑ a, der hθ τ (hX a) (der hθ τ (hX a) φ) - ∑ b, der hθ τ (hY b) (der hθ τ (hY b) φ) := by
  simp [quad, LinearMap.sub_apply, LinearMap.sum_apply, Module.End.mul_apply]

theorem symm_of_skew {M H : Type} [AddCommGroup M] [Module ℂ M] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ι : M →ₗ[ℂ] H) {n₁ n₂ : ℕ} (P : Fin n₁ → Module.End ℂ M) (Q : Fin n₂ → Module.End ℂ M)
    (hP : ∀ a x y, ⟪ι (P a x), ι y⟫_ℂ = -⟪ι x, ι (P a y)⟫_ℂ)
    (hQ : ∀ b x y, ⟪ι (Q b x), ι y⟫_ℂ = -⟪ι x, ι (Q b y)⟫_ℂ) (x y : M) :
    ⟪ι ((∑ a, P a * P a - ∑ b, Q b * Q b) x), ι y⟫_ℂ = ⟪ι x, ι ((∑ a, P a * P a - ∑ b, Q b * Q b) y)⟫_ℂ := by
  have h1 : ∀ a x y, ⟪ι (P a (P a x)), ι y⟫_ℂ = ⟪ι x, ι (P a (P a y))⟫_ℂ := fun a x y => by
    rw [hP, hP, neg_neg]
  have h2 : ∀ b x y, ⟪ι (Q b (Q b x)), ι y⟫_ℂ = ⟪ι x, ι (Q b (Q b y))⟫_ℂ := fun b x y => by
    rw [hQ, hQ, neg_neg]
  simp only [LinearMap.sub_apply, LinearMap.sum_apply, Module.End.mul_apply, map_sub, map_sum, inner_sub_left,
    inner_sub_right, sum_inner, inner_sum, h1, h2]

theorem quad_symm (μ : Measure (GA D V)) [μ.IsHaarMeasure] (hθ : IsInfFam θ) {τ : D.what₂.Tau} {n₁ n₂ : ℕ}
    {X : Fin n₁ → Matrix (Fin V.rank) (Fin V.rank) ℂ} {Y : Fin n₂ → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : ∀ a, X a ∈ lieAt V τ) (hY : ∀ b, Y b ∈ lieAt V τ) (φ ψ : Mc θ V) :
    ⟪io μ hθ (quad hθ hX hY φ), io μ hθ ψ⟫_ℂ = ⟪io μ hθ φ, io μ hθ (quad hθ hX hY ψ)⟫_ℂ :=
  symm_of_skew (io μ hθ) (fun a => der hθ τ (hX a)) (fun b => der hθ τ (hY b))
    (fun a x y => GlobalTheory.T.derivative_skew_adjoint_cusp_forms D θ hθ V μ τ _ (hX a) x y) (fun b x y => GlobalTheory.T.derivative_skew_adjoint_cusp_forms D θ hθ V μ τ _ (hY b) x y) φ ψ

theorem bd_of_quad (μ : Measure (GA D V)) [μ.IsHaarMeasure] (hθ : IsInfFam θ) {τ : D.what₂.Tau}
    (E : Set (Mc θ V)) {n₁ n₂ : ℕ} {X : Fin n₁ → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {Y : Fin n₂ → Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : ∀ a, X a ∈ lieAt V τ) (hY : ∀ b, Y b ∈ lieAt V τ)
    (hT : Bd μ hθ E (quad hθ hX hY))
    (hK : ∀ b, Bd μ hθ E (der hθ τ (hY b))) (a : Fin n₁) : Bd μ hθ E (der hθ τ (hX a)) := by
  choose κ hκ0 hκ using hK
  obtain ⟨Λ, hΛ0, hΛ⟩ := hT
  set B : ℝ := Λ + ∑ b, κ b ^ 2 with hB
  have hB0 : 0 ≤ B := add_nonneg hΛ0 (Finset.sum_nonneg fun b _ => sq_nonneg _)
  refine ⟨Real.sqrt B, Real.sqrt_nonneg _, fun φ hφ => ?_⟩
  have h2 := congrArg (fun w => ⟪io μ hθ φ, io μ hθ w⟫_ℂ) (quad_apply hθ hX hY φ)
  simp only [map_sub, map_sum, inner_sub_right, inner_sum, inner_der_der] at h2
  have h3 := congrArg Complex.re h2
  simp only [Complex.sub_re, Complex.re_sum, Complex.neg_re, Complex.ofReal_re,
    Finset.sum_neg_distrib, sub_neg_eq_add, Complex.add_re] at h3
  have h4 : ‖io μ hθ (der hθ τ (hX a) φ)‖ ^ 2 ≤ ∑ x, ‖io μ hθ (der hθ τ (hX x) φ)‖ ^ 2 :=
    Finset.single_le_sum (f := fun x => ‖io μ hθ (der hθ τ (hX x) φ)‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ a)
  have h5 : ∑ b, ‖io μ hθ (der hθ τ (hY b) φ)‖ ^ 2 ≤ (∑ b, κ b ^ 2) * ‖io μ hθ φ‖ ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hκ b φ hφ) 2
  have h6 : -(⟪io μ hθ φ, io μ hθ (quad hθ hX hY φ)⟫_ℂ).re ≤ Λ * ‖io μ hθ φ‖ ^ 2 := by
    have e1 := (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans
      (norm_inner_le_norm (𝕜 := ℂ) (io μ hθ φ) (io μ hθ (quad hθ hX hY φ))))
    have e2 := mul_le_mul_of_nonneg_left (hΛ φ hφ) (norm_nonneg (io μ hθ φ))
    nlinarith
  have h7 : ‖io μ hθ (der hθ τ (hX a) φ)‖ ^ 2 ≤ B * ‖io μ hθ φ‖ ^ 2 := by
    rw [hB, add_mul]
    linarith
  have h8 := Real.sqrt_le_sqrt h7
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hB0, Real.sqrt_sq (norm_nonneg _)] at h8

def opOf {M : Type} [AddCommGroup M] [Module ℂ M] (C : Module.End ℂ M) (L : List ℂ) : Module.End ℂ M :=
  L.foldr (fun a T => (C - a • 1) * T) 1

theorem bd_of_opOf {M H : Type} [AddCommGroup M] [Module ℂ M] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ι : M →ₗ[ℂ] H) (hι : Function.Injective ι) (C : Module.End ℂ M)
    (hC : ∀ x y, ⟪ι (C x), ι y⟫_ℂ = ⟪ι x, ι (C y)⟫_ℂ) (L : List ℂ) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ x, opOf C L x = 0 → ‖ι (C x)‖ ≤ κ * ‖ι x‖ := by
  classical
  let S : Module.End ℂ M := Complex.I • C
  let m : Polynomial ℂ := (L.map fun a => Polynomial.X - Polynomial.C (Complex.I * a)).prod
  have hm : m ≠ 0 := List.prod_ne_zero (by
    simp only [List.mem_map, not_exists, not_and]
    exact fun a _ => Polynomial.X_sub_C_ne_zero _)
  have hS : ∀ x y, ⟪ι (S x), ι y⟫_ℂ = -⟪ι x, ι (S y)⟫_ℂ := fun x y => by
    simp only [S, LinearMap.smul_apply, map_smul, inner_smul_left, inner_smul_right, hC]
    simp
  have hmS : ∀ L' : List ℂ, Polynomial.aeval S ((L'.map fun a => Polynomial.X - Polynomial.C (Complex.I * a)).prod) =
      Complex.I ^ L'.length • opOf C L' := by
    intro L'
    induction L' with
    | nil => simp [opOf]
    | cons a l ih =>
      have e : opOf C (a :: l) = (C - a • 1) * opOf C l := rfl
      rw [List.map_cons, List.prod_cons, map_mul, ih, e, List.length_cons, pow_succ]
      have e2 : Polynomial.aeval S (Polynomial.X - Polynomial.C (Complex.I * a)) = Complex.I • (C - a • 1) := by
        simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, S, smul_sub, smul_smul]
      rw [e2, smul_mul_smul_comm, mul_comm]
  have hκ0 : 0 ≤ ∑ r ∈ m.roots.toFinset, ‖r‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨_, hκ0, fun x hx => ?_⟩
  have h := GlobalTheory.T.skew_operator_bounded_by_polynomial_roots M H ι hι S hS m hm _ hκ0
    (fun r hr => Finset.single_le_sum (f := fun r : ℂ => ‖r‖) (fun _ _ => norm_nonneg _)
      (Multiset.mem_toFinset.2 hr)) x (by
      rw [hmS L, LinearMap.smul_apply, hx, smul_zero])
  simpa [S, norm_smul] using h

theorem foldr_gelf (τ : D.what₂.Tau) (C : Module.End ℂ (Mc θ V)) (hC : ∀ φ : Mc θ V, gelf θ V τ 1 φ.1 = (C φ).1)
    (L : List ℂ) (φ : Mc θ V) :
    L.foldr (fun a f => gelf θ V τ 1 f - a • f) φ.1 = (opOf C L φ).1 := by
  induction L with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldr_cons, ih, hC]
    rfl

theorem exists_gelfOp (hθ : IsInfFam θ) {τ : D.what₂.Tau} {e : Fin V.rank → Bool}
    {P : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hP : IsUnit P) (hg : Pᴴ * Formalism.REAL.Jm e * P = gramAt D V τ) :
    ∃ C : Module.End ℂ (Mc θ V), (∀ φ : Mc θ V, gelf θ V τ 1 φ.1 = (C φ).1) ∧
      ∀ (μ : Measure (GA D V)) [μ.IsHaarMeasure] (φ ψ : Mc θ V),
        ⟪io μ hθ (C φ), io μ hθ ψ⟫_ℂ = ⟪io μ hθ φ, io μ hθ (C ψ)⟫_ℂ := by
  obtain ⟨n₁, n₂, X, y, hX, hy, -, hq⟩ := GlobalTheory.T.lie_algebra_spanned_by_compact_and_frame D θ hθ V τ e P hP hg
  have hYl : ∀ b, P⁻¹ * y b * P ∈ lieAt V τ := fun b => lie_conj hP hg (hy b)
  refine ⟨quad hθ hX hYl, fun φ => ?_, fun μ _ φ ψ => quad_symm μ hθ hX hYl φ ψ⟩
  rw [hq φ.1 (smooth_of_mem φ), quad_apply]
  simp [Submodule.coe_sum]

theorem bd_der (μ : Measure (GA D V)) [μ.IsHaarMeasure] (hθ : IsInfFam θ) {τ : D.what₂.Tau} {e : Fin V.rank → Bool}
    {P : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hP : IsUnit P) (hg : Pᴴ * Formalism.REAL.Jm e * P = gramAt D V τ)
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Formalism.REAL.KG e) W)
    (hρ : IsContRep ρ) (E : Set (Mc θ V)) (hE : ∀ φ ∈ E, HasTypeAt θ V τ e P ρ φ.1) (C : Module.End ℂ (Mc θ V))
    (hC : ∀ φ : Mc θ V, gelf θ V τ 1 φ.1 = (C φ).1) (hb : Bd μ hθ E C)
    (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hZ : Z ∈ lieAt V τ) : Bd μ hθ E (der hθ τ hZ) := by
  obtain ⟨n₁, n₂, X, y, hX, hy, hspan, hq⟩ := GlobalTheory.T.lie_algebra_spanned_by_compact_and_frame D θ hθ V τ e P hP hg
  have hYl : ∀ b, P⁻¹ * y b * P ∈ lieAt V τ := fun b => lie_conj hP hg (hy b)
  have bK : ∀ b, Bd μ hθ E (der hθ τ (hYl b)) := fun b =>
    (bd_ktype μ hθ hP ρ hρ (hy b) (hYl b)).mono fun φ hφ => hE φ hφ
  have hCq : C = quad hθ hX hYl := LinearMap.ext fun φ => Subtype.ext (by
    rw [← hC, hq φ.1 (smooth_of_mem φ), quad_apply]
    simp [Submodule.coe_sum])
  have bX := bd_of_quad μ hθ E hX hYl (hCq ▸ hb) bK
  obtain ⟨_, b'⟩ := bd_span μ hθ E (Set.range X ∪ Set.range fun b => P⁻¹ * y b * P) (by
    rintro _ (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · exact ⟨hX a, bX a⟩
    · exact ⟨hYl b, bK b⟩) (hspan Z hZ)
  exact b'

theorem finite_of_polyGelf : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)), (∀ τ, IsContRep (ρ τ)) → ∀ A : D.what₂.Tau → List ℂ, FiniteDimensional ℂ (Submodule.span ℂ {φ : GA D V → ℂ | IsAutFunSm θ V φ ∧ (∀ u ∈ U, u ∈ GfC V → ∀ g, φ (g * u) = φ g) ∧ (∀ τ, HasTypeAt θ V τ (ε τ) (fr τ) (ρ τ) φ) ∧ IsCuspFun V φ ∧ ∀ τ, (A τ).foldr (fun a f => gelf θ V τ 1 f - a • f) φ = 0}) := by
  intro D θ hθ V U hU ε fr hfr W _ _ _ ρ hρ A
  obtain ⟨μ, -, hμ, -⟩ := PositivityTheory.MatrixIdentityOffBase.exists_meas V
  haveI := hμ
  haveI := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V μ hμ
  have hop := fun τ => exists_gelfOp (θ := θ) (V := V) (τ := τ) hθ (hfr τ).1 (hfr τ).2
  choose C hCg hCs using hop
  let E : Submodule ℂ (Mc θ V) :=
    { carrier := {φ | (∀ u ∈ U, u ∈ GfC V → ∀ g, φ.1 (g * u) = φ.1 g) ∧
        (∀ τ, HasTypeAt θ V τ (ε τ) (fr τ) (ρ τ) φ.1) ∧ ∀ τ, opOf (C τ) (A τ) φ = 0}
      add_mem' := by
        intro f g hf hg
        refine ⟨fun u hu hu' x => ?_, fun τ x => ?_, fun τ => ?_⟩
        · simp only [Submodule.coe_add, Pi.add_apply, hf.1 u hu hu' x, hg.1 u hu hu' x]
        · exact (coeffSpan (ρ τ)).add_mem (hf.2.1 τ x) (hg.2.1 τ x)
        · rw [map_add, hf.2.2, hg.2.2, add_zero]
      zero_mem' := ⟨fun _ _ _ _ => rfl, fun τ x => (coeffSpan (ρ τ)).zero_mem, fun τ => map_zero _⟩
      smul_mem' := by
        intro a f hf
        refine ⟨fun u hu hu' x => ?_, fun τ x => ?_, fun τ => ?_⟩
        · simp only [Submodule.coe_smul, Pi.smul_apply, hf.1 u hu hu' x]
        · exact (coeffSpan (ρ τ)).smul_mem a (hf.2.1 τ x)
        · rw [map_smul, hf.2.2, smul_zero] }
  have hgr : ∀ (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hZ : Z ∈ lieAt V τ),
      Bd μ hθ (E : Set (Mc θ V)) (der hθ τ hZ) := by
    intro τ Z hZ
    obtain ⟨κ, hκ0, hκ⟩ := bd_of_opOf (io μ hθ) (io_injective μ hθ) (C τ) (hCs τ μ) (A τ)
    exact bd_der μ hθ (hfr τ).1 (hfr τ).2 (ρ τ) (hρ τ) (E : Set (Mc θ V)) (fun φ hφ => hφ.2.1 τ) (C τ) (hCg τ)
      ⟨κ, hκ0, fun φ hφ => hκ φ (hφ.2.2 τ)⟩ Z hZ
  obtain ⟨B, hB0, hB⟩ := bd_inf μ hθ (E : Set (Mc θ V)) hgr
  have hfE : FiniteDimensional ℂ E := finite_of_bound μ hθ U hU E (fun φ hφ => hφ.1) hB0 hB
  refine Submodule.finiteDimensional_of_le (S₂ := E.map (Mc θ V).subtype) (Submodule.span_le.2 ?_)
  rintro x ⟨h1, h2, h3, h4, h5⟩
  refine ⟨⟨x, mem_Mc_iff.2 ⟨h1, h4⟩⟩, ⟨h2, h3, fun τ => Subtype.ext ?_⟩, rfl⟩
  rw [← foldr_gelf τ (C τ) (hCg τ) (A τ)]
  exact h5 τ

end GlobalTheory.CompanionTheory.HCCusp.GenEig
end
