import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.BaseChangeIndex
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Assembly
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsThetaSectionsBoundedStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IteratedDerivBoundGaussianGrowthStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.IntegralFlagEmbeddingCriterionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PolarizedDataFieldExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionSupNormFieldExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaFunctionArchimedeanFrameStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsIntegralJetBasisStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ThetaDerivativeBoundStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsThetaSupBoundLogMeanStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaMultiplierQuadraticCharacterStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.LineProof

theorem sum_range_lin (n : ℕ) (X Y : ℝ) :
    ∑ i ∈ Finset.range (n + 1), ((i : ℝ) * X + Y) = (n : ℝ) * (n + 1) / 2 * X + (n + 1) * Y := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem slope_sum {K : Type} [Field K] [NumberField K] (n' : ℕ) (hn' : 1 ≤ n') (B T : ℝ) (hB : 0 < B) (hT : 0 < T)
    (len Mσ : (K →+* ℂ) → ℝ) (hl : ∀ σ, 0 < len σ) (hM : ∀ σ, 0 < Mσ σ)
    (h : 0 ≤ ∑ i ∈ Finset.range (n' + 1), ∑ σ : K →+* ℂ, Real.log (B ^ i * len σ ^ i * (T * Mσ σ))) :
    -mean K (fun σ => Real.log (len σ)) ≤
      Real.log B + 2 / (n' : ℝ) * (Real.log T + mean K (fun σ => Real.log (Mσ σ))) := by
  have hcard : (Fintype.card (K →+* ℂ) : ℝ) = (Module.finrank ℚ K : ℝ) := by
    rw [NumberField.Embeddings.card K ℂ]
  have hd : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast Module.finrank_pos
  have hn : (0 : ℝ) < (n' : ℝ) := by exact_mod_cast hn'
  set d : ℝ := (Module.finrank ℚ K : ℝ) with hdd
  set Sl : ℝ := ∑ σ : K →+* ℂ, Real.log (len σ) with hSl
  set Sm : ℝ := ∑ σ : K →+* ℂ, Real.log (Mσ σ) with hSm
  have e1 : ∀ i : ℕ, ∑ σ : K →+* ℂ, Real.log (B ^ i * len σ ^ i * (T * Mσ σ)) =
      (i : ℝ) * (d * Real.log B + Sl) + (d * Real.log T + Sm) := by
    intro i
    have : ∀ σ : K →+* ℂ, Real.log (B ^ i * len σ ^ i * (T * Mσ σ)) =
        (i : ℝ) * Real.log B + (i : ℝ) * Real.log (len σ) + Real.log T + Real.log (Mσ σ) := by
      intro σ
      have h1 := (hl σ).ne'
      have h2 := (hM σ).ne'
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_mul hT.ne' h2]
      ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum,
      hcard, ← hSl, ← hSm, ← hdd]
    ring
  simp only [e1] at h
  rw [sum_range_lin] at h
  have hmean1 : mean K (fun σ => Real.log (len σ)) = Sl / d := rfl
  have hmean2 : mean K (fun σ => Real.log (Mσ σ)) = Sm / d := rfl
  rw [hmean1, hmean2]
  have hP : 0 < (n' : ℝ) * (n' + 1) / 2 * d := by positivity
  have key : 0 ≤ ((n' : ℝ) * (n' + 1) / 2 * d) *
      (Real.log B + 2 / (n' : ℝ) * (Real.log T + Sm / d) + Sl / d) := by
    have : ((n' : ℝ) * (n' + 1) / 2 * d) * (Real.log B + 2 / (n' : ℝ) * (Real.log T + Sm / d) + Sl / d) =
        (n' : ℝ) * (n' + 1) / 2 * (d * Real.log B + Sl) + (n' + 1) * (d * Real.log T + Sm) := by
      field_simp
      ring
    rw [this]
    exact h
  have := nonneg_of_mul_nonneg_right key hP
  linarith

theorem mean_comp {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (f : (K →+* ℂ) → ℝ) : mean K' (fun σ => f (σ.comp (algebraMap K K'))) = mean K f := by
  have hd : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  have hd' : (Module.finrank K K' : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := K) (M := K')).ne'
  have hm : (Module.finrank ℚ K' : ℝ) = Module.finrank ℚ K * Module.finrank K K' := by
    exact_mod_cast (Module.finrank_mul_finrank ℚ K K').symm
  simp only [mean]
  rw [GroundTheory.Heights₂.Heights.LatticeLemmas.sum_comp_algebraMap, hm]
  field_simp

section Frame

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : RigLB G} {z : Sp ℂ ⟶ S} {g : ℕ}

theorem herm_smul (a : ArchFrame P z g) (τ : ℂ) (v : Fin g → ℂ) :
    (a.herm (τ • v) (τ • v)).re = ‖τ‖ ^ 2 * (a.herm v v).re := by
  have : a.herm (τ • v) (τ • v) = ((‖τ‖ ^ 2 : ℝ) : ℂ) * a.herm v v := by
    simp only [ArchFrame.herm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    have h : star τ * τ = ((‖τ‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, _root_.mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [← _root_.mul_assoc, h]
  rw [this, Complex.re_ofReal_mul]

theorem sum_bound (a : ArchFrame P z g) (n r : ℕ) (f : Fin r → (Fin g → ℂ) → ℂ) (Mv : ℝ) (hM : 0 < Mv)
    (hs : ∀ j w, a.nrm n (f j) w ≤ Mv) (c : Fin r → ℂ) (w : Fin g → ℂ) :
    ‖∑ j, c j * f j w‖ ≤ (√(r : ℝ) * Mv * √(∑ j, ‖c j‖ ^ 2)) *
      Real.exp (Real.pi * n / 2 * (a.herm w w).re) := by
  set e : ℝ := Real.exp (-(Real.pi * n / 2) * (a.herm w w).re) with he
  have hepos : 0 < e := Real.exp_pos _
  have hk : 0 < Mv⁻¹ * e := by positivity
  have h1 := SupOfOrthonormalSum.full ℂ (Fin r) (fun j => ((Mv⁻¹ * e : ℝ) : ℂ) * f j w) (normSeminorm ℂ ℂ)
    (by
      intro j
      have h2 := hs j w
      simp only [ArchFrame.nrm] at h2
      simp only [coe_normSeminorm, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk]
      have h3 : Mv⁻¹ * e * ‖f j w‖ = Mv⁻¹ * (‖f j w‖ * e) := by ring
      first
        | rw [abs_of_pos (inv_pos.2 hM), abs_of_pos hepos, h3, inv_mul_le_iff₀ hM, _root_.mul_one]
        | rw [h3, inv_mul_le_iff₀ hM, _root_.mul_one]
      exact h2) c
  simp only [coe_normSeminorm, Fintype.card_fin, smul_eq_mul] at h1
  have h3 : ∑ j, c j * (((Mv⁻¹ * e : ℝ) : ℂ) * f j w) = ((Mv⁻¹ * e : ℝ) : ℂ) * ∑ j, c j * f j w := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h3, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk] at h1
  have h4 : Real.exp (Real.pi * n / 2 * (a.herm w w).re) = e⁻¹ := by
    rw [he, ← Real.exp_neg]
    congr 1
    ring
  rw [h4]
  have h5 : ‖∑ j, c j * f j w‖ = (Mv * e⁻¹) * ((Mv⁻¹ * e) * ‖∑ j, c j * f j w‖) := by
    field_simp
  rw [h5]
  have h6 : 0 < Mv * e⁻¹ := by positivity
  calc (Mv * e⁻¹) * ((Mv⁻¹ * e) * ‖∑ j, c j * f j w‖)
      ≤ (Mv * e⁻¹) * (√(r : ℝ) * √(∑ j, ‖c j‖ ^ 2)) := by gcongr
    _ = _ := by ring

end Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem fn_ne_zero {H : Host E} {L : Type} [Field L] [NumberField L] (D : PPData H L) (th : Out.H0 D.t.PP.L 1) {Φ : ℝ}
    (hth : D.HasTheta th Φ) (σ : L →+* ℂ) {g : ℕ} (hg : g = D.g) (a : ArchFrame D.t.PP (emb σ) g)
    (θ : (Fin g → ℂ) → ℂ) (h : a.IsFn th θ) : θ ≠ 0 := by
  subst hg
  obtain ⟨b, hb, -⟩ := hth
  obtain ⟨hb0, hL⟩ := hb σ a θ h
  rintro rfl
  have h1 := a.u.discrete
  have h2 : IsZLattice ℝ a.u.Λ := ⟨a.u.full⟩
  have hF := ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ a.u.Λ) (volume : Measure (Fin D.g → ℂ))
  have h3 := hL _ hF
  simp [ArchFrame.nrm] at h3
  exact absurd h3 hb0.ne'

theorem theta_on_ext {H : Host E} {L L' : Type} [Field L] [NumberField L] [Field L'] [NumberField L'] [Algebra L L']
    (D : PPData H L) (D' : PPData H L') (e : D.Ext D') (th : Out.H0 D.t.PP.L 1) {Φ : ℝ} (hth : D.HasTheta th Φ)
    (hg : D'.g = D.g) (σ' : L' →+* ℂ) (a' : D'.Frame σ') : ∃ θ, a'.IsTheta 1 θ ∧ θ ≠ 0 := by
  obtain ⟨s', -, hs'⟩ := GlobalTheory.T.section_sup_norm_field_extension E H L D L' D' e 1 th
  obtain ⟨-, hall⟩ := GlobalTheory.T.theta_function_archimedean_frame E H L' D' σ'
  obtain ⟨h1, h2, -⟩ := hall a'
  obtain ⟨θ, hθ, -⟩ := h1 1 s'
  obtain ⟨a, -, -, hiff⟩ := hs' σ' a'
  exact ⟨θ, h2 1 s' θ hθ, fn_ne_zero D th hth _ hg a θ ((hiff θ).2 hθ)⟩

theorem g_pos {H : Host E} {L : Type} [Field L] [NumberField L] (D : PPData H L) (x : D.B.carrier) (hx : x ≠ 0) :
    1 ≤ D.g := by
  by_contra hg
  have hg0 : D.g = 0 := by omega
  have σ : L →+* ℂ := (IsAlgClosed.lift : L →ₐ[ℚ] ℂ).toRingHom
  obtain ⟨⟨a⟩, hall⟩ := GlobalTheory.T.theta_function_archimedean_frame E H L D σ
  obtain ⟨-, -, hv⟩ := hall a
  obtain ⟨⟨c, hc, -⟩, hc2⟩ := hv x
  have h3 := (hc2 c hc).2 hx
  have : IsEmpty (Fin D.g) := by rw [hg0]; infer_instance
  exact h3 (funext fun i => isEmptyElim i)

theorem len_pos {H : Host E} {L : Type} [Field L] [NumberField L] (D : PPData H L) (x : D.B.carrier) (hx : x ≠ 0)
    (σ : L →+* ℂ) : 0 < D.len σ x := by
  obtain ⟨⟨a⟩, hall⟩ := GlobalTheory.T.theta_function_archimedean_frame E H L D σ
  obtain ⟨-, -, hv⟩ := hall a
  obtain ⟨⟨c, hc, -⟩, hc2⟩ := hv x
  obtain ⟨h2, h3⟩ := hc2 c hc
  have hpos : 0 < (a.herm c c).re := a.ah.2.1 c (h3 hx)
  have h4 : 0 < D.len σ x ^ 2 := by
    rw [h2]
    exact mul_pos Real.pi_pos hpos
  have h0 : 0 ≤ D.len σ x := Real.sqrt_nonneg _
  exact lt_of_le_of_ne h0 fun h => by
    rw [← h] at h4
    simp at h4

theorem core_applied {H : Host E} {L : Type} [Field L] [NumberField L] (D : PPData H L) (x : D.B.carrier) (hx : x ≠ 0)
    (n n' r : ℕ) (hn : n = 3 * n') (hn' : 1 ≤ n') (hr : 0 < r) (s : Fin r → Out.H0 D.t.PP.L n)
    (Mv : (L →+* ℂ) → ℝ) (hM : ∀ σ, 0 < Mv σ) (hs : ∀ j, D.SupLe (s j) Mv)
    (hθ : ∀ (σ : L →+* ℂ) (a : D.Frame σ), ∃ θ, a.IsTheta 1 θ ∧ θ ≠ 0)
    (hspan : ∀ (σ : L →+* ℂ) (a : D.Frame σ) (f : Fin r → (Fin D.g → ℂ) → ℂ), (∀ i, a.IsFn (s i) (f i)) →
      ∀ F, a.IsTheta n F → ∃ c : Fin r → ℂ, F = ∑ i, c i • f i) :
    0 ≤ ∑ i ∈ Finset.range (n' + 1), ∑ σ : L →+* ℂ,
      Real.log (√(Real.exp 1 * n * n') ^ i * D.len σ x ^ i * (√(r : ℝ) * Mv σ)) := by
  subst hn
  have hlen := len_pos D x hx
  have hn0 : (0 : ℝ) < n' := by exact_mod_cast hn'
  have hB : 0 < √(Real.exp 1 * ((3 * n' : ℕ) : ℝ) * n') := by
    apply Real.sqrt_pos.2
    push_cast
    positivity
  have hr0 : 0 < √(r : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hr)

  have hdata : ∀ σ : L →+* ℂ, ∃ (a : D.Frame σ) (f : Fin r → (Fin D.g → ℂ) → ℂ) (v : Fin D.g → ℂ),
      (∀ j, a.IsFn (s j) (f j)) ∧ (∀ j, a.IsTheta (3 * n') (f j)) ∧ D.IsVec a x v ∧ v ≠ 0 ∧
        D.len σ x ^ 2 = Real.pi * (a.herm v v).re := by
    intro σ
    obtain ⟨⟨a⟩, hall⟩ := GlobalTheory.T.theta_function_archimedean_frame E H L D σ
    obtain ⟨h1, h2, hv⟩ := hall a
    choose f hf using fun j => (h1 (3 * n') (s j)).exists
    obtain ⟨⟨c, hc, -⟩, hc2⟩ := hv x
    obtain ⟨h5, h6⟩ := hc2 c hc
    exact ⟨a, f, c, hf, fun j => h2 _ _ _ (hf j), hc, h6 hx, h5⟩
  obtain ⟨J, hint, hJ⟩ := GlobalTheory.T.exists_integral_jet_basis E H L D x (3 * n') r s
  refine GlobalTheory.T.integral_flag_embedding_criterion L r n' J
    (fun i σ => √(Real.exp 1 * ((3 * n' : ℕ) : ℝ) * n') ^ i * D.len σ x ^ i * (√(r : ℝ) * Mv σ)) ?_ hint ?_ ?_
  · intro i σ
    have := hlen σ
    have := hM σ
    positivity
  · intro i hi
    have σ : L →+* ℂ := (IsAlgClosed.lift : L →ₐ[ℚ] ℂ).toRingHom
    obtain ⟨a, f, v, hf, -, hvec, hv0, -⟩ := hdata σ
    obtain ⟨θ, hθ1, hθ0⟩ := hθ σ a
    obtain ⟨u1, u2, u3, -⟩ := GlobalTheory.T.theta_multiplier_quadratic_character E H L D σ a
    obtain ⟨F, hF, hvan, hne⟩ := GlobalTheory.T.theta_derivative_bound a u1 u2 u3 θ v n' i hθ1 hθ0 hv0 hi
    obtain ⟨c, hc⟩ := hspan σ a f hf F hF
    have hfun : (fun τ : ℂ => F (τ • v)) = fun τ : ℂ => ∑ j, c j * f j (τ • v) := by
      funext τ
      rw [hc]
      simp [Finset.sum_apply]
    rw [hfun] at hvan hne
    have h := hJ σ a f v hf hvec i c
    have h7 := h.1.2 hvan
    refine ⟨σ, c, h7, ?_⟩
    rw [h.2 h7]
    exact hne
  · intro i hi σ c hvan
    obtain ⟨a, f, v, hf, hT, hvec, -, hl2⟩ := hdata σ
    have h := hJ σ a f v hf hvec i c
    rw [h.2 hvan]
    have hd : ∀ j, Differentiable ℂ (fun τ : ℂ => f j (τ • v)) := fun j =>
      (hT j).1.comp (differentiable_id.smul_const v)
    have hdiff : Differentiable ℂ (fun τ : ℂ => ∑ j, c j * f j (τ • v)) :=
      Differentiable.fun_sum fun j _ => (hd j).const_mul _
    have hgrow : ∀ τ : ℂ, ‖∑ j, c j * f j (τ • v)‖ ≤ (√(r : ℝ) * Mv σ * √(∑ j, ‖c j‖ ^ 2)) *
        Real.exp (((3 * n' : ℕ) : ℝ) * ‖τ‖ ^ 2 * D.len σ x ^ 2 / 2) := by
      intro τ
      have h8 := sum_bound a (3 * n') r f (Mv σ) (hM σ) (fun j w => hs j σ a (f j) (hf j) w) c (τ • v)
      have h9 : Real.pi * ((3 * n' : ℕ) : ℝ) / 2 * (a.herm (τ • v) (τ • v)).re =
          ((3 * n' : ℕ) : ℝ) * ‖τ‖ ^ 2 * D.len σ x ^ 2 / 2 := by
        rw [herm_smul, hl2]
        ring
      rwa [h9] at h8
    have h10 := GlobalTheory.T.iterated_deriv_bound_gaussian_growth (fun τ : ℂ => ∑ j, c j * f j (τ • v)) _ (D.len σ x) (3 * n') n' i hdiff (hlen σ)
      (by omega) hn' hi hgrow
    calc _ ≤ _ := h10
      _ = _ := by ring

theorem line_of_key : KeyDegSt → LineSt := by
  rintro ⟨C₁, hC₁, key⟩
  obtain ⟨C₃, hC₃, sup⟩ := GlobalTheory.T.exists_theta_sup_bound_log_mean
  have hlog1 : 0 ≤ Real.log (1 + C₁) := Real.log_nonneg (by linarith)
  have hC₂ : 0 ≤ C₃ * (1 + Real.log (1 + C₁)) := mul_nonneg hC₃ (by linarith)
  obtain ⟨C₄, hC₄⟩ := SlopeParameterChoice.full C₁ _ hC₁ hC₂
  refine ⟨max C₄ 0, le_max_right _ _, ?_⟩
  intro E _ _ _ H L _ _ D x hx
  have hg1 : 1 ≤ D.g := g_pos D x hx
  have hg1R : (1 : ℝ) ≤ D.g := by exact_mod_cast hg1
  have hh : 0 ≤ D.hp := le_max_right _ _
  obtain ⟨L₁, _, _, _, D₁, e₁, th, hth⟩ := key E H L D hg1
  obtain ⟨hg₁, hh₁, io₁, hi₁, -, hm₁⟩ := (GlobalTheory.T.polarized_data_field_extension E H L D L₁).2 D₁ e₁
  have hΦ : 0 ≤ D.hp / 2 + C₁ * D.g := by positivity
  obtain ⟨M, hM, hsup, hmean⟩ := sup E H L₁ D₁ th _ (hg₁.symm ▸ hg1) hΦ hth
  rw [hg₁] at hmean
  obtain ⟨m, hm⟩ : ∃ m, m = SlopeParameterChoice.level D.g D.hp := ⟨_, rfl⟩
  obtain ⟨K, hK, hmK⟩ : ∃ K : ℕ, 1 ≤ K ∧ m = 3 * K :=
    ⟨⌈2 + (D.g : ℝ) ^ 2 + D.hp⌉₊, Nat.ceil_pos.2 (by positivity), hm⟩
  have hm1 : 1 ≤ m := by omega
  obtain ⟨L₂, _, _, _, D₂, e₂, s, hsup₂, hspan⟩ := GlobalTheory.T.exists_theta_sections_bounded E H L₁ D₁ th _ M m hm1 hth hsup
  obtain ⟨hg₂, hh₂, io₂, hi₂, -, hm₂⟩ := (GlobalTheory.T.polarized_data_field_extension E H L₁ D₁ L₂).2 D₂ e₂
  have hx₁ : io₁ x ≠ 0 := fun h => hx (hi₁ (by rw [h, map_zero]))
  have hx₂ : io₂ (io₁ x) ≠ 0 := fun h => hx₁ (hi₂ (by rw [h, map_zero]))
  have hK2 : 1 ≤ 3 * K ^ 2 := by
    have : 1 ≤ K ^ 2 := Nat.one_le_pow _ _ hK
    omega
  have hr : 0 < m ^ (2 * D₁.g) := by positivity
  have hcore := core_applied D₂ (io₂ (io₁ x)) hx₂ (m ^ 2) (3 * K ^ 2) (m ^ (2 * D₁.g)) (by rw [hmK]; ring) hK2 hr s
    (fun σ => M (σ.comp (algebraMap L₁ L₂))) (fun σ => hM _) hsup₂
    (fun σ a => theta_on_ext D₁ D₂ e₂ th hth hg₂ σ a) hspan
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hmR : (m : ℝ) = 3 * K := by rw [hmK]; push_cast; ring
  have hB : 0 < √(Real.exp 1 * ((m ^ 2 : ℕ) : ℝ) * ((3 * K ^ 2 : ℕ) : ℝ)) := by
    apply Real.sqrt_pos.2
    push_cast
    rw [hmR]
    positivity
  have hr0 : 0 < √((m ^ (2 * D₁.g) : ℕ) : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hr)
  have hslope := slope_sum (3 * K ^ 2) hK2 _ _ hB hr0 (fun σ => D₂.len σ (io₂ (io₁ x)))
    (fun σ => M (σ.comp (algebraMap L₁ L₂))) (len_pos D₂ _ hx₂) (fun σ => hM _) hcore

  have hlen₂ : ∀ σ : L₂ →+* ℂ, D₂.len σ (io₂ (io₁ x)) = D₁.len (σ.comp (algebraMap L₁ L₂)) (io₁ x) := by
    intro σ
    simp only [PPData.len]
    rw [hm₂]
  have hlen₁ : ∀ σ : L₁ →+* ℂ, D₁.len σ (io₁ x) = D.len (σ.comp (algebraMap L L₁)) x := by
    intro σ
    simp only [PPData.len]
    rw [hm₁]
  have hmeanlen : mean L₂ (fun σ => Real.log (D₂.len σ (io₂ (io₁ x)))) = mean L (fun σ => Real.log (D.len σ x)) := by
    simp only [hlen₂, hlen₁]
    rw [mean_comp (fun σ : L₁ →+* ℂ => Real.log (D.len (σ.comp (algebraMap L L₁)) x)),
      mean_comp (fun σ : L →+* ℂ => Real.log (D.len σ x))]
  have hmeanM : mean L₂ (fun σ => Real.log (M (σ.comp (algebraMap L₁ L₂)))) = mean L₁ (fun σ => Real.log (M σ)) :=
    mean_comp (fun σ : L₁ →+* ℂ => Real.log (M σ))
  rw [hmeanlen, hmeanM] at hslope

  have hthird : SlopeParameterChoice.third D.g D.hp = ((3 * K ^ 2 : ℕ) : ℝ) := by
    rw [SlopeParameterChoice.third, ← hm, hmR]
    push_cast
    ring
  have hlogB : Real.log (√(Real.exp 1 * ((m ^ 2 : ℕ) : ℝ) * ((3 * K ^ 2 : ℕ) : ℝ))) =
      1 / 2 * Real.log (3 * Real.exp 1 * SlopeParameterChoice.third D.g D.hp ^ 2) := by
    rw [Real.log_sqrt (by positivity), hthird]
    have : Real.exp 1 * ((m ^ 2 : ℕ) : ℝ) * ((3 * K ^ 2 : ℕ) : ℝ) = 3 * Real.exp 1 * ((3 * K ^ 2 : ℕ) : ℝ) ^ 2 := by
      push_cast
      rw [hmR]
      ring
    rw [this]
    ring
  have hlogT : Real.log (√((m ^ (2 * D₁.g) : ℕ) : ℝ)) = D.g * Real.log (SlopeParameterChoice.level D.g D.hp) := by
    rw [Real.log_sqrt (by positivity), ← hm, hg₁]
    push_cast
    rw [Real.log_pow]
    push_cast
    ring
  rw [hlogB, hlogT, ← hthird] at hslope

  set Y : ℝ := 2 + D.g + D.hp with hY
  have hY3 : 3 ≤ Y := by rw [hY]; linarith
  have hlogY : 1 ≤ Real.log Y := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hbd : Real.log (2 + D.g + (D.hp / 2 + C₁ * D.g)) ≤ (1 + Real.log (1 + C₁)) * Real.log Y := by
    have h1 : 2 + (D.g : ℝ) + (D.hp / 2 + C₁ * D.g) ≤ (1 + C₁) * Y := by
      rw [hY]
      nlinarith [mul_nonneg hC₁ hh]
    have h2 : Real.log (2 + D.g + (D.hp / 2 + C₁ * D.g)) ≤ Real.log ((1 + C₁) * Y) :=
      Real.log_le_log (by positivity) h1
    rw [Real.log_mul (by positivity) (by positivity)] at h2
    nlinarith
  have hμ : -(D.hp / 2 + C₁ * D.g) - C₃ * (1 + Real.log (1 + C₁)) * D.g * Real.log Y ≤
      -mean L₁ (fun σ => Real.log (M σ)) := by
    have h1 : C₃ * D.g * Real.log (2 + D.g + (D.hp / 2 + C₁ * D.g)) ≤
        C₃ * D.g * ((1 + Real.log (1 + C₁)) * Real.log Y) :=
      mul_le_mul_of_nonneg_left hbd (by positivity)
    linarith
  have hfin := hC₄ D.g D.hp _ (-mean L (fun σ => Real.log (D.len σ x))) hg1 hh hμ (by
    rw [sub_neg_eq_add]
    exact hslope)
  have hlogY0 : 0 ≤ Real.log Y := by linarith
  calc _ ≤ C₄ * Real.log Y := hfin
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hlogY0

end GlobalTheory.CompanionTheory.Ar.Sl.LineProof
