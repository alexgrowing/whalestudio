import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsAbLift
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimitStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLogPeriodFamilyStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExpLogCoverBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartFactorsThroughStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDvrThroughDiscPointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PolarizedAbelianPartPrincipalStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifPeriodMatrixLeftStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsDerivAt0ZeroOfFixed
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifPeriodMatrixMiddleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifPeriodMatrixRightStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.QuotLoc

theorem exists_pull_form {g g' : ℕ} (ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (Hm : Matrix (Fin g') (Fin g') ℂ) (hH : Hm.IsHermitian) :
    ∃ Hb : Matrix (Fin g) (Fin g) ℂ, Hb.IsHermitian ∧ (∀ x y, x ⬝ᵥ Hb *ᵥ star y = ℓ x ⬝ᵥ Hm *ᵥ star (ℓ y)) ∧
      ∀ y, ℓ y = 0 → Hb *ᵥ star y = 0 := by
  set Lm := LinearMap.toMatrix' ℓ with hLm
  have h1 : ∀ x, Lm *ᵥ x = ℓ x := fun x => LinearMap.toMatrix'_mulVec ℓ x
  have h2 : ∀ y, (Lm.map star) *ᵥ star y = star (ℓ y) := fun y => by
    rw [← h1]
    ext i
    simp [Matrix.mulVec, dotProduct]
  have h3 : ∀ y, (Lmᵀ * Hm * Lm.map star) *ᵥ star y = Lmᵀ *ᵥ (Hm *ᵥ star (ℓ y)) := fun y => by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h2]
  refine ⟨Lmᵀ * Hm * Lm.map star, ?_, fun x y => ?_, fun y hy => ?_⟩
  · have e1 : (Lm.map star)ᴴ = Lmᵀ := by ext i j; simp [Matrix.conjTranspose_apply]
    have e2 : (Lmᵀ)ᴴ = Lm.map star := by ext i j; simp [Matrix.conjTranspose_apply]
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, e1, e2, hH.eq, Matrix.mul_assoc]
  · rw [h3, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, h1]
  · rw [h3, hy]
    simp

theorem eq_of_forall_exp {d e : ℝ} (h : ∀ N : ℕ, 0 < N →
    Complex.exp (-(2 * Real.pi * Complex.I) * (d : ℂ) / N) = Complex.exp (-(2 * Real.pi * Complex.I) * (e : ℂ) / N)) :
    d = e := by
  obtain ⟨N, hN⟩ := exists_nat_gt |d - e|
  have hN0 : 0 < N + 1 := Nat.succ_pos N
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h (N + 1) hN0)
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have hNc : ((N + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
  have h1 : ((d - e : ℝ) : ℂ) = (((-k * (N + 1 : ℕ) : ℤ) : ℝ) : ℂ) := by
    push_cast
    field_simp at hk
    push_cast at hk
    linear_combination -hk
  have h2 : d - e = ((-k * (N + 1 : ℕ) : ℤ) : ℝ) := by exact_mod_cast h1
  by_contra hne
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hne
    simpa [sub_eq_zero] using h2
  have h3 : (N + 1 : ℝ) ≤ |d - e| := by
    rw [h2]
    have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
    have h4 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast this
    push_cast
    rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) + 1)]
    nlinarith [abs_nonneg (k : ℝ), (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  linarith

theorem eq_zero_of_im_lattice {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (Λ : Submodule ℤ (Fin g → ℂ))
    (hfull : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) (p : Fin g → ℂ)
    (h : ∀ q ∈ Λ, (p ⬝ᵥ Hm *ᵥ star q).im = 0) : p = 0 := by
  have key : ∀ w : Fin g → ℂ, (p ⬝ᵥ Hm *ᵥ star w).im = 0 := by
    intro w
    have hw : w ∈ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) := by rw [hfull]; trivial
    induction hw using Submodule.span_induction with
    | mem x hx => exact h x hx
    | zero => simp
    | add x y _ _ hx hy => simp [star_add, Matrix.mulVec_add, dotProduct_add, hx, hy]
    | smul c x _ hx =>
      have e : star (c • x) = (c : ℂ) • star x := by
        ext i; simp
      rw [e, Matrix.mulVec_smul, dotProduct_smul]
      simp [hx]
  by_contra hp
  have h1 := hpos p hp
  have h2 := key (Complex.I • p)
  have e : star (Complex.I • p) = (-Complex.I) • star p := by
    ext i; simp
  rw [e, Matrix.mulVec_smul, dotProduct_smul] at h2
  simp at h2
  linarith

theorem abPart_principal_and_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → ∃ ρ K : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∀ P : AbPart C.t (spMap (C.ψ z)), IsPrincipal P.tB ∧ ∀ (Mz : LieModel C.t.G (spMap (C.ψ z)) (Fin C.g → ℂ)), (∀ i, C.M.Lifts (C.ψ z) (𝟙 _) (Pi.single i 1) (Mz.pt (Pi.single i 1))) → ∀ (x : Fin C.g → ℂ) (v : epsAt (𝟙 (Sp ℂ)) ⟶ P.tK.G) (c : ℂ), v.left ≫ P.m.φ = (Mz.pt x).left → HodgeIP P.tB.G P.tB.PP.L (𝟙 _) (v ≫ P.τ.q ≫ P.e.hom) (v ≫ P.τ.q ≫ P.e.hom) c → c.re ≤ K * ∑ i, ‖x i‖ ^ 2 := by
  intro E _ _ _ H D l Xo σ n a C hpq hσ
  obtain ⟨ρ₀, Λ, _, L, e, hρ0, hρ1, hlink⟩ := GlobalTheory.T.exists_log_period_family E H D l Xo σ n a C hpq hσ
  obtain ⟨ρ₁, Cb, h1, h2, hL⟩ := GlobalTheory.T.log_period_limit n a C.g Λ L
  have hol : Flat.IsHolPts (Metric.ball 0 ρ₀) C.ψ :=
    ⟨Metric.isOpen_ball, fun r => (C.hol.2 r).mono (Metric.ball_subset_ball hρ1)⟩
  have hprin : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ P : AbPart C.t (spMap (C.ψ z)), IsPrincipal P.tB := by
    intro z hz P
    obtain ⟨V, _, _, _, f, r, tV, mV, hV, hr, hker, hrf, hpol⟩ := GlobalTheory.T.exists_dvr_through_disc_point E H D l Xo σ n a C z hz
    have key : ∀ (z₀ : Sp ℂ ⟶ Sp C.R), z₀ = spMap r ≫ spMap f → ∀ P : AbPart C.t z₀, IsPrincipal P.tB := by
      rintro _ rfl P
      obtain ⟨m', -⟩ := GlobalTheory.T.abelian_part_factors_through E H _ _ tV C.t _ mV ℂ (spMap r) P
      exact GlobalTheory.T.polarized_abelian_part_principal E H V r tV hV hr hker hpol ⟨P.tK, m', P.τ, P.tB, P.e, P.e_hom, P.act, P.pp⟩
    refine key _ ?_ P
    rw [← hrf]
    show Spec.map (CommRingCat.ofHom (r.comp f)) = _
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  refine ⟨ρ₀ * ρ₁, Real.pi * Cb, mul_pos hρ0 h1, by nlinarith, ?_⟩
  intro z hz
  obtain ⟨z', hz', rfl⟩ : ∃ z' ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, z = (ρ₀ : ℂ) • z' := by
    refine ⟨(ρ₀⁻¹ : ℂ) • z, ?_, ?_⟩
    · rw [mem_ball_zero_iff] at hz ⊢
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hρ0.le]
      rw [inv_mul_lt_iff₀ hρ0]
      exact hz
    · rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast hρ0.ne'), one_smul]
  have hz1 : z' ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.ball_subset_ball h2 hz'
  have hb : (ρ₀ : ℂ) • z' ∈ Metric.ball (0 : Fin n → ℂ) ρ₀ := by
    rw [mem_ball_zero_iff] at hz1 ⊢
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ0.le]
    nlinarith
  have hb1 : (ρ₀ : ℂ) • z' ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.ball_subset_ball hρ1 hb
  obtain ⟨ws, W, per, hws, hlim, hper, hfour, -, hsix⟩ := hL z' hz'
  obtain ⟨hA, hB, hC⟩ := GlobalTheory.T.family_exp_log_cover_bound E H C.R C.t C.g n a C.M C.ψ ρ₀ e Λ L hρ0 hρ1 hol hlink z' hz1 ws W per hws hlim hper hfour
  intro P
  have hP := hprin _ hb1 P
  refine ⟨hP, ?_⟩
  intro Mz hMz x v c hv hc
  obtain ⟨-, -, -, A, iA, φ, g', u, Hm, χ, v', w', a', b', hφ, hAH, hv', hw', ha', hb', rfl⟩ := hc
  obtain ⟨ℓ, hℓ⟩ := GlobalTheory.T.hol_unif_period_matrix_left E H C.R C.t C.g n C.M _ C.ψ e _ P A iA φ g' u Hm χ hb hφ hAH hP
  have e1 : a' = ℓ x := GlobalTheory.CompanionTheory.Ar.QuotLoc.DiffL.isDiff_eq_lift E H C.R C.t C.g n C.M _ C.ψ e _ P A iA φ g' u Hm χ ℓ hb hφ hAH hP hℓ Mz hMz x v v' a' hv hv' ha'
  have e2 : b' = ℓ x := GlobalTheory.CompanionTheory.Ar.QuotLoc.DiffL.isDiff_eq_lift E H C.R C.t C.g n C.M _ C.ψ e _ P A iA φ g' u Hm χ ℓ hb hφ hAH hP hℓ Mz hMz x v w' b' hv hw' hb'
  obtain ⟨hin, honto⟩ := GlobalTheory.T.hol_unif_period_matrix_right E H C.R C.t C.g n C.M _ C.ψ e _ P A iA φ g' u Hm χ ℓ hb hφ hAH hP hℓ
  obtain ⟨Hb, hH1, hH2, hH3⟩ := exists_pull_form ℓ Hm hAH.1
  have hE : ∀ x x' : W, (per x ⬝ᵥ Hb *ᵥ star (per x')).im = ((L.E x x' : ℤ) : ℝ) := by
    intro x x'
    rw [hH2]
    refine eq_of_forall_exp fun N hN => ?_
    have hw := hC N (Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * ((L.E x x' : ℤ) : ℂ) / N))) x x' hN rfl
    have := GlobalTheory.T.hol_unif_period_matrix_middle E H C.R C.t C.g n C.M _ C.ψ e _ P A iA φ g' u Hm χ ℓ hb hφ hAH hP hℓ N _ (per x) (per x') hN
      (hA x) (hA x') hw
    rw [Units.val_mk0] at this
    have c : (((L.E x x' : ℤ) : ℝ) : ℂ) = ((L.E x x' : ℤ) : ℂ) := by push_cast; rfl
    rw [c]
    exact this.symm
  have hrad : ∀ x : W, (∀ x' : W, L.E x x' = 0) → Hb *ᵥ star (per x) = 0 := by
    intro x hx
    refine hH3 _ (eq_zero_of_im_lattice Hm u.Λ u.full hAH.2.1 _ fun q hq => ?_)
    obtain ⟨y, hy, rfl⟩ := honto q hq
    obtain ⟨x', rfl⟩ := hB y hy
    rw [← hH2, hE, hx]
    simp
  subst e1 e2
  have hbd := (hsix Hb hH1 hE hrad x).2.1
  rw [hH2] at hbd
  have e3 : ((Real.pi : ℂ) * (ℓ x ⬝ᵥ Hm.mulVec (star (ℓ x)))).re = Real.pi * (ℓ x ⬝ᵥ Hm *ᵥ star (ℓ x)).re := by simp
  rw [e3, _root_.mul_assoc]
  exact mul_le_mul_of_nonneg_left hbd Real.pi_pos.le

end GlobalTheory.CompanionTheory.Ar.QuotLoc
