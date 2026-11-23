import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannFormPeriodDeterminantBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianPeriodLinearAlgebra
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformisedEigenFrameOneStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsDerivAt0CompLinMap
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodHermitianTypeCompatibility
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodEigenFrameStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

open Matrix GlobalTheory.CompanionTheory.Ar.LinFlat
open scoped ComplexOrder

local notation "HF" => ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm

theorem det_rows_mul_det_rows {p q : ℕ} (A C : Matrix (Fin p) (Fin q ⊕ Fin p) ℂ)
    (F : Matrix (Fin q) (Fin q ⊕ Fin p) ℂ) (hAF : A * Fᵀ = 0) (hAC : A * Cᵀ = 1) :
    (fromRows (Fᵀ)ᴴ A).det * (fromRows F C).det = ((Fᵀ)ᴴ * Fᵀ).det := by
  have h : fromRows (Fᵀ)ᴴ A * (fromRows F C)ᵀ = fromBlocks ((Fᵀ)ᴴ * Fᵀ) ((Fᵀ)ᴴ * Cᵀ) 0 1 := by
    rw [transpose_fromRows, fromRows_mul_fromCols, hAF, hAC]
  rw [← det_transpose (fromRows F C), ← det_mul, h, det_fromBlocks_zero₂₁]
  simp

theorem norm_core {p q g : ℕ} (V : Fin p → Fin g → ℂ) (W : Fin q → Fin g → ℂ)
    (U U' : Fin p ⊕ Fin q → Fin g → ℂ) (S : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (HF Hm z z).re) (hS : S.det ≠ 0)
    (hV : LinearIndependent ℂ V) (hW : LinearIndependent ℂ W)
    (hU : ∀ n, U n ∈ Submodule.span ℂ (Set.range V))
    (C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ) (Fm B : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ)
    (hB : ∀ n, U' n = ∑ j, B j n • W j) (hFm : ∀ j n, ∑ m, Fm j m * S m n = B j n)
    (hC : ∀ a, ∑ m, C a m • U m = V a)
    (hR : ∀ m n, HF Hm (U m) (U n) - star (HF Hm (U' m) (U' n)) = 2 * Complex.I * S m n)
    (Γ : Matrix (Fin p) (Fin p) ℂ) (Δ : Matrix (Fin q) (Fin q) ℂ)
    (hΓ : ∀ a b, Γ a b = Real.pi * HF Hm (V a) (V b))
    (hΔ : ∀ a b, Δ a b = Real.pi * HF Hm (W a) (W b)) :
    ‖Γ.det‖ = ‖(fromRows C Fm).det‖ ^ 2 *
      ((2 * Real.pi) ^ p * (2 * Real.pi)⁻¹ ^ q * ‖S.det‖) * ‖Δ.det‖ := by
  choose a ha using fun n => (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hU n)
  let A : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ := Matrix.of fun i n => a n i
  have hA : ∀ n, ∑ i, A i n • V i = U n := ha
  clear_value A
  set H₁ : Matrix (Fin p) (Fin p) ℂ := Matrix.of fun i j => HF Hm (V i) (V j) with hH₁
  set H₂ : Matrix (Fin q) (Fin q) ℂ := Matrix.of fun i j => HF Hm (W i) (W j) with hH₂
  have pd₁ : H₁.PosDef := gram_posDef Hm hH hpos V hV
  have pd₂ : H₂.PosDef := gram_posDef Hm hH hpos W hW
  have hrel : Aᵀ * H₁ * A.map star - (Bᵀ * H₂ * B.map star)ᵀ = (2 * Complex.I) • S := by
    ext m n
    rw [Matrix.sub_apply, Matrix.transpose_apply, gram_expand, gram_expand, hA, hA, ← hB, ← hB,
      ← star_hermForm hH (U' m) (U' n), hR m n]
    simp
  let e : Fin q ⊕ Fin p ≃ Fin p ⊕ Fin q := Equiv.sumComm _ _
  have hrel' : (A.submatrix id e)ᵀ * H₁ * (A.submatrix id e).map star -
      ((B.submatrix id e)ᵀ * H₂ * (B.submatrix id e).map star)ᵀ =
      (2 * Complex.I) • S.submatrix e e := by
    ext m n
    have := congrFun (congrFun hrel (e m)) (e n)
    simpa [Matrix.mul_apply] using this
  have hdet : (S.submatrix e e).det ≠ 0 := by rwa [Matrix.det_submatrix_equiv_self]
  obtain ⟨t₁, -, -, t₄⟩ := GlobalTheory.T.riemann_form_period_determinant p q (A.submatrix id e) (B.submatrix id e)
    (S.submatrix e e) H₁ H₂ pd₁ pd₂ hdet hrel'
  have hFS : Fm * S = B := by
    ext j n
    rw [Matrix.mul_apply, hFm]
  have hN : ((S.submatrix e e)ᵀ)⁻¹ * (B.submatrix id e)ᵀ = (Fm.submatrix id e)ᵀ := by
    have h1 : B.submatrix id e = Fm.submatrix id e * S.submatrix e e := by
      rw [Matrix.submatrix_mul_equiv, hFS]
    have hu : IsUnit ((S.submatrix e e)ᵀ).det := by
      rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.mpr hdet
    rw [h1, Matrix.transpose_mul, Matrix.nonsing_inv_mul_cancel_left _ _ hu]
  rw [hN] at t₁ t₄
  have hCA : C * Aᵀ = 1 := by
    ext i k
    have hexp : ∑ m, C i m • U m = ∑ k, (C * Aᵀ) i k • V k := by
      simp_rw [← hA, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.mul_apply, Finset.sum_smul]
      rfl
    have := coef_unique hV (fun k => (C * Aᵀ) i k) (fun k => (1 : Matrix _ _ ℂ) i k)
      (by rw [← hexp, hC i]; simp [Matrix.one_apply])
    exact congrFun this k
  have hAC : A.submatrix id e * (C.submatrix id e)ᵀ = 1 := by
    have h1 : C.submatrix id e * (A.submatrix id e)ᵀ = 1 := by
      rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, hCA]
      simp
    have := congrArg Matrix.transpose h1
    simpa [Matrix.transpose_mul] using this
  have hG : (fromRows (Fm.submatrix id e) (C.submatrix id e)).det = (fromRows C Fm).det := by
    have : fromRows (Fm.submatrix id e) (C.submatrix id e) = (fromRows C Fm).submatrix e e := by
      ext (i | i) n <;> simp [e]
    rw [this, Matrix.det_submatrix_equiv_self]
  have hmul := det_rows_mul_det_rows _ _ _ t₁ hAC
  rw [hG] at hmul
  set d := (fromRows C Fm).det with hd
  set X := (((Fm.submatrix id e)ᵀ)ᴴ * (Fm.submatrix id e)ᵀ).det with hX
  set M := (fromRows ((Fm.submatrix id e)ᵀ)ᴴ (A.submatrix id e)).det with hM
  have hSd : ‖(S.submatrix e e).det‖ = ‖S.det‖ := by rw [Matrix.det_submatrix_equiv_self]
  rw [hSd] at t₄
  have p₁ : 0 < H₁.det := pd₁.det_pos
  have p₂ : 0 < H₂.det := pd₂.det_pos
  have r₁ : 0 < H₁.det.re := (Complex.pos_iff.mp p₁).1
  have r₂ : 0 < H₂.det.re := (Complex.pos_iff.mp p₂).1
  have n₁ : ‖H₁.det‖ = H₁.det.re := by
    rw [← Complex.abs_re_eq_norm.mpr (Complex.pos_iff.mp p₁).2.symm, abs_of_pos r₁]
  have n₂ : ‖H₂.det‖ = H₂.det.re := by
    rw [← Complex.abs_re_eq_norm.mpr (Complex.pos_iff.mp p₂).2.symm, abs_of_pos r₂]
  have hSp : 0 < ‖S.det‖ := norm_pos_iff.mpr hS
  have hc : 0 < (2 : ℝ) ^ p * (2 : ℝ)⁻¹ ^ q * ‖S.det‖ * H₂.det.re := by positivity
  have hXne : X ≠ 0 := by
    intro h0
    rw [h0, div_zero, norm_zero] at t₄
    have h00 : (2 : ℝ) ^ p * (2 : ℝ)⁻¹ ^ q * ‖S.det‖ * H₂.det.re = 0 := by rw [← t₄]; simp
    exact hc.ne' h00
  have hdne : d ≠ 0 := fun h0 => hXne (by rw [← hmul, h0, mul_zero])
  have hq : M / X = d⁻¹ := by
    have hMne : M ≠ 0 := fun h0 => hXne (by rw [← hmul, h0, zero_mul])
    rw [← hmul]
    field_simp
  have hΓ' : Γ = (Real.pi : ℂ) • H₁ := by ext a b; simp [hΓ, hH₁]
  have hΔ' : Δ = (Real.pi : ℂ) • H₂ := by ext a b; simp [hΔ, hH₂]
  have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by simp [abs_of_pos Real.pi_pos]
  rw [hΓ', hΔ', Matrix.det_smul, Matrix.det_smul, norm_mul, norm_mul, norm_pow, norm_pow, hpi, n₁, n₂]
  simp only [Fintype.card_fin]
  rw [hq, norm_inv] at t₄
  have hdn : 0 < ‖d‖ := norm_pos_iff.mpr hdne
  have t₅ : H₁.det.re = ‖d‖ ^ 2 * (2 ^ p * (2 : ℝ)⁻¹ ^ q * ‖S.det‖ * H₂.det.re) := by
    rw [← t₄]; field_simp
  rw [t₅, mul_pow, inv_pow, inv_pow, mul_pow]
  have := Real.pi_pos
  field_simp

theorem hodgeNorm_flat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ τ' : E →+* ℂ) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H D.p D.q ty → τ' (H.rt : E) = H.rt0 → (∀ a : 𝓞 E, σ (tauIn c τ a) = τ' (a : E)) → ∀ (i : Fin FU.n) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La), LinearIndependent (𝓞 E) e → ∃ t : ℝ, 0 < t ∧ ∀ (ρ : ℂ) (Φ : CFn Xo c), IsFlatAn Set.univ τ τ' σ Φ FU i e ρ → ∀ (P : (FU.Di i).La →+ (Fin g → ℂ)) (y : Sp ℂ ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q) (Γ : Matrix (Fin D.p) (Fin D.p) ℂ) (Δ : Matrix (Fin D.q) (Fin D.q) ℂ), IsPeriod (FU.Di i) ty P → under y = FU.u i P → IsFramed Set.univ τ σ y v w → IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y) v Γ → IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y) w Δ → ‖Φ y v w‖ ^ 2 * ‖Γ.det‖ = ‖ρ‖ ^ 2 * t * ‖Δ.det‖ := by
  intro E _ _ _ H D l Xo c τ τ' σ g ty FU hty hrt hτ i e he
  let S : Matrix (Fin D.p ⊕ Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ :=
    Matrix.of fun m n => τ' (sesq (FU.Di i) (e m) (e n))
  have hSne : ∀ P : (FU.Di i).La →+ (Fin g → ℂ), IsPeriod (FU.Di i) ty P → S.det ≠ 0 := by
    intro P hP
    obtain ⟨Hm, hHh, -, hHi⟩ := id hP.2.2.2.2
    obtain ⟨-, -, hd⟩ := GlobalTheory.CompanionTheory.Ar.Flat.riemann_tau_component E H (FU.Di i) g ty P Hm hP hHh hHi
    have hcard : Fintype.card (Fin D.p ⊕ Fin D.q) = (FU.Di i).p + (FU.Di i).q := by
      rw [(FU.sig i).1, (FU.sig i).2]; simp
    have := hd 0 _ e hcard he
    have h2 : S = (Matrix.of fun m n => sesq (FU.Di i) (e m) (e n)).map τ' := rfl
    rw [h2, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero τ').2 this
  by_cases hS0 : S.det = 0
  · refine ⟨1, one_pos, ?_⟩
    intro ρ Φ _ P y v w Γ Δ hP
    exact absurd hS0 (hSne P hP)
  refine ⟨(2 * Real.pi) ^ D.p * (2 * Real.pi)⁻¹ ^ D.q * ‖S.det‖, ?_, ?_⟩
  · have := norm_pos_iff.mpr hS0
    have := Real.pi_pos
    positivity
  intro ρ Φ hΦ P y v w Γ Δ hP hy hfr hΓ hΔ
  obtain ⟨⟨V₀, W₀, Fm, B, d⟩, ⟨k1, k2, k3, k4, -, ⟨C, k6⟩, k7⟩, -⟩ :=
    GlobalTheory.T.uniformised_eigen_frame_one E H D l Xo c τ τ' σ g ty FU hty hrt hτ i e P y v w he hP hy hfr
  simp only at k1 k2 k3 k4 k6 k7
  have hflat : Φ y v w * (Matrix.fromRows C Fm).det = ρ :=
    hΦ P y v w V₀ W₀ C Fm B hP hy hfr k1 k2 k6 k3 k4
  obtain ⟨-, -, hv, hw⟩ := id hfr
  have hc : ∀ a : 𝓞 E, (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) a = ComplexEmbedding.conjugate τ' (a : E) := by
    intro a
    have h1 : tauIn c (ComplexEmbedding.conjugate τ) a = tauIn c τ (H.bar a) := by
      apply Subtype.ext
      show ComplexEmbedding.conjugate τ (a : E) = τ ((H.bar a : 𝓞 E) : E)
      rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]
      rfl
    show σ (tauIn c (ComplexEmbedding.conjugate τ) a) = _
    rw [h1, hτ, H.bar_eq, IsCMField.complexEmbedding_complexConj]
    rfl
  obtain ⟨V, hVd, hVl, hVs⟩ := GlobalTheory.T.period_eigen_frame E H D l Xo _ g ty FU i P (under y) (σ.comp (tauIn c τ)) τ' D.p v hP hy hτ hv
  obtain ⟨W, hWd, hWl, -⟩ := GlobalTheory.T.period_eigen_frame E H D l Xo _ g ty FU i P (under y) _ (ComplexEmbedding.conjugate τ') D.q w hP hy hc hw
  have eV : V₀ = V := funext fun a => (hVd a _).1 (k1 a)
  have eW : W₀ = W := funext fun a => (hWd a _).1 (k2 a)
  subst eV eW
  obtain ⟨Hm, hHh, hHp, hHi⟩ := id hP.2.2.2.2
  obtain ⟨-, hs, -⟩ := GlobalTheory.CompanionTheory.Ar.Flat.riemann_tau_component E H (FU.Di i) g ty P Hm hP hHh hHi
  have hΓ' := (GlobalTheory.CompanionTheory.Ar.Flat.hodgeGram_iff_period E H D l Xo _ g ty FU i P Hm hP hHh hHi (under y) hy D.p v V₀ Γ k1).1 hΓ
  have hΔ' := (GlobalTheory.CompanionTheory.Ar.Flat.hodgeGram_iff_period E H D l Xo _ g ty FU i P Hm hP hHh hHi (under y) hy D.q w W₀ Δ k2).1 hΔ
  have hlin : IsLinearMap ℂ (tyPart ty τ') := by
    constructor
    · intro a b; funext k; simp only [tyPart, Pi.add_apply]; split_ifs <;> simp
    · intro a b; funext k; simp only [tyPart, Pi.smul_apply]; split_ifs <;> simp
  have hC : ∀ a, ∑ m, C a m • tyPart ty τ' (P (e m)) = V₀ a := by
    intro a
    rw [← k6 a]
    have := map_sum (hlin.mk' _) (fun m => C a m • P (e m)) Finset.univ
    simpa [hlin.map_smul] using this.symm
  have key := norm_core V₀ W₀ (fun n => tyPart ty τ' (P (e n)))
    (fun n => tyPart ty (ComplexEmbedding.conjugate τ') (P (e n))) S Hm hHh hHp hS0 hVl hWl
    (fun n => hVs _) C Fm B k3 k4 hC (fun m n => hs τ' _ _) Γ Δ hΓ' hΔ'
  rw [key, ← hflat, norm_mul]
  ring

end GlobalTheory.CompanionTheory.Ar.Flat
