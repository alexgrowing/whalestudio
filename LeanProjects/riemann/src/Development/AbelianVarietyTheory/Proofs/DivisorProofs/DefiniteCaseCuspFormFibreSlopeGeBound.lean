import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyDefiniteRationalPointDataComponentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveDualWeylTensorCuspFormsRationalPoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCoordinatesFormsAndFibreNormBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeDualDetLieEqNegFlatSectionDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLineDegreeGeHalfDetLieDefinitePointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreActionPreservesAdelicMatricesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeDualWeylFibreLatticeGeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeLatticeOfLocalMatrixFamilyStatement

noncomputable section

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

namespace GlobalTheory.DefFibre

theorem vAdd_pow' {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : K) (n : ℕ) :
    vAdd w (x ^ n) = n * vAdd w x := by
  simp [vAdd, map_pow, WithZero.log_pow]

theorem vAdd_one' {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) : vAdd w (1 : K) = 0 := by
  simp [vAdd]

theorem subsingleton_idx : ∀ (N : ℕ) (la : Fin N → ℕ), N = 0 → Subsingleton (Idx la) := by
  rintro N la rfl
  constructor
  rintro ⟨m, -⟩ ⟨m', -⟩
  congr 1
  ext ⟨i, _⟩
  exact i.elim0

theorem dim_eq_one_of_zero {N : ℕ} (la : Fin N → ℕ) (hla : Antitone la) (h : N = 0) : dim la = 1 := by
  haveI := subsingleton_idx N la h
  have h1 := dim_pos hla
  have h2 : dim la ≤ 1 := by rw [dim_eq_card]; exact Fintype.card_le_one_iff_subsingleton.2 inferInstance
  omega

theorem fibreAt_defCase : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (c₁ : ℝ), DefCase U ξ → Dom a n → FlatExistsAt U ξ c₁ →
      ∀ Z : Comp Xo c, FibreAt U ξ Z (wtZ a n) (defBound Dw a n c₁) := by
  intro E _ _ _ H Dw l Xo c r U ξ a n c₁ hD hDom hFl Z
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_definiteRationalPointData_component E H Dw l Xo c r U ξ hD Z
  haveI hTC : IsTotallyComplex c.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => GlobalTheory.CompHt.conj_comp_ne (c := c) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩
  have hanti : ∀ τ, Antitone (part Dw a τ) := fun τ i j hij => hDom.1 τ (show (i : ℕ) ≤ j from hij)
  obtain ⟨φ, hinj, hrange, hreads⟩ := GlobalTheory.T.exists_injective_dualWeylTensor_cuspForms_rationalPoint E H Dw l Xo c r U ξ a n hD hDom Z P
  obtain ⟨hconj, hint⟩ := GlobalTheory.T.integral_coordinates_forms_and_fibre_norm_bound E H Dw l Xo c r U ξ a n hD hDom Z P
  obtain ⟨hlie, -⟩ := GlobalTheory.T.degree_dualDetLie_eq_neg_flatSection_degree E H Dw l Xo c r U ξ hD Z P
  have hth := GlobalTheory.T.thetaLine_degree_ge_half_detLie_definitePoint E H Dw l Xo c r U ξ hD Z P
  have hIntOne : ∀ (w : HeightOneSpectrum (𝓞 c.F)) (m : ℕ), IntAt w (1 : Matrix (Fin m) (Fin m) c.F) :=
    fun w m i j => by by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hBad : ∀ τ, IsAdelic fun w => P.B w τ := fun τ => by
    refine ⟨fun w => (P.loc w).2.1 τ, P.fin.subset fun w hw h => hw ?_⟩
    show IntAt w (P.B w τ) ∧ IntAt w (P.B w τ)⁻¹
    have hB : P.B w τ = 1 := by rw [h.2]; rfl
    rw [hB, inv_one]
    exact ⟨hIntOne w _, hIntOne w _⟩
  have ha0 : ∀ w, P.a w ^ n ≠ 0 := fun w => pow_ne_zero _ (P.loc w).1
  have hsupp1 : (Function.support fun w => vAdd w (P.a w)).Finite :=
    P.fin.subset fun w hw h => hw (by simp only; rw [h.1, vAdd_one'])
  have hsupp : (Function.support fun w => vAdd w (P.a w ^ n)).Finite :=
    hsupp1.subset fun w hw h => hw (by simp only at h ⊢; rw [vAdd_pow', h, mul_zero])
  have hspos : ∀ σ, 0 < (Real.sqrt (P.N σ))⁻¹ ^ n := fun σ =>
    pow_pos (inv_pos.2 (Real.sqrt_pos.2 (P.arch σ).1)) n
  have hsconj : ∀ σ, (Real.sqrt (P.N ((starRingEnd ℂ).comp σ)))⁻¹ ^ n = (Real.sqrt (P.N σ))⁻¹ ^ n := fun σ => by
    rw [(hconj σ).1]
  obtain ⟨hdet, hslope⟩ := GlobalTheory.T.slope_dualWeylFibreLattice_ge c.F (E →+* ℂ) Dw.mult (part Dw a) hanti (fun w => P.a w ^ n) P.B
    (fun σ => (Real.sqrt (P.N σ))⁻¹ ^ n) P.X ha0 hsupp hBad hspos (fun σ τ => (P.arch σ).2.1 τ) hsconj
    (fun σ τ => (hconj σ).2 τ)
  have hlat : IsAdelic fun w => fibA (part Dw a) (P.a w ^ n) (P.B w) :=
    GlobalTheory.T.fibre_action_preserves_adelic_matrices c.F (E →+* ℂ) Dw.mult (part Dw a) (fun w => P.a w ^ n) P.B ha0 hsupp hBad
  have hsec : ∀ x, φ x ∈ sec Xo c a n := fun x => by
    have h1 : φ x ∈ cuspOn U Z (wtZ a n) := hrange ▸ ⟨x, rfl⟩
    have h2 := cuspOn_le U Z (wtZ a n) h1
    rw [cuspW_wtZ] at h2
    exact cusp_le_sec Xo c U a n h2
  have hne : ∀ τ, Nonempty (Idx (part Dw a τ)) := fun τ =>
    Fintype.card_pos_iff.1 ((dim_eq_card _) ▸ dim_pos (hanti τ))

  have hline : lineDeg (fun σ => (Real.sqrt (P.N σ))⁻¹ ^ n) (fun w => (vAdd w (P.a w ^ n) : ℝ)) = n * P.degTh := by
    simp only [PtData.degTh, lineDeg, vAdd_pow', Int.cast_mul, Int.cast_natCast, Real.log_pow]
    have hf := fin_mul (ρ := fun w => (vAdd w (P.a w) : ℝ)) (hsupp1.subset fun w hw => by simpa [Function.mem_support] using hw) (lw c.F)
    simp only [mul_assoc]
    rw [← mul_finsum, ← Finset.mul_sum]
    ring

  have hterm : ∀ τ : E →+* ℂ, ¬ τ (H.rt : E) = H.rt0 →
      (size (part Dw a τ) : ℝ) / (Dw.mult τ : ℝ) * detDeg (fun w => P.B w τ) (fun σ => P.X σ τ) -
        Real.log (dim (part Dw a τ)) / 2 = 0 := fun τ hτ => by
    have hm : Dw.mult τ = 0 := by simp [Datum.mult, hτ, hD.q]
    have hm' : (Dw.mult τ : ℝ) = 0 := by rw [hm]; simp
    rw [dim_eq_one_of_zero _ (hanti τ) hm, hm', div_zero, zero_mul]
    simp
  have hpsi : ∀ τ : Psi H,
      (size (part Dw a τ.1) : ℝ) / (Dw.mult τ.1 : ℝ) * detDeg (fun w => P.B w τ.1) (fun σ => P.X σ τ.1) -
        Real.log (dim (part Dw a τ.1)) / 2 =
      (size (part Dw a τ.1) : ℝ) / (Dw.p : ℝ) * c₁ - Real.log (dim (part Dw a τ.1)) / 2 := fun τ => by
    have hm : Dw.mult τ.1 = Dw.p := by simp [Datum.mult, τ.2]
    have hl : P.degLie τ.1 = c₁ := by
      obtain ⟨s⟩ := (hFl Z τ).1
      rw [hlie τ s, (hFl Z τ).2 s, neg_neg]
    have hm' : (Dw.mult τ.1 : ℝ) = Dw.p := by rw [hm]
    rw [hm', show detDeg (fun w => P.B w τ.1) (fun σ => P.X σ τ.1) = P.degLie τ.1 from rfl, hl]
  have hsum := (Fintype.sum_subtype_add_sum_subtype (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)
    (fun τ => (size (part Dw a τ) : ℝ) / (Dw.mult τ : ℝ) * detDeg (fun w => P.B w τ) (fun σ => P.X σ τ) -
        Real.log (dim (part Dw a τ)) / 2)).symm
  have h0 : ∑ τ : {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0}, ((size (part Dw a τ.1) : ℝ) / (Dw.mult τ.1 : ℝ) *
      detDeg (fun w => P.B w τ.1) (fun σ => P.X σ τ.1) - Real.log (dim (part Dw a τ.1)) / 2) = 0 :=
    Finset.sum_eq_zero fun τ _ => hterm τ.1 τ.2
  rw [h0, add_zero] at hsum
  have hsum' : ∑ τ : Psi H, ((size (part Dw a τ.1) : ℝ) / (Dw.mult τ.1 : ℝ) *
      detDeg (fun w => P.B w τ.1) (fun σ => P.X σ τ.1) - Real.log (dim (part Dw a τ.1)) / 2) =
      ∑ τ : Psi H, ((size (part Dw a τ.1) : ℝ) / (Dw.p : ℝ) * c₁ - Real.log (dim (part Dw a τ.1)) / 2) :=
    Finset.sum_congr rfl fun τ _ => hpsi τ
  have hlieSum : ∑ τ : Psi H, P.degLie τ.1 = (Fintype.card (Psi H) : ℝ) * c₁ := by
    rw [Finset.sum_congr rfl fun τ _ => (show P.degLie τ.1 = c₁ by
      obtain ⟨s⟩ := (hFl Z τ).1
      rw [hlie τ s, (hFl Z τ).2 s, neg_neg]), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hbound : defBound Dw a n c₁ = ∑ τ : Psi H, ((size (part Dw a τ.1) : ℝ) / (Dw.p : ℝ) * c₁ -
      Real.log (dim (part Dw a τ.1)) / 2) + (Fintype.card (Psi H) : ℝ) * ((n : ℝ) / 2 * c₁) +
      (n : ℝ) * ((Fintype.card (Psi H) : ℝ) * Dw.p) * (Real.log (2 * Real.pi) / 4 - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E / 2) := by
    have hS : ∑ τ : Psi H, ((((size (part Dw a τ.1) : ℝ) / (Dw.p : ℝ) + (n : ℝ) / 2) * c₁ -
        Real.log (dim (part Dw a τ.1)) / 2)) = ∑ τ : Psi H, ((size (part Dw a τ.1) : ℝ) / (Dw.p : ℝ) * c₁ -
        Real.log (dim (part Dw a τ.1)) / 2) + ∑ _τ : Psi H, ((n : ℝ) / 2 * c₁) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun τ _ => by ring
    rw [defBound, hS, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hmul := mul_le_mul_of_nonneg_left hth hn
  rw [hlieSum] at hmul
  refine ⟨TIdx (part Dw a), inferInstance, inferInstance, ⟨fun τ => (hne τ).some⟩, locLat (P.matA a n), P.matY a n, φ,
    GlobalTheory.T.isLattice_latticeOfLocalMatrixFamily c.F _ (P.matA a n) hlat, hdet, ?_, hinj, hrange, fun x hx w v hv =>
      (hint x (φ x) (hsec x) (hreads x)).1 hx w v hv, fun σ x z hz => (hint x (φ x) (hsec x) (hreads x)).2 σ z hz⟩
  refine le_trans ?_ hslope
  have htot : ∑ t : E →+* ℂ, ((size (part Dw a t) : ℝ) / (Dw.mult t : ℝ) *
      detDeg (fun w => P.B w t) (fun σ => P.X σ t) - Real.log (dim (part Dw a t)) / 2) =
      ∑ τ : Psi H, ((size (part Dw a τ.1) : ℝ) / (Dw.p : ℝ) * c₁ - Real.log (dim (part Dw a τ.1)) / 2) := by
    rw [hsum]
    convert hsum' using 3
  rw [hline, htot, hbound]
  nlinarith [hmul]

end GlobalTheory.DefFibre
