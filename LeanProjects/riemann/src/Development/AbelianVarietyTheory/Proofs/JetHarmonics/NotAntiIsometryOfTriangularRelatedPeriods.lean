import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryOfSabMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointMoveCalculus
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsUnitGramFrameBorelChange
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CabsDiagEqOne
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.UnitFramesGeneratorRatioModulusOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicIndexSums
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IntegralBasisReduction

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.AntiIsom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def hermL (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (y : Fin r → ℂ) : (Fin r → ℂ) →ₗ[ℂ] ℂ where
  toFun w := hermC τ G w y
  map_add' u v := by simp [hermC, add_mul, Finset.sum_add_distrib]
  map_smul' c v := by simp [hermC, Finset.mul_sum, mul_assoc]

open NumberField AlgebraicGeometry CategoryTheory in
open scoped Matrix in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private theorem exists_emb_not_mem_conjEmb_mem_Ψ (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) :
    ∃ σ τ : E →+* ℂ, σ ∉ X.Ψ ∧ τ ∈ X.Ψ ∧ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb σ = τ := by
  have hconj : ∀ σ : E →+* ℂ, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb σ = ComplexEmbedding.conjugate σ := fun σ => by
    ext t; simp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb, ComplexEmbedding.conjugate_coe_eq]
  obtain ⟨ρ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases hρ : ρ ∈ X.Ψ
  · refine ⟨ComplexEmbedding.conjugate ρ, ρ, (X.cmType ρ).1 hρ, hρ, ?_⟩
    ext t
    simp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb, ComplexEmbedding.conjugate_coe_eq]
  · refine ⟨ρ, _, hρ, ?_, rfl⟩
    rw [hconj]
    by_contra h
    exact hρ ((X.cmType ρ).2 h)

open NumberField AlgebraicGeometry CategoryTheory in
open scoped Matrix in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private theorem hermC_self_re_eq_neg_sum_normSq_of_p0_eq_zero (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (h0 : X.p0 = 0) (τ : X.Ψ) :
    ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧ ∀ p : Fin r → ℂ,
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (↑τ) X.Gm p p).re = -∑ a, Complex.normSq ((P⁻¹ *ᵥ p) a) := by
  obtain ⟨P, hP, hG⟩ := X.signature τ
  refine ⟨P, hP, fun p => ?_⟩
  rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.IntegralBasisReduction.hermC_normal X hP _ hG p p]
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, h0, mul_assoc, Complex.mul_conj, Complex.re_sum]

open NumberField AlgebraicGeometry CategoryTheory in
open scoped Matrix in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private theorem hermC_col_emb_eq_of_not_mem_Ψ (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (v : Fin r → E)
    {σ τ : E →+* ℂ} (hσ : σ ∉ X.Ψ) (hτ : τ ∈ X.Ψ) (hστ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb σ = τ) (i : ℕ)
    (hi : X.p0 - 1 - i < r) :
    _root_.Formalism.L2.PjFree.perFr X x v σ i =
      _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x ⟨τ, hτ⟩) ⟨X.p0 - 1 - i, hi⟩) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v) := by
  subst hστ
  unfold _root_.Formalism.L2.PjFree.perFr
  rw [dif_neg hσ, dif_pos hτ, dif_pos hi]

open NumberField AlgebraicGeometry CategoryTheory in
open scoped Matrix in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private theorem hermC_first_col_self_re_pos (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom)
    (τ : X.Ψ) (hp : 0 < X.p0) (hr : 0 < r) :
    0 < (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) ⟨0, hr⟩)
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) ⟨0, hr⟩)).re := by
  have hx' : x ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.GG X.Ψ X.Gm X.p0 := hx
  have h := (hx' τ).2 ⟨1, by omega⟩
  have h1 : _root_.ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 1 = 1 := by simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.psgn, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, hp]
  simp only [h1, one_mul] at h
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin, _root_.ReciprocityTheory.ChartRestriction.G.FD.lminor, _root_.ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.det_fin_one] at h
  exact h

open NumberField AlgebraicGeometry CategoryTheory in
open scoped Matrix in
open scoped ComplexConjugate in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in

theorem _root_.GlobalTheory.AntiIsom.not_antiIsometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), X.Ψ = X'.Ψ → X.p0 = X'.p0 → 1 ≤ r → ∀ (a : GL (Fin r) E), (∀ u v, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X'.Gm ((a : Matrix (Fin r) (Fin r) E) *ᵥ u) ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) = -1 * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v) → ∀ (m : (E →+* ℂ) → ℕ), (∀ τ ∈ X.Ψ, m τ = r - X.p0) → (∀ τ ∉ X.Ψ, m τ = X.p0) → ∀ x ∈ X.dom, ∀ x' ∈ X'.dom, ∀ (A : (E →+* ℂ) → ℕ → ℕ → ℂ), (∀ τ i j, j < i → A τ i j = 0) → (∀ τ, ∀ i < m τ, ∀ v ∈ X.Λ, _root_.Formalism.L2.PjFree.perFr X' x' ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i = ∑ j ∈ Finset.range (m τ), A τ i j * _root_.Formalism.L2.PjFree.perFr X x v τ j) → False := by
  intro E _ _ _ r X X' hΨ hp r1 a ha m _ hmout x hx x' hx' A hA hrel
  have hr : 0 < r := r1
  have hiso : ∀ (τ : E →+* ℂ) (u v : Fin r → ℂ),
      _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ X'.Gm (((a : Matrix (Fin r) (Fin r) E).map τ) *ᵥ u)
        (((a : Matrix (Fin r) (Fin r) E).map τ) *ᵥ v) = -_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ X.Gm u v := by
    intro τ u v
    have h := _root_.GlobalTheory.LevelCusp.hermC_of_herm (ε := -1) ha τ u v
    simpa using h
  obtain ⟨σ, τ, hσ, hτ, hστ⟩ := exists_emb_not_mem_conjEmb_mem_Ψ X
  have hτ' : τ ∈ X'.Ψ := hΨ ▸ hτ
  have hσ' : σ ∉ X'.Ψ := hΨ ▸ hσ
  rcases Nat.eq_zero_or_pos X.p0 with h0 | hp0
  · obtain ⟨P, hP, hPf⟩ := hermC_self_re_eq_neg_sum_normSq_of_p0_eq_zero X h0 ⟨τ, hτ⟩
    obtain ⟨P', _, hPf'⟩ := hermC_self_re_eq_neg_sum_normSq_of_p0_eq_zero X' (hp ▸ h0) ⟨τ, hτ'⟩
    let p : Fin r → ℂ := Pi.single ⟨0, hr⟩ 1
    have e1 := hPf p
    have e2 := hPf' ((a : Matrix (Fin r) (Fin r) E).map τ *ᵥ p)
    simp only at e1 e2
    rw [hiso, Complex.neg_re, e1] at e2
    have s1 : 0 ≤ ∑ i, Complex.normSq ((P⁻¹ *ᵥ p) i) :=
      Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
    have s2 : 0 ≤ ∑ i, Complex.normSq ((P'⁻¹ *ᵥ ((a : Matrix (Fin r) (Fin r) E).map τ *ᵥ p)) i) :=
      Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
    have hzero : ∑ i, Complex.normSq ((P⁻¹ *ᵥ p) i) = 0 := by linarith
    have hw : P⁻¹ *ᵥ p = 0 := by
      funext i
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg _)).1
        hzero i (Finset.mem_univ _)
      simpa using h
    have hu : IsUnit P.det := isUnit_iff_ne_zero.2 hP
    have hp0 : p = 0 := by
      calc p = (P * P⁻¹) *ᵥ p := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
        _ = 0 := by rw [← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]
    have h := congrFun hp0 ⟨0, hr⟩
    simp [p] at h
  · have hi : X.p0 - 1 - (X.p0 - 1) < r := by omega
    have hi' : X'.p0 - 1 - (X.p0 - 1) < r := by omega
    have hlat : ∀ v ∈ X.Λ,
        _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ X'.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x' ⟨τ, hτ'⟩) ⟨0, hr⟩)
          ((a : Matrix (Fin r) (Fin r) E).map τ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v) =
        A σ (X.p0 - 1) (X.p0 - 1) *
          _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x ⟨τ, hτ⟩) ⟨0, hr⟩) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v) := by
      intro v hv
      have h := hrel σ (X.p0 - 1) (by rw [hmout σ hσ]; omega) v hv
      rw [hmout σ hσ, Finset.sum_eq_single (X.p0 - 1)] at h
      · rw [hermC_col_emb_eq_of_not_mem_Ψ X' x' _ hσ' hτ' hστ _ hi', hermC_col_emb_eq_of_not_mem_Ψ X x v hσ hτ hστ _ hi] at h
        have e1 : (⟨X.p0 - 1 - (X.p0 - 1), hi⟩ : Fin r) = ⟨0, hr⟩ := Fin.ext (by simp)
        have e2 : (⟨X'.p0 - 1 - (X.p0 - 1), hi'⟩ : Fin r) = ⟨0, hr⟩ := Fin.ext (by simp; omega)
        have emb_mul : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) =
            (a : Matrix (Fin r) (Fin r) E).map τ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v := by
          funext k
          exact RingHom.map_mulVec τ (a : Matrix (Fin r) (Fin r) E) v k
        rw [e1, e2, emb_mul] at h
        exact h
      · intro j hj hne
        rw [hA σ _ _ (by simp at hj; omega), zero_mul]
      · intro h
        simp at h
        omega
    have emb_add : ∀ v w : Fin r → E,
        _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ (v + w) = _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v + _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ w := by
      intro v w; funext k; simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb]
    have emb_smul : ∀ (e : E) (v : Fin r → E),
        _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ (e • v) = τ e • _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v := by
      intro e v; funext k; simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb]
    have hE : ∀ v : Fin r → E,
        _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ X'.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x' ⟨τ, hτ'⟩) ⟨0, hr⟩)
          ((a : Matrix (Fin r) (Fin r) E).map τ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v) =
        A σ (X.p0 - 1) (X.p0 - 1) *
          _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x ⟨τ, hτ⟩) ⟨0, hr⟩) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v) := by
      intro v
      have hv : v ∈ Submodule.span E (X.Λ : Set (Fin r → E)) := by
        rw [X.Λ_span]; trivial
      induction hv using Submodule.span_induction with
      | mem v hv => exact hlat v hv
      | zero =>
        have h0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ (0 : Fin r → E) = (0 : ℂ) • _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ 0 := by
          funext k; simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb]
        rw [h0, Matrix.mulVec_smul, _root_.ReciprocityTheory.ChartRestriction.G.FD.hC_smul_right, _root_.ReciprocityTheory.ChartRestriction.G.FD.hC_smul_right]
        simp
      | add v w _ _ h1 h2 =>
        rw [emb_add, Matrix.mulVec_add, _root_.ReciprocityTheory.ChartRestriction.G.FD.hC_add_right, _root_.ReciprocityTheory.ChartRestriction.G.FD.hC_add_right, h1, h2, mul_add]
      | smul e v _ h =>
        rw [emb_smul, Matrix.mulVec_smul, _root_.ReciprocityTheory.ChartRestriction.G.FD.hC_smul_right, _root_.ReciprocityTheory.ChartRestriction.G.FD.hC_smul_right, h]
        ring
    have hC : ∀ z : Fin r → ℂ,
        _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ X'.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x' ⟨τ, hτ'⟩) ⟨0, hr⟩)
          ((a : Matrix (Fin r) (Fin r) E).map τ *ᵥ z) =
        A σ (X.p0 - 1) (X.p0 - 1) *
          _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x ⟨τ, hτ⟩) ⟨0, hr⟩) z := by
      intro z
      rw [pi_eq_sum_univ z, Matrix.mulVec_sum, _root_.ReciprocityTheory.ChartRestriction.G.FD.IsotropicIndexSums.hC_sum_right, _root_.ReciprocityTheory.ChartRestriction.G.FD.IsotropicIndexSums.hC_sum_right, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.mulVec_smul, _root_.ReciprocityTheory.ChartRestriction.G.FD.hC_smul_right, _root_.ReciprocityTheory.ChartRestriction.G.FD.hC_smul_right]
      have h := hE (Pi.single k 1)
      have hs : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ (Pi.single k (1 : E)) = fun j => if k = j then (1 : ℂ) else 0 := by
        funext j
        by_cases hkj : k = j
        · subst hkj; simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb]
        · simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb, Pi.single_apply, hkj, Ne.symm hkj]
      rw [hs] at h
      rw [h]
      ring
    obtain ⟨u, hu⟩ : ∃ u, (a : Matrix (Fin r) (Fin r) E).map τ *ᵥ u =
        _root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x' ⟨τ, hτ'⟩) ⟨0, hr⟩ := by
      refine ⟨((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ *ᵥ
        _root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x' ⟨τ, hτ'⟩) ⟨0, hr⟩, ?_⟩
      rw [Matrix.mulVec_mulVec, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul,
        Units.mul_inv, map_one, Matrix.one_mulVec]
    have k1 := hC (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x ⟨τ, hτ⟩) ⟨0, hr⟩)
    have k2 := hiso τ u (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x ⟨τ, hτ⟩) ⟨0, hr⟩)
    rw [hu] at k2
    have k3 := hC u
    rw [hu] at k3
    have k4 := _root_.ReciprocityTheory.ChartRestriction.G.FD.hC_symm τ X.Gm X.Gm_herm u (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x ⟨τ, hτ⟩) ⟨0, hr⟩)
    have k5 : _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ X.Gm u (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x ⟨τ, hτ⟩) ⟨0, hr⟩) =
        -(A σ (X.p0 - 1) (X.p0 - 1) * _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x ⟨τ, hτ⟩) ⟨0, hr⟩)
          (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x ⟨τ, hτ⟩) ⟨0, hr⟩)) := by
      linear_combination k2 - k1
    rw [k4, k5] at k3
    have hd := hermC_first_col_self_re_pos X hx ⟨τ, hτ⟩ hp0 hr
    have hd' := hermC_first_col_self_re_pos X' hx' ⟨τ, hτ'⟩ (hp ▸ hp0) hr
    simp only at hd hd'
    rw [k3] at hd'
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im] at hd'
    nlinarith [Complex.normSq_nonneg (A σ (X.p0 - 1) (X.p0 - 1)), Complex.normSq_apply (A σ (X.p0 - 1) (X.p0 - 1)),
      sq_nonneg (A σ (X.p0 - 1) (X.p0 - 1)).re, sq_nonneg (A σ (X.p0 - 1) (X.p0 - 1)).im]

end GlobalTheory.AntiIsom
