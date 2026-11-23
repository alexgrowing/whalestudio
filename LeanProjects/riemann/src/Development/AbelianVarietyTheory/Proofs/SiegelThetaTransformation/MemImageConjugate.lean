import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Fischer
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero

open Matrix Complex NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate Classical

namespace GlobalTheory.Ker.ConjDatum

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

open Matrix Complex NumberField in
open scoped ComplexConjugate Classical in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.Ker.ConjDatum.conjugate_twice (τ : E →+* ℂ) :
    ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := by
  ext x
  simp [ComplexEmbedding.conjugate_coe_eq]

open Matrix Complex NumberField in
open scoped ComplexConjugate Classical in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.Ker.ConjDatum.gram_conjugate (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (P : Matrix (Fin r) (Fin r) ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (ComplexEmbedding.conjugate τ) G (P.map (starRingEnd ℂ)) =
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G P).map (starRingEnd ℂ) := by
  ext a b
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.gram, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC, _root_.ReciprocityTheory.ChartRestriction.G.FD.col, ComplexEmbedding.conjugate_coe_eq, map_sum]

open Matrix Complex NumberField in
open scoped ComplexConjugate Classical in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.Ker.ConjDatum.det_map_ne {M : Matrix (Fin r) (Fin r) ℂ} (h : M.det ≠ 0) :
    (M.map (starRingEnd ℂ)).det ≠ 0 := by
  have hdet : (M.map (starRingEnd ℂ)).det = starRingEnd ℂ M.det := by
    rw [RingHom.map_det]
    rfl
  rw [hdet]
  exact (map_ne_zero _).2 h

open Matrix Complex NumberField in
open scoped ComplexConjugate Classical in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.Ker.ConjDatum.mem_image_conjugate (Ψ : Finset (E →+* ℂ)) (τ : E →+* ℂ) :
    τ ∈ Ψ.image ComplexEmbedding.conjugate ↔ ComplexEmbedding.conjugate τ ∈ Ψ := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    rwa [_root_.GlobalTheory.Ker.ConjDatum.conjugate_twice]
  · exact fun h => ⟨_, h, _root_.GlobalTheory.Ker.ConjDatum.conjugate_twice τ⟩

def cpl (Ψ : Finset (E →+* ℂ)) (τ : Ψ) : Ψ.image ComplexEmbedding.conjugate :=
  ⟨ComplexEmbedding.conjugate τ.1, Finset.mem_image_of_mem _ τ.2⟩

def cfr (Ψ : Finset (E →+* ℂ)) (x : Frame (Ψ.image ComplexEmbedding.conjugate) r) : Frame Ψ r :=
  fun τ a b => conj (x (cpl Ψ τ) a b)

open Matrix Complex NumberField in
open scoped ComplexConjugate Classical in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.Ker.ConjDatum.cfr_mem_GG (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E)
    (p : ℕ) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame (Ψ.image ComplexEmbedding.conjugate) r} (hx : x ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.GG _ G p) :
    _root_.GlobalTheory.Ker.ConjDatum.cfr Ψ x ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.GG Ψ G p := by
  intro τ
  obtain ⟨hdet, hpos⟩ := hx (_root_.GlobalTheory.Ker.ConjDatum.cpl Ψ τ)
  have hmat : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.GlobalTheory.Ker.ConjDatum.cfr Ψ x) τ =
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (_root_.GlobalTheory.Ker.ConjDatum.cpl Ψ τ)).map (starRingEnd ℂ) := by
    ext a b
    rfl
  have hgram : _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (τ : E →+* ℂ) G (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.GlobalTheory.Ker.ConjDatum.cfr Ψ x) τ) =
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.gram (_root_.GlobalTheory.Ker.ConjDatum.cpl Ψ τ : E →+* ℂ) G
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (_root_.GlobalTheory.Ker.ConjDatum.cpl Ψ τ))).map (starRingEnd ℂ) := by
    rw [hmat]
    have h := _root_.GlobalTheory.Ker.ConjDatum.gram_conjugate (ComplexEmbedding.conjugate (τ : E →+* ℂ)) G
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (_root_.GlobalTheory.Ker.ConjDatum.cpl Ψ τ))
    rw [_root_.GlobalTheory.Ker.ConjDatum.conjugate_twice] at h
    exact h
  refine ⟨?_, fun i => ?_⟩
  · rw [hmat]
    exact _root_.GlobalTheory.Ker.ConjDatum.det_map_ne hdet
  · have h := hpos i
    have hminor : _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin G (_root_.GlobalTheory.Ker.ConjDatum.cfr Ψ x) τ i =
        starRingEnd ℂ (_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin G x (_root_.GlobalTheory.Ker.ConjDatum.cpl Ψ τ) i) := by
      simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin, _root_.ReciprocityTheory.ChartRestriction.G.FD.lminor, hgram, ← Matrix.submatrix_map]
      rw [RingHom.map_det]
      rfl
    rw [hminor, Complex.conj_re]
    exact h

open Matrix Complex NumberField in
open scoped ComplexConjugate Classical in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.Ker.ConjDatum.cfr_mem_Bor (Ψ : Finset (E →+* ℂ))
    {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame (Ψ.image ComplexEmbedding.conjugate) r} (hx : x ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor _ r) :
    _root_.GlobalTheory.Ker.ConjDatum.cfr Ψ x ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r := by
  intro τ
  obtain ⟨hdet, htri⟩ := hx (_root_.GlobalTheory.Ker.ConjDatum.cpl Ψ τ)
  refine ⟨?_, fun a c hca => ?_⟩
  · have hmat : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.GlobalTheory.Ker.ConjDatum.cfr Ψ x) τ =
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (_root_.GlobalTheory.Ker.ConjDatum.cpl Ψ τ)).map (starRingEnd ℂ) := by
      ext a b
      rfl
    rw [hmat]
    exact _root_.GlobalTheory.Ker.ConjDatum.det_map_ne hdet
  · simp [_root_.GlobalTheory.Ker.ConjDatum.cfr, htri a c hca]

open Matrix Complex NumberField in
open scoped ComplexConjugate Classical in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.Ker.ConjDatum.cfr_rmul (Ψ : Finset (E →+* ℂ))
    (x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame (Ψ.image ComplexEmbedding.conjugate) r) :
    _root_.GlobalTheory.Ker.ConjDatum.cfr Ψ (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) =
      _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul (_root_.GlobalTheory.Ker.ConjDatum.cfr Ψ x) (_root_.GlobalTheory.Ker.ConjDatum.cfr Ψ b) := by
  funext τ a c
  simp [_root_.GlobalTheory.Ker.ConjDatum.cfr, _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat, Matrix.mul_apply, map_sum]

open Matrix Complex NumberField in
open scoped ComplexConjugate Classical in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.Ker.ConjDatum.cfr_lact (Ψ : Finset (E →+* ℂ)) (γ : GL (Fin r) E)
    (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame (Ψ.image ComplexEmbedding.conjugate) r) :
    _root_.GlobalTheory.Ker.ConjDatum.cfr Ψ (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x) =
      _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ (_root_.GlobalTheory.Ker.ConjDatum.cfr Ψ x) := by
  funext τ a c
  simp [_root_.GlobalTheory.Ker.ConjDatum.cfr, _root_.ReciprocityTheory.ChartRestriction.G.FD.lact, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat, Matrix.mul_apply, map_sum,
    _root_.GlobalTheory.Ker.ConjDatum.cpl, ComplexEmbedding.conjugate_coe_eq]

def conjData (X : Data E r) : Data E r where
  Ψ := X.Ψ.image ComplexEmbedding.conjugate
  cmType τ := by
    rw [mem_image_conjugate, mem_image_conjugate]
    exact X.cmType _
  Gm := X.Gm
  Gm_herm := X.Gm_herm
  Gm_det := X.Gm_det
  p0 := X.p0
  p0_le := X.p0_le
  signature τ := by
    obtain ⟨P, h1, h2⟩ := X.signature ⟨_, (mem_image_conjugate _ _).1 τ.2⟩
    refine ⟨P.map (starRingEnd ℂ), det_map_ne h1, ?_⟩
    have h4 := gram_conjugate (ComplexEmbedding.conjugate τ.1) X.Gm P
    rw [conjugate_twice] at h4
    rw [h4, h2]
    ext a b
    by_cases h : a = b <;> simp [Matrix.diagonal, h]
  Λ := X.Λ
  Λ_fg := X.Λ_fg
  Λ_span := X.Λ_span
  den := X.den
  den_ne := X.den_ne
  Λ_int := X.Λ_int
  Γ := X.Γ
  Γ_stab := X.Γ_stab
  Γ_index := X.Γ_index
  Γ_free γ hγ x hx b hb h := by
    refine X.Γ_free γ hγ _ (cfr_mem_GG _ _ _ hx) _ (cfr_mem_Bor _ hb) ?_
    rw [← cfr_lact, h, cfr_rmul]
  χ _ _ := 1
  χ_mul := by simp
  χ_add := by simp
  χ_fin _ := ⟨1, one_pos, by simp⟩
  ξ0 := X.ξ0
  ξ0_im := X.ξ0_im
  ξ0_ne := X.ξ0_ne
  κ0 := -X.κ0
  κ0_xi := by
    rcases X.κ0_xi with h | h
    · right; rw [h]
    · left; rw [h, neg_neg]
  κ0_sign τ := by
    have := X.κ0_sign ⟨_, (mem_image_conjugate _ _).1 τ.2⟩
    simpa [ComplexEmbedding.conjugate_coe_eq] using this
  m := X.m
  m_pos := X.m_pos
  transv ξ hξ h0 s hs hi := by
    obtain ⟨γ, h1, h2⟩ := X.transv ξ hξ h0 (-s) (by unfold cc at hs ⊢; rw [map_neg, hs]) hi.neg
    refine ⟨γ, h1, ?_⟩
    rw [h2]
    congr 1
    ring

end

end GlobalTheory.Ker.ConjDatum
