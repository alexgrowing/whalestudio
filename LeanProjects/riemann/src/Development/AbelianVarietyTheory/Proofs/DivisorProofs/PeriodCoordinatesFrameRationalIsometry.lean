import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

namespace GlobalTheory.GeoLevel

open NumberField AlgebraicGeometry CategoryTheory in
open scoped Matrix in
private lemma mat_lact_castFr_eq_map_mul {E : Type} [Field E] {r : ℕ} {Ψ Ψ' : Finset (E →+* ℂ)}
    (hΨ : Ψ = Ψ') (a : GL (Fin r) E) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) (τ : E →+* ℂ) (hτ : τ ∈ Ψ')
    (hτ₀ : τ ∈ Ψ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact a (_root_.GlobalTheory.Dict.castFr hΨ x)) ⟨τ, hτ⟩ =
      (a : Matrix (Fin r) (Fin r) E).map τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x ⟨τ, hτ₀⟩ := by
  rfl

open NumberField AlgebraicGeometry CategoryTheory in
open scoped Matrix in
private lemma emb_mulVec_eq_map_mulVec_emb {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (τ : E →+* ℂ) (A : Matrix (Fin r) (Fin r) E) (v : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ (A *ᵥ v) = (A.map τ) *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ v := by
  funext k
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb, Matrix.mulVec, dotProduct, map_sum, map_mul]

open NumberField AlgebraicGeometry CategoryTheory in
open scoped Matrix in
private lemma col_mul_eq_mulVec_col' {r : ℕ} (A M : Matrix (Fin r) (Fin r) ℂ) (j : Fin r) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.col (A * M) j = A *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.col M j := by
  funext k
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mulVec, dotProduct, Matrix.mul_apply]

open NumberField AlgebraicGeometry CategoryTheory in
open scoped Matrix in

theorem _root_.GlobalTheory.GeoLevel.perFr_lact_of_isMatch : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (r : ℕ) (X X' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (a : GL (Fin r) E)
    (h : _root_.GlobalTheory.LevelCusp.IsMatch X X' a) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (v : Fin r → E)
    (τ : E →+* ℂ) (i : ℕ),
    _root_.Formalism.L2.PjFree.perFr X' (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact a (_root_.GlobalTheory.Dict.castFr h.psi x))
        ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) τ i = _root_.Formalism.L2.PjFree.perFr X x v τ i := by
  intro E _ _ _ r X X' a h x v τ i
  have hΨ := h.psi
  have hp := h.p0
  have hA : IsUnit ((a : Matrix (Fin r) (Fin r) E).map τ).det := by
    have h₀ := (Matrix.isUnits_det_units a).map τ
    rwa [RingHom.map_det] at h₀
  unfold _root_.Formalism.L2.PjFree.perFr
  by_cases hτ : τ ∈ X.Ψ
  · have hτ' : τ ∈ X'.Ψ := hΨ ▸ hτ
    rw [dif_pos hτ', dif_pos hτ]
    by_cases hi : X.p0 + i < r
    · have hi' : X'.p0 + i < r := hp ▸ hi
      rw [dif_pos hi', dif_pos hi]
      have hfin : (⟨X'.p0 + i, hi'⟩ : Fin r) = ⟨X.p0 + i, hi⟩ := Fin.ext (by simp [hp])
      rw [hfin, mat_lact_castFr_eq_map_mul hΨ a x τ hτ' hτ, emb_mulVec_eq_map_mulVec_emb, Matrix.mul_inv_rev,
        Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA, Matrix.mul_one]
    · have hi' : ¬ X'.p0 + i < r := hp ▸ hi
      rw [dif_neg hi', dif_neg hi]
  · have hτ' : τ ∉ X'.Ψ := hΨ ▸ hτ
    rw [dif_neg hτ', dif_neg hτ]
    by_cases hσ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ ∈ X.Ψ
    · have hσ' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ ∈ X'.Ψ := hΨ ▸ hσ
      rw [dif_pos hσ', dif_pos hσ]
      by_cases hj : X.p0 - 1 - i < r
      · have hj' : X'.p0 - 1 - i < r := hp ▸ hj
        rw [dif_pos hj', dif_pos hj]
        have hfin : (⟨X'.p0 - 1 - i, hj'⟩ : Fin r) = ⟨X.p0 - 1 - i, hj⟩ := Fin.ext (by simp [hp])
        rw [hfin, mat_lact_castFr_eq_map_mul hΨ a x _ hσ' hσ, col_mul_eq_mulVec_col', emb_mulVec_eq_map_mulVec_emb]
        exact h.hermC_eq _ _ _
      · have hj' : ¬ X'.p0 - 1 - i < r := hp ▸ hj
        rw [dif_neg hj', dif_neg hj]
    · have hσ' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ ∉ X'.Ψ := hΨ ▸ hσ
      rw [dif_neg hσ', dif_neg hσ]

end GlobalTheory.GeoLevel
