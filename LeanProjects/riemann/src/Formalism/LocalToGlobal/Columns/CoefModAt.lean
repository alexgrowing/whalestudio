import Formalism.LocalToGlobal.Columns.CoefficientsModP

open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions

section

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}
  (emb : ι → E →+* K) (lam : ι → DomWeight n)

theorem nabAt_isLattice (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L) :
    Submodule.IsLattice K (nabAt emb lam L) :=
  (nabDelLattice K ι n lam _ fun τ => tauLatLattice E K ι n emb τ L hL).1

theorem delAt_isLattice (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L) :
    Submodule.IsLattice K (delAt emb lam L) :=
  (nabDelLattice K ι n lam _ fun τ => tauLatLattice E K ι n emb τ L hL).2

theorem dualFr_tauLat_isLattice (τ : ι) (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L) :
    Submodule.IsLattice K (dualFr (tauLat emb τ L)) :=
  (@dualFrLattice K _ _ starRingOfComm n 1 _ (by simp) (tauLatLattice E K ι n emb τ L hL)).1

theorem nabAtr_isLattice (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L) :
    Submodule.IsLattice K (nabAtr emb lam L) :=
  (nabDelLattice K ι n lam _ fun τ => dualFr_tauLat_isLattice emb τ L hL).1

theorem delAtr_isLattice (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L) :
    Submodule.IsLattice K (delAtr emb lam L) :=
  (nabDelLattice K ι n lam _ fun τ => dualFr_tauLat_isLattice emb τ L hL).2

omit [NumberField E] [NumberField K] [Fintype ι] in
theorem isUnit_det_gramK (J : Matrix (Fin n) (Fin n) E) (hJ : IsUnit J.det) (τ : ι) : IsUnit (gramK emb J τ).det := by
  have : (gramK emb J τ).det = emb τ J.det := ((emb τ).map_det J).symm
  rw [this]
  exact hJ.map _

omit [NumberField E] [NumberField K] [Fintype ι] in
theorem isUnit_det_gramKd (J : Matrix (Fin n) (Fin n) E) (hJ : IsUnit J.det) (τ : ι) : IsUnit (gramKd emb J τ).det := by
  unfold gramKd
  rw [Matrix.det_transpose, Matrix.det_nonsing_inv]
  have := isUnit_det_gramK emb J hJ τ
  unfold gramK at this
  exact this.ringInverse

variable [StarRing K]

theorem pairV_nondegenerate (J : Matrix (Fin n) (Fin n) E) (hJ : IsUnit J.det) : (pairV emb lam J).Nondegenerate :=
  pairNondeg K ι n lam _ (isUnit_det_gramK emb J hJ)

theorem pairVr_nondegenerate (J : Matrix (Fin n) (Fin n) E) (hJ : IsUnit J.det) : (pairVr emb lam J).Nondegenerate :=
  pairNondeg K ι n lam _ (isUnit_det_gramKd emb J hJ)

variable (cE : E →+* E) (hc : ∀ τ x, star (emb τ x) = emb τ (cE x)) (J : Matrix (Fin n) (Fin n) E)
  (hJ : Formalism.UG.IsHerm cE J) (hdet : IsUnit J.det) (L L' : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L)
  (hL' : ∀ y, y ∈ L' ↔ ∀ x ∈ L, Formalism.UG.hform cE J x y ∈ (algebraMap (𝓞 E) E).range)

include hc hJ hdet hL hL'

theorem dual_at :
    Formalism.HermitianLatticesTheory.dual (pairV emb lam J) (nabAt emb lam L) = delAt emb lam L' ∧
    Formalism.HermitianLatticesTheory.dual (pairV emb lam J) (delAt emb lam L) = nabAt emb lam L' := by
  have h := nabDelDual K ι n lam (gramK emb J) (fun τ => tauLat emb τ L)
    (fun τ => (gramHerm E K ι n emb cE τ (hc τ) J hJ).1) (isUnit_det_gramK emb J hdet)
    (fun τ => tauLatLattice E K ι n emb τ L hL)
  have e : (fun τ => hdualFr (gramK emb J τ) (tauLat emb τ L)) = fun τ => tauLat emb τ L' :=
    funext fun τ => tauLatDual E K ι n emb cE τ (hc τ) J L L' hdet hL hL'
  rw [e] at h
  exact h

theorem dual_atr :
    Formalism.HermitianLatticesTheory.dual (pairVr emb lam J) (nabAtr emb lam L) = delAtr emb lam L' ∧
    Formalism.HermitianLatticesTheory.dual (pairVr emb lam J) (delAtr emb lam L) = nabAtr emb lam L' := by
  have h := nabDelDual K ι n lam (gramKd emb J) (fun τ => dualFr (tauLat emb τ L))
    (fun τ => (gramHerm E K ι n emb cE τ (hc τ) J hJ).2) (isUnit_det_gramKd emb J hdet)
    (fun τ => dualFr_tauLat_isLattice emb τ L hL)
  have e : (fun τ => hdualFr (gramKd emb J τ) (dualFr (tauLat emb τ L))) = fun τ => dualFr (tauLat emb τ L') := by
    funext τ
    have h1 := dualFrHdual K n (gramK emb J τ) (tauLat emb τ L) (gramHerm E K ι n emb cE τ (hc τ) J hJ).1
      (isUnit_det_gramK emb J hdet τ) (tauLatLattice E K ι n emb τ L hL)
    rw [tauLatDual E K ι n emb cE τ (hc τ) J L L' hdet hL hL'] at h1
    exact h1
  rw [e] at h
  exact h

end

end Formalism.L2.DIV
