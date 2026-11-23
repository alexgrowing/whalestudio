import Formalism.SharpRestriction.CuspSpanNormBounds.GramProductLeHeightBoundTwo

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.GramProductBounds

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals
  Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem NE_pow (D : D7) : NE (E := D.host.E) (gS D) ^ (D.R.rS + 1) = (gS D : ℝ) ^ (D.R.m * D.R.f) := by
  unfold NE
  rw [j_finrank D, ← pow_mul]
  congr 1
  have h2 := D.R.two_le_m
  obtain ⟨k, hk⟩ := D.R.m_even
  have hm : 2 * (D.R.rS + 1) = D.R.m := by
    unfold Ranks.rS
    omega
  rw [← hm]
  ring

def DetProductFormula : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ),
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ →
  ∀ F' : FlagU D u', IsTermF D Λ (lf D F0) F' → IsGeneric Λ (gS D) (lf D F0) F' →
    NG Λ (lf D F0) F' = ∏ τ, Cnt.Gz D (Tu D u) (Tu D u') (ZhatL (lf D F0) F') τ

theorem id_of_detUU (h : DetProductFormula) : LatticeIdentityGeneric := by
  intro D large₂ u u' C' Cl Cg cb Cu cT CT C0 A hH F0 he hz0 Λ hΛr F' hT' hgen
  unfold G0 localGramProduct
  rw [h D large₂ u u' C' Cl Cg cb Cu cT CT C0 A hH F0 he hz0 Λ hΛr F' hT' hgen, NE_pow, div_eq_mul_inv, inv_pow]

theorem gram_flag_family_of_det_product (h : DetProductFormula) {eps : ℝ} (Fm : FamP eps) (Cg cb Cu cT CT C0 A : ℝ) :
    FamilyGenericTermDetProductBound Fm Cg cb Cu cT CT C0 A :=
  gram_flag_family_of_identity (id_of_detUU h) Fm Cg cb Cu cT CT C0 A

end Formalism.MainNotions.GramProductBounds

end
