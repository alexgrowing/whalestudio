import Formalism.SharpRestriction.CuspSpanNormBounds.GramProductLeHeightBound
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsCnt

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.GramProductBounds

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals
  Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem one_le_generic_gram_value (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) {C' Cl Cg cb Cu cT CT C0 A : ℝ}
    (hH : Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A)
    (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (he : F0.e = D.sp.hypE) (hz0 : F0.z = D.zmOf u)
    (Λ : LatV D) (hΛr : IsRowLat D F0 Λ) (F' : FlagU D u') (hT' : IsTermF D Λ (lf D F0) F')
    (hgen : IsGeneric Λ (gS D) (lf D F0) F') : 1 ≤ G0 Λ (gS D) (lf D F0) F' := by
  have hSt : Cnt.Stand D u u' := hH.2.1
  have hPr := Formalism.MainNotions.VanishingOnXAndXPlus.primeHyp_of_stand D u u' hSt
  have hF : FixedHyp D Λ (lf D F0) := hΛr.2.1
  have hg : gS D ≠ 0 := by
    unfold gS
    exact Nat.mul_ne_zero hSt.2.2.2.2.2.2.2.1.ne_zero hSt.2.2.2.2.2.2.2.2.1.ne_zero
  have hU1 : HU Λ (lf D F0) F' := a_HU Λ hF.1 _ _ hF.2.2.1.2 hT'.1.1.2
  obtain ⟨_, _, h2, h3, _⟩ := lemma_one_section D u (Tu D u') Λ (lf D F0) F' hF hPr hT'.1
  have hbot := generic_B_eq_bot hg hF.2.2.1 hT'.1.1 hF.2.2.2 hT'.2.1 hgen
  have hle := generic_index_one D large₂ u u' C' Cl Cg cb Cu cT CT C0 A hH F0 he hz0 Λ hΛr F' hT' hgen
  have hLa : La Λ (gS D) (lf D F0) F' = Thp Λ (lf D F0) F' := le_antisymm hle (c_Thp_le_La hU1)
  have hc1 : Nat.card (gB Λ (gS D) (lf D F0) F') = 1 := by rw [hbot]; exact Nat.card_unique
  have hi : iIdx Λ (gS D) (lf D F0) F' = 1 := by
    unfold iIdx idx
    rw [Submodule.comap_subtype_eq_top.2 hle]
    exact Nat.card_unique
  have hNE : 0 < NE (E := D.host.E) (gS D) ^ (D.R.rS + 1) := by
    unfold NE
    have : (0 : ℝ) < (gS D : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hg
    positivity
  have hlow : NE (E := D.host.E) (gS D) ^ (D.R.rS + 1) ≤ (Nat.card (BQ Λ (lf D F0) F') : ℝ) := by
    rw [hc1, Nat.cast_one, le_div_iff₀ hNE, one_mul] at h2
    exact h2
  have hun : Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ := hΛr.2.1.2.1
  have hdet : 1 ≤ latDet (hS D) (La Λ (gS D) (lf D F0) F') := by
    rw [hLa]
    exact rows_one_le_latDet _ fun x hx y hy =>
      Submodule.mem_one.1 (i_int Λ hun (Submodule.mem_inf.1 hy).1 (Submodule.mem_inf.1 hx).1)
  have hB : 0 < (Nat.card (BQ Λ (lf D F0) F') : ℝ) := lt_of_lt_of_le hNE hlow
  rw [hi, Nat.cast_one, mul_one] at h3
  have hNG : NG Λ (lf D F0) F' = latDet (hS D) (La Λ (gS D) (lf D F0) F') * (Nat.card (BQ Λ (lf D F0) F') : ℝ) := by
    rw [h3]
    field_simp
  unfold G0
  rw [le_div_iff₀ hNE, one_mul, hNG]
  nlinarith

def LatticeIdentityPositive : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ),
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ →
  ∀ F' : FlagU D u', IsTermF D Λ (lf D F0) F' → IsGeneric Λ (gS D) (lf D F0) F' →
    G0 Λ (gS D) (lf D F0) F' = localGramProduct D u u' (ZhatL (lf D F0) F') ∧
    (∀ τ, 0 ≤ Cnt.Gz D (Tu D u) (Tu D u') (ZhatL (lf D F0) F') τ)

end Formalism.MainNotions.GramProductBounds

end
