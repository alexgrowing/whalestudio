import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSectionsVanishingOriginSeparatingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApplyNeOriginStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem hom_left_origin {K : Type} [Field K] {A B : AbVar K} (f : A ⟶ B) : f.hom.left A.origin = B.origin := by
  have e : (1 : Over.mk (𝟙 (Sp K)) ⟶ A.X) ≫ f.hom = 1 := by
    rw [CategoryTheory.Hom.one_def, CategoryTheory.Hom.one_def, Category.assoc, IsMonHom.one_hom]
  unfold origin
  rw [← e, Over.comp_left]
  rfl

theorem exists_sec_pull_ample_vanish_origin : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (d : Pic B.X.left),
    IsAmpleCls d → f ≠ 0 → ∃ (m : ℕ) (M : LB A.X.left) (hM : M.IsLB) (s : LB.Sec M), 0 < m ∧
      cls M hM = m • CechPic.pull f.hom.left d ∧ Out.nonzeroLocus s ≠ ⊥ ∧ A.origin ∉ Out.nonzeroLocus s := by
  intro K _ A B f d hd hf
  obtain ⟨L, hL, amp, rfl⟩ := hd
  obtain ⟨N, hN, M, t, h0, h1⟩ := GlobalTheory.T.exists_ampleSections_vanishing_origin_separating K B L hL amp
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_apply_ne_origin' K A B f hf
  let ιB := (B.X.hom ⁻¹ᵁ ⊤).ι
  let h : A.X.left ⟶ (B.X.hom ⁻¹ᵁ ⊤).toScheme := IsOpenImmersion.lift ιB f.hom.left (by
    rw [Scheme.Opens.range_ι]; intro x _; trivial)
  have hh : h ≫ ιB = f.hom.left := IsOpenImmersion.lift_fac _ _ _
  have hpt : ∀ x, ιB (h x) = f.hom.left x := fun x => by rw [← hh]; rfl
  obtain ⟨j, hj⟩ := h1 (h a) (by rw [hpt]; exact ha)
  let s := ReciprocityTheory.ChartRestriction.G.DVR.pullSec L (fun _ : Fin N => ιB) (fun _ => 1) (t j) h
  have hs : Out.nonzeroLocus s = h ⁻¹ᵁ Out.nonzeroLocus (t j) := GlobalTheory.nonzeroLocus_pullSec _ _ (t j) h
  refine ⟨N, _, LB.isLB_linComb hL _ _, s, hN, ?_, ?_, ?_⟩
  · rw [cls_linComb hL]
    simp only [hh, one_zsmul, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  · intro e
    have : a ∈ Out.nonzeroLocus s := by rw [hs]; exact hj
    rw [e] at this; exact this
  · intro ho
    rw [hs] at ho
    exact h0 j (h A.origin) (by rw [hpt, hom_left_origin]) ho

end GlobalTheory.AV.AbVar
