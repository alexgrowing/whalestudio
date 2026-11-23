import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.Vert GlobalTheory.TriFrame GlobalTheory.FlagCell
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)

namespace GlobalTheory.Vert.VertDiv

theorem cls_eq_of_local_units : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B : Vert.Model O) (P P' : VertDiv B), (∀ x : B.X, ∃ (V : B.X.Opens) (i : P.M.ι) (j : P'.M.ι) (hi : V ≤ P.M.U i) (hj : V ≤ P'.M.U j) (u : Γ(B.X, V)ˣ), x ∈ V ∧ P'.eqn j (inf_le_inf_left B.gen hj) = resG B.X inf_le_right u.val * P.eqn i (inf_le_inf_left B.gen hi)) → P.cls = P'.cls := by
  intro O _ _ _ B P P' H
  obtain ⟨⟨⟨g, hg⟩, s⟩, h⟩ := P.exists_extends'
  obtain ⟨⟨⟨g', hg'⟩, s'⟩, h'⟩ := P'.exists_extends'
  have h₁ := h.smul g'
  have h₂ := mul_comm g g' ▸ h'.smul g
  have h0 := mul_ne_zero hg' hg
  rw [h₁.cls_eq h0, h₂.cls_eq h0, sub_left_inj]
  refine congrArg Model.ofEff (Subtype.ext ?_)
  simp only [Extends.eff, Model.effMk]
  refine idealSheaf_eq_of_germ _ _ fun x i j hi hj => ?_
  obtain ⟨V, i0, j0, hi0, hj0, u, hx, hu⟩ := H x
  have key : resG B.X hj0 ((B.const g • s').f j0) =
      u.val * resG B.X hi0 ((B.const g' • s).f i0) := by
    refine B.resG_injective inf_le_right le_rfl ?_
    simp only [map_mul, resG_resG]
    rw [h₂.resG_f j0 (inf_le_inf_left _ hj0), h₁.resG_f i0 (inf_le_inf_left _ hi0), hu]
    ring
  have e := congrArg (B.X.presheaf.germ _ x hx).hom key
  simp only [map_mul, GlobalTheory.Cartier.germ_resG] at e
  refine ((EffCartierData.ofSec P.isLB _ (h₁.isRegularSec h0)).associated_germ i i0 x hi
    (hi0 hx)).trans (((associated_unit_mul_left _ _ (u.isUnit.map _)).symm.trans
      (Associated.of_eq e.symm)).trans
    ((EffCartierData.ofSec P'.isLB _ (h₂.isRegularSec h0)).associated_germ j0 j x (hj0 hx) hj))

end GlobalTheory.Vert.VertDiv
