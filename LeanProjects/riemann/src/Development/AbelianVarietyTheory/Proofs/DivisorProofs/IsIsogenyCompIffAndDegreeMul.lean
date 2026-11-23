import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyCompAndDegreeMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffFiniteKerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfIsFiniteOfDimEqAbelianVarietyHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteOfSurjectiveOfDimEqStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.AV.AbVar.isIsogeny_comp_iff_and_deg_comp : ∀ (K : Type) [Field K] (A B C : AbVar K) (f : A ⟶ B) (g : B ⟶ C),
    A.dim = B.dim → B.dim = C.dim →
      (IsIsogeny (f ≫ g) ↔ IsIsogeny f ∧ IsIsogeny g) ∧ deg (f ≫ g) = deg f * deg g := by
  intro K _ A B C f g hAB hBC
  have hleft : (f ≫ g).hom.left = f.hom.left ≫ g.hom.left := by
    rw [comp_hom, Over.comp_left]
  have key : IsIsogeny (f ≫ g) ↔ IsIsogeny f ∧ IsIsogeny g := by
    constructor
    · rintro ⟨hfin, hsurj⟩
      have hs2 : Surjective (f.hom.left ≫ g.hom.left) := by rw [← hleft]; exact hsurj
      have hgs : Surjective g.hom.left := Surjective.of_comp f.hom.left g.hom.left
      have hgf : IsFinite g.hom.left := GlobalTheory.T.isFinite_of_surjective_of_dim_eq' K B C g hBC hgs
      have hker : Finite (ptMap (f ≫ g)).ker := (GlobalTheory.T.isFinite_iff_finite_ker' K A C (f ≫ g)).1 hfin
      have hle : (ptMap f).ker ≤ (ptMap (f ≫ g)).ker := by
        intro x hx
        rw [MonoidHom.mem_ker] at hx ⊢
        have hx' : x ≫ f.hom = 1 := hx
        show x ≫ (f ≫ g).hom = 1
        rw [comp_hom, ← Category.assoc, hx', MonObj.one_comp]
      have hfk : Finite (ptMap f).ker :=
        Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
      have hff : IsFinite f.hom.left := (GlobalTheory.T.isFinite_iff_finite_ker' K A B f).2 hfk
      exact ⟨⟨hff, GlobalTheory.T.surjective_of_isFinite_of_dim_eq_abelianVarietyHom K A B f hAB hff⟩, ⟨hgf, hgs⟩⟩
    · rintro ⟨hf, hg⟩
      exact (GlobalTheory.T.isogeny_comp_and_degree_mul K A B C f g hf hg).1
  refine ⟨key, ?_⟩
  by_cases h : IsIsogeny f ∧ IsIsogeny g
  · exact (GlobalTheory.T.isogeny_comp_and_degree_mul K A B C f g h.1 h.2).2
  · have h0 : deg (f ≫ g) = 0 := by
      unfold deg; rw [if_neg (fun h' => h (key.1 h'))]
    rw [h0]
    rcases not_and_or.1 h with hf | hg
    · have : deg f = 0 := by unfold deg; rw [if_neg hf]
      rw [this, zero_mul]
    · have : deg g = 0 := by unfold deg; rw [if_neg hg]
      rw [this, mul_zero]
