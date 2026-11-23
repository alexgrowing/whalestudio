import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CechPoset

variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)

def triVal (c : CC F 2) (X : (NE κ)ᵒᵖ) (s : Finset κ) : F.obj X :=
  if h : s.card = 2 + 1 ∧ s ⊆ sub X then
    mp F (homOf (a := ne s (card_nonempty ⟨s, h.1⟩)) (b := X) h.2) (c ⟨s, h.1⟩)
  else 0

variable {F}

theorem hom_eq {a b : (NE κ)ᵒᵖ} (f g : a ⟶ b) : f = g := Subsingleton.elim _ _

theorem triVal_eq (c : CC F 2) (X : (NE κ)ᵒᵖ) {s : Finset κ} (hs : s.card = 2 + 1) (h : s ⊆ sub X) :
    mp F (homOf (a := ne s (card_nonempty ⟨s, hs⟩)) (b := X) h) (c ⟨s, hs⟩) = triVal F c X s := by
  unfold triVal; rw [dif_pos ⟨hs, h⟩]

theorem triVal_map (c : CC F 2) {X Y : (NE κ)ᵒᵖ} (f : X ⟶ Y) {s : Finset κ} (h : s ⊆ sub X) :
    mp F f (triVal F c X s) = triVal F c Y s := by
  unfold triVal
  by_cases hs : s.card = 2 + 1
  · rw [dif_pos ⟨hs, h⟩, dif_pos ⟨hs, h.trans (sub_subset f)⟩, ← mp_comp]
    congr 1
  · rw [dif_neg (fun h' => hs h'.1), dif_neg (fun h' => hs h'.1), map_zero]

theorem alternatingToOrderedCechDegreeTwo_apply_triple (c : CC F 2) {a b d : (NE κ)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ d) :
    e2 F c a b d f g = if mn d < mn b ∧ mn b < mn a then -triVal F c d {mn d, mn b, mn a} else 0 := by
  unfold e2
  simp only [LinearMap.pi_apply]
  split_ifs with h
  · simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [← triVal_eq c d (card_three h.1 h.2) (triple_subset f g)]
    rfl
  · rfl

end GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset
variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] {F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R}

theorem triVal_eq' (c : CC F 2) {X : (NE κ)ᵒᵖ} (s : {s : Finset κ // s.card = 2 + 1})
    (f : ne s.1 (card_nonempty s) ⟶ X) : mp F f (c s) = triVal F c X s.1 := by
  obtain ⟨s, hs⟩ := s
  rw [← triVal_eq c X hs (sub_subset f), hom_eq f (homOf (sub_subset f))]

theorem triVal_rel (c : CC F 2) (hc : δ F 2 c = 0) (X : (NE κ)ᵒᵖ) {w x y z : κ}
    (h1 : w < x) (h2 : x < y) (h3 : y < z) (hs : ({w, x, y, z} : Finset κ) ⊆ sub X) :
    triVal F c X {x, y, z} - triVal F c X {w, y, z} + triVal F c X {w, x, z} - triVal F c X {w, x, y} = 0 := by
  have ht : ({w, x, y, z} : Finset κ).card = 2 + 1 + 1 := by
    rw [Finset.card_insert_of_notMem (by simp [h1.ne, (h1.trans h2).ne, (h1.trans (h2.trans h3)).ne]),
      Finset.card_insert_of_notMem (by simp [h2.ne, (h2.trans h3).ne]), Finset.card_pair h3.ne]
  have e := congrArg (mp F (homOf (a := ne _ (card_nonempty ⟨_, ht⟩)) (b := X) hs))
    (congrFun hc ⟨_, ht⟩)
  rw [δ_apply, map_sum, Pi.zero_apply, map_zero] at e
  have e' : ∑ i ∈ ({w, x, y, z} : Finset κ), GlobalTheory.cubeSign ({w, x, y, z} : Finset κ) i •
      triVal F c X (({w, x, y, z} : Finset κ).erase i) = 0 := by
    rw [← e, ← Finset.sum_coe_sort]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, ← mp_comp, triVal_eq']
  rw [Finset.sum_insert (by simp [h1.ne, (h1.trans h2).ne, (h1.trans (h2.trans h3)).ne]),
    Finset.sum_insert (by simp [h2.ne, (h2.trans h3).ne]), Finset.sum_pair h3.ne] at e'
  have hwx := h1.ne; have hwy := (h1.trans h2).ne; have hwz := (h1.trans (h2.trans h3)).ne
  have hxy := h2.ne; have hxz := (h2.trans h3).ne; have hyz := h3.ne
  simp only [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, h1, h2, h3, h1.trans h2,
    h1.trans (h2.trans h3), h2.trans h3, lt_irrefl, not_lt_of_gt, if_true, if_false] at e'
  simp only [Finset.insert_empty, Finset.card_empty, Finset.card_singleton,
    Finset.card_pair hwx, Finset.card_insert_of_notMem (show w ∉ ({x, y} : Finset κ) by simp [hwx, hwy]),
    Finset.card_pair hxy] at e'
  rw [Finset.erase_insert (by simp [hwx, hwy, hwz]),
    Finset.erase_insert_of_ne hwx, Finset.erase_insert (by simp [hxy, hxz]),
    Finset.erase_insert_of_ne hwy, Finset.erase_insert_of_ne hxy,
    Finset.erase_insert (by simp [hyz]),
    Finset.erase_insert_of_ne hwz, Finset.erase_insert_of_ne hxz,
    Finset.erase_insert_of_ne hyz, Finset.erase_singleton] at e'
  norm_num at e'
  linear_combination e'

end GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset
variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] {F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R}

theorem alternatingToOrderedCechDegreeTwo_map_apply (c : CC F 2) {a b d g : (NE κ)ᵒᵖ} (f : a ⟶ b) (f' : b ⟶ d) (f'' : d ⟶ g) :
    mp F f'' (e2 F c a b d f f') =
      if mn d < mn b ∧ mn b < mn a then -triVal F c g {mn d, mn b, mn a} else 0 := by
  rw [alternatingToOrderedCechDegreeTwo_apply_triple]
  split_ifs
  · rw [map_neg, triVal_map c f'' (triple_subset f f')]
  · exact map_zero _

theorem e2_mem_Z2_of_delta_eq_zero (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (c : CC F 2) (hc : δ F 2 c = 0) :
    e2 F c ∈ Z2 F := by
  intro a b d g φ ψ χ
  have hab := mn_le_of_hom φ; have hbd := mn_le_of_hom ψ; have hdg := mn_le_of_hom χ
  have hs : ({mn g, mn d, mn b, mn a} : Finset κ) ⊆ sub g := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact mn_mem g
    · exact sub_subset χ (mn_mem d)
    · exact sub_subset (ψ ≫ χ) (mn_mem b)
    · exact sub_subset (φ ≫ ψ ≫ χ) (mn_mem a)
  have hrel : mn g < mn d → mn d < mn b → mn b < mn a →
      triVal F c g {mn d, mn b, mn a} - triVal F c g {mn g, mn b, mn a} +
        triVal F c g {mn g, mn d, mn a} - triVal F c g {mn g, mn d, mn b} = 0 :=
    fun h1 h2 h3 => triVal_rel c hc g h1 h2 h3 hs
  rw [alternatingToOrderedCechDegreeTwo_map_apply, alternatingToOrderedCechDegreeTwo_apply_triple, alternatingToOrderedCechDegreeTwo_apply_triple, alternatingToOrderedCechDegreeTwo_apply_triple]
  generalize mn a = xa at *
  generalize mn b = xb at *
  generalize mn d = xd at *
  generalize mn g = xg at *
  rcases hdg.lt_or_eq with h1 | rfl <;> rcases hbd.lt_or_eq with h2 | rfl <;>
    rcases hab.lt_or_eq with h3 | rfl <;>
    simp_all [lt_irrefl, not_lt_of_ge, le_of_lt]
  rw [if_pos (h2.trans h3), if_pos (h1.trans h2)]
  linear_combination -hrel
end GlobalTheory.CechPoset
