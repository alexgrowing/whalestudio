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
namespace GlobalTheory.CechPosetDegreeOne
variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)

open Classical in

def val {p : ℕ} (c : CC F p) (s : Finset κ) (b : (NE κ)ᵒᵖ) : F.obj b :=
  if h : s.card = p + 1 ∧ s ⊆ sub b then
    mp F (homOf (a := ne s (card_nonempty ⟨s, h.1⟩)) (b := b) h.2) (c ⟨s, h.1⟩) else 0

theorem val_eq {p : ℕ} (c : CC F p) (s : {s : Finset κ // s.card = p + 1}) (b : (NE κ)ᵒᵖ)
    (f : ne s.1 (card_nonempty s) ⟶ b) : mp F f (c s) = val F c s.1 b := by
  unfold val
  obtain ⟨s, hs⟩ := s
  have hsub : s ⊆ sub b := sub_subset f
  rw [dif_pos (⟨hs, hsub⟩ : s.card = p + 1 ∧ s ⊆ sub b)]
  exact congrArg (fun φ => mp F φ (c ⟨s, hs⟩)) (Subsingleton.elim _ _)

theorem mp_val {p : ℕ} (c : CC F p) (s : Finset κ) {b d : (NE κ)ᵒᵖ} (g : b ⟶ d)
    (h : s.card = p + 1) (hs : s ⊆ sub b) : mp F g (val F c s b) = val F c s d := by
  rw [← val_eq F c ⟨s, h⟩ b (homOf hs), ← mp_comp, val_eq]

theorem orderedCechToCatCochainsOne_apply_valueAtSubset (c : CC F 1) {a b : (NE κ)ᵒᵖ} (f : a ⟶ b) :
    e1 F c a b f = if mn b < mn a then - val F c {mn b, mn a} b else 0 := by
  simp only [e1, LinearMap.pi_apply]
  split_ifs with h
  · simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.proj_apply, AlgHom.toLinearMap_apply]
    exact congrArg Neg.neg (val_eq F c ⟨{mn b, mn a}, Finset.card_pair h.ne⟩ b _)
  · rfl

theorem alternatingToOrderedCechDegreeTwo_apply_valueAtSubset (c : CC F 2) {a b d : (NE κ)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ d) :
    e2 F c a b d f g = if mn d < mn b ∧ mn b < mn a then - val F c {mn d, mn b, mn a} d else 0 := by
  simp only [e2, LinearMap.pi_apply]
  split_ifs with h
  · simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.proj_apply, AlgHom.toLinearMap_apply]
    exact congrArg Neg.neg (val_eq F c ⟨{mn d, mn b, mn a}, card_three h.1 h.2⟩ d _)
  · rfl

theorem val_δ {p : ℕ} (c : CC F p) (t : Finset κ) (d : (NE κ)ᵒᵖ) (h : t.card = p + 1 + 1)
    (ht : t ⊆ sub d) :
    val F (δ F p c) t d = ∑ i ∈ t, GlobalTheory.cubeSign t i • val F c (t.erase i) d := by
  rw [← val_eq F (δ F p c) ⟨t, h⟩ d (homOf ht), δ_apply, map_sum,
    ← Finset.sum_coe_sort t (fun i => GlobalTheory.cubeSign t i • val F c (t.erase i) d)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, ← mp_comp, val_eq]

theorem val_δ_three (c : CC F 1) {x y z : κ} (h₁ : x < y) (h₂ : y < z) (d : (NE κ)ᵒᵖ)
    (ht : ({x, y, z} : Finset κ) ⊆ sub d) :
    val F (δ F 1 c) {x, y, z} d = val F c {y, z} d - val F c {x, z} d + val F c {x, y} d := by
  have h₃ := h₁.trans h₂
  rw [val_δ F c _ d (card_three h₁ h₂) ht, Finset.sum_insert (by simp [h₁.ne, h₃.ne]),
    Finset.sum_pair h₂.ne]
  have e₁ : ({x, y, z} : Finset κ).erase x = {y, z} := by
    ext w; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · tauto
    · rintro (rfl | rfl) <;> simp [h₁.ne', h₃.ne']
  have e₂ : ({x, y, z} : Finset κ).erase y = {x, z} := by
    ext w; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · tauto
    · rintro (rfl | rfl) <;> simp [h₁.ne, h₂.ne']
  have e₃ : ({x, y, z} : Finset κ).erase z = {x, y} := by
    ext w; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · tauto
    · rintro (rfl | rfl) <;> simp [h₃.ne, h₂.ne]
  have s₁ : GlobalTheory.cubeSign ({x, y, z} : Finset κ) x = 1 := by
    simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, h₁.not_gt, h₃.not_gt]
  have s₂ : GlobalTheory.cubeSign ({x, y, z} : Finset κ) y = -1 := by
    simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, h₁, h₂.not_gt]
  have s₃ : GlobalTheory.cubeSign ({x, y, z} : Finset κ) z = 1 := by
    simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, h₃, h₂, Finset.card_pair h₁.ne]
  rw [e₁, e₂, e₃, s₁, s₂, s₃]
  simp only [one_smul, neg_smul]
  ring

theorem orderedCechToCatCochainsOne_coboundary_comm {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)
    (c : CC F 1) : d1 F (e1 F c) = e2 F (δ F 1 c) := by
  funext a b d f g
  rw [d1_apply, orderedCechToCatCochainsOne_apply_valueAtSubset, orderedCechToCatCochainsOne_apply_valueAtSubset, orderedCechToCatCochainsOne_apply_valueAtSubset, alternatingToOrderedCechDegreeTwo_apply_valueAtSubset]
  rcases (mn_le_of_hom f).lt_or_eq with h₂ | h₂ <;> rcases (mn_le_of_hom g).lt_or_eq with h₁ | h₁
  · rw [if_pos h₂, if_pos h₁, if_pos (h₁.trans h₂), if_pos ⟨h₁, h₂⟩, map_neg,
      mp_val F c _ g (Finset.card_pair h₂.ne) (pair_subset f),
      val_δ_three F c h₁ h₂ d (triple_subset f g)]
    ring
  · rw [if_pos h₂, if_neg h₁.not_lt, if_pos (h₁ ▸ h₂), if_neg (fun h => h₁.not_lt h.1), map_neg,
      mp_val F c _ g (Finset.card_pair h₂.ne) (pair_subset f), h₁]
    ring
  · rw [if_neg h₂.not_lt, if_pos h₁, if_pos (h₂ ▸ h₁), if_neg (fun h => h₂.not_lt h.2), map_zero, h₂]
    ring
  · rw [if_neg h₂.not_lt, if_neg h₁.not_lt, if_neg (h₁.trans h₂).not_lt,
      if_neg (fun h => h₂.not_lt h.2), map_zero]
    ring

end GlobalTheory.CechPosetDegreeOne
