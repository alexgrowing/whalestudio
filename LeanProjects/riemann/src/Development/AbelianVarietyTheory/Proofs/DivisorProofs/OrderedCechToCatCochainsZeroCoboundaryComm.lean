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

theorem mp_cochain_congr {p : ℕ} (c : CC F p) {s s' : {s : Finset κ // s.card = p + 1}} (h : s.1 = s'.1)
    {b : (NE κ)ᵒᵖ} (φ : ne s.1 (card_nonempty s) ⟶ b) (φ' : ne s'.1 (card_nonempty s') ⟶ b) :
    mp F φ (c s) = mp F φ' (c s') := by
  obtain rfl : s = s' := Subtype.ext h
  rw [Subsingleton.elim φ φ']

theorem orderedCech_cochainsZero_coboundary_comm {κ : Type} [LinearOrder κ] {R : Type} [CommRing R]
    (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (c : CC F 0) : d0 F (e0 F c) = e1 F (δ F 0 c) := by
  funext a b f
  rw [amitsur_d0_apply]
  simp only [e0, e1, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    AlgHom.toLinearMap_apply]
  rw [← mp_comp]
  split_ifs with h
  · simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      AlgHom.toLinearMap_apply]
    rw [δ_apply, map_sum]
    have hb : mn b ∈ ({mn b, mn a} : Finset κ) := by simp
    have ha : mn a ∈ ({mn b, mn a} : Finset κ) := by simp
    have s1 : GlobalTheory.cubeSign ({mn b, mn a} : Finset κ) (mn b) = 1 :=
      GlobalTheory.cubeSign_eq_one_of_forall_le (by simp [h.le])
    have s2 : GlobalTheory.cubeSign ({mn b, mn a} : Finset κ) (mn a) = -1 := by
      have := GlobalTheory.cubeSign_erase_of_lt (t := {mn b, mn a}) hb h
      rw [Finset.erase_insert (by simp [h.ne]), GlobalTheory.cubeSign_singleton] at this
      omega
    rw [Fintype.sum_eq_add (⟨mn b, hb⟩ : ({mn b, mn a} : Finset κ)) ⟨mn a, ha⟩
      (fun e => h.ne (congrArg Subtype.val e))
      (by
        rintro ⟨x, hx⟩ ⟨h1, h2⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact (h1 rfl).elim
        · exact (h2 rfl).elim)]
    simp only [s1, s2, one_smul, neg_smul, map_neg, ← mp_comp]
    rw [neg_add, neg_neg, neg_add_eq_sub]
    refine congrArg₂ (· - ·) ?_ ?_
    · refine mp_cochain_congr F c (s := ⟨{mn b}, Finset.card_singleton _⟩)
        (s' := GlobalTheory.Cube.eraseIdx ⟨{mn b, mn a}, Finset.card_pair h.ne⟩ ⟨mn a, ha⟩) ?_ _ _
      show {mn b} = Finset.erase {mn b, mn a} (mn a)
      rw [Finset.pair_comm, Finset.erase_insert (by simp [h.ne'])]
    · refine mp_cochain_congr F c (s := ⟨{mn a}, Finset.card_singleton _⟩)
        (s' := GlobalTheory.Cube.eraseIdx ⟨{mn b, mn a}, Finset.card_pair h.ne⟩ ⟨mn b, hb⟩) ?_ _ _
      show {mn a} = Finset.erase {mn b, mn a} (mn b)
      rw [Finset.erase_insert (by simp [h.ne])]
  · have e : mn b = mn a := le_antisymm (mn_le_of_hom f) (not_lt.1 h)
    rw [LinearMap.zero_apply, sub_eq_zero]
    refine mp_cochain_congr F c (s := ⟨{mn b}, Finset.card_singleton _⟩)
      (s' := ⟨{mn a}, Finset.card_singleton _⟩) ?_ _ _
    show ({mn b} : Finset κ) = {mn a}
    rw [e]

end GlobalTheory.CechPoset
