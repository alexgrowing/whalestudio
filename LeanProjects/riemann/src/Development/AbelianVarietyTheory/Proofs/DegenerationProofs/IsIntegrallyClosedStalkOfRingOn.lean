import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH
namespace RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}

theorem isIntegrallyClosed_stalk_of_ringOn {U : M.Z.Opens} (hU : IsAffineOpen U) {z : M.Z} (hz : z ∈ U)
    (h : ∀ x : Ω, IsIntegral (M.ringOn U) x → x ∈ M.ringOn U) :
    IsIntegrallyClosed (M.Z.presheaf.stalk z) := by
  have hne : (U : Set M.Z).Nonempty := ⟨z, hz⟩
  have : Nonempty U := ⟨⟨z, hz⟩⟩
  have : IsFractionRing (M.ringOn U) Ω := isFractionRing_ringOn hU hne
  have : IsIntegrallyClosed (M.ringOn U) := by
    rw [isIntegrallyClosed_iff Ω]
    intro x hx
    exact ⟨⟨x, h x hx⟩, rfl⟩
  have : IsIntegrallyClosed Γ(M.Z, U) := IsIntegrallyClosed.of_equiv (M.sectionsEquiv U hne).symm
  let _ := TopCat.Presheaf.algebra_section_stalk M.Z.presheaf (⟨z, hz⟩ : U)
  have := hU.isLocalization_stalk ⟨z, hz⟩
  exact isIntegrallyClosed_of_isLocalization (M.Z.presheaf.stalk z) _
    (Ideal.primeCompl_le_nonZeroDivisors (hU.primeIdealOf ⟨z, hz⟩).asIdeal)

theorem IsNm.isNormalScheme {J : Type} {t : J → Ω} (h : M.IsNm t) : IsNormalScheme M.Z := by
  obtain ⟨hd, hU⟩ := h
  have key : ∀ z : M.Z, IsIntegrallyClosed (M.Z.presheaf.stalk z) := by
    intro z
    obtain ⟨i, hi⟩ := hd z
    obtain ⟨U, hUa, hUeq, hmem⟩ := hU i hi.1
    have hz : z ∈ (U : Set M.Z) := hUeq ▸ hi
    refine isIntegrallyClosed_stalk_of_ringOn hUa hz fun x hx => ?_
    set A := Algebra.adjoin o (Set.range fun j => t j / t i)
    have hle : A ≤ M.ringOn U := fun y hy => (hmem y).2 (isIntegral_algebraMap (x := (⟨y, hy⟩ : A)))
    let : Algebra A (M.ringOn U) := (Subalgebra.inclusion hle).toRingHom.toAlgebra
    have : IsScalarTower A (M.ringOn U) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have : Algebra.IsIntegral A (M.ringOn U) := ⟨fun y =>
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom A (M.ringOn U) Ω) Subtype.val_injective).1
        ((hmem y).1 y.2)⟩
    exact (hmem x).2 (isIntegral_trans x hx)
  exact fun z => ⟨(M.stalkHom_injective z).isDomain _, key z⟩

theorem div_prod_iff {J J' : Type} {t : J → Ω} {t' : J' → Ω} {i : J} {i' : J'} {z : M.Z} :
    M.Div (fun q : J × J' => t q.1 * t' q.2) (i, i') z ↔ M.Div t i z ∧ M.Div t' i' z := by
  simp only [RatModel.Div]
  constructor
  · rintro ⟨h0, h⟩
    have hi : t i ≠ 0 := left_ne_zero_of_mul h0
    have hi' : t' i' ≠ 0 := right_ne_zero_of_mul h0
    refine ⟨⟨hi, fun j => ?_⟩, ⟨hi', fun j' => ?_⟩⟩
    · simpa [mul_div_mul_right _ _ hi'] using h (j, i')
    · simpa [mul_div_mul_left _ _ hi] using h (i, j')
  · rintro ⟨⟨hi, h⟩, ⟨hi', h'⟩⟩
    refine ⟨mul_ne_zero hi hi', fun q => ?_⟩
    rw [mul_div_mul_comm]
    exact mul_mem (h q.1) (h' q.2)

theorem div_finprod_iff {A : Type} [Fintype A] {JJ : A → Type} {tt : ∀ a, JJ a → Ω} {q : ∀ a, JJ a} {z : M.Z} :
    M.Div (fun q : ∀ a, JJ a => ∏ a, tt a (q a)) q z ↔ ∀ a, M.Div (tt a) (q a) z := by
  simp only [RatModel.Div]
  constructor
  · rintro ⟨h0, h⟩
    have hne : ∀ a, tt a (q a) ≠ 0 := fun a => Finset.prod_ne_zero_iff.1 h0 a (Finset.mem_univ a)
    intro a
    refine ⟨hne a, fun j => ?_⟩
    have hj := h (Function.update q a j)
    rw [← Finset.prod_div_distrib, Finset.prod_eq_single a] at hj
    · simpa using hj
    · intro b _ hb
      simp [Function.update_of_ne hb, div_self (hne b)]
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  · intro h
    refine ⟨Finset.prod_ne_zero_iff.2 fun a _ => (h a).1, fun q' => ?_⟩
    rw [← Finset.prod_div_distrib]
    exact prod_mem fun a _ => (h a).2 (q' a)

theorem hasDiv_finprod_iff {A : Type} [Fintype A] {JJ : A → Type} {tt : ∀ a, JJ a → Ω} :
    M.HasDiv (fun q : ∀ a, JJ a => ∏ a, tt a (q a)) ↔ ∀ a, M.HasDiv (tt a) := by
  simp only [RatModel.HasDiv]
  constructor
  · intro h a z
    obtain ⟨q, hq⟩ := h z
    exact ⟨q a, div_finprod_iff.1 hq a⟩
  · intro h z
    choose q hq using fun a => h a z
    exact ⟨q, div_finprod_iff.2 hq⟩

end RatModel

theorem isNm_normal_and_div_prod : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (J : Type) (t : J → Ω), (M.IsNm t → IsNormalScheme M.Z) ∧ (∀ (J' : Type) (t' : J' → Ω) (i : J) (i' : J') (z : M.Z), M.Div (fun q : J × J' => t q.1 * t' q.2) (i, i') z ↔ M.Div t i z ∧ M.Div t' i' z) ∧ (∀ (A : Type) [Fintype A] (JJ : A → Type) (tt : ∀ a, JJ a → Ω), M.HasDiv (fun q : ∀ a, JJ a => ∏ a, tt a (q a)) ↔ ∀ a, M.HasDiv (tt a)) := by
  intro o Ω _ _ _ M J t
  exact ⟨fun h => h.isNormalScheme, fun J' t' i i' z => RatModel.div_prod_iff,
    fun A _ JJ tt => RatModel.hasDiv_finprod_iff⟩

end GlobalTheory.ZH
end
