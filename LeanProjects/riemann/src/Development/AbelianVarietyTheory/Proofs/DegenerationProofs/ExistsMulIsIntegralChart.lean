import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveClosureIsProjOverStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsIntegralMulPowOfSubalgebra
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsNmOfIsClVeronese

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem exists_mul_isIntegral_chart {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {J : Type} (t : J → Ω)
    {i : J} (hi : t i ≠ 0)
    (hfin : Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i})) Ω)
    (x : Ω) : ∃ a ∈ Algebra.adjoin o (Set.range fun j => t j / t i), a ≠ 0 ∧
      IsIntegral (Algebra.adjoin o (Set.range fun j => t j / t i)) (a * x) := by
  set A := Algebra.adjoin o (Set.range fun j => t j / t i) with hA
  set K := Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i}) with hKdef
  have hK : K ≤ Subfield.closure (A : Set Ω) := by
    refine Subfield.closure_le.mpr ?_
    rintro x (⟨a, rfl⟩ | ⟨k, j, rfl⟩)
    · exact Subfield.subset_closure (A.algebraMap_mem a)
    · have : t j / t k = (t j / t i) / (t k / t i) := by
        rw [div_div_div_cancel_right₀ hi]
      rw [this]
      exact div_mem (Subfield.subset_closure (Algebra.subset_adjoin ⟨j, rfl⟩))
        (Subfield.subset_closure (Algebra.subset_adjoin ⟨k, rfl⟩))
  have hAK : ∀ y ∈ A, y ∈ K := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact Subfield.subset_closure (Or.inr ⟨i, j, rfl⟩)
    | algebraMap a => exact Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  letI : Algebra A K := (A.val.toRingHom.codRestrict K fun y => hAK y y.2).toAlgebra
  haveI : IsScalarTower A K Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective A K).2 fun a b h =>
    Subtype.ext (congrArg (fun c : K => (c : Ω)) h)
  haveI : IsFractionRing A K := by
    refine IsFractionRing.of_field _ _ fun c => ?_
    obtain ⟨y, hy, w, hw, hc⟩ := Subfield.mem_closure_iff.mp (hK c.2)
    have hAA : Subring.closure (A : Set Ω) = A.toSubring := Subring.closure_eq A.toSubring
    rw [hAA] at hy hw
    exact ⟨⟨y, hy⟩, ⟨w, hw⟩, Subtype.ext hc.symm⟩
  have h1 : IsAlgebraic A x := (IsFractionRing.isAlgebraic_iff A K Ω).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨a, ha, h⟩ := h1.exists_integral_multiple
  exact ⟨a, a.2, fun h0 => ha (Subtype.ext h0), h⟩

theorem exists_isNm_isProjOver : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [IsDedekindDomain o] [CharZero Ω], Function.Injective (algebraMap o Ω) → ∀ (J : Type) [Fintype J] (t : J → Ω), (∃ i, t i ≠ 0) → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i})) Ω → ∃ M : RatModel o Ω, M.IsNm t ∧ IsProjOver M.s := by
  intro o Ω _ _ _ _ _ hinj J _ t ht hfin
  obtain ⟨e, n, z, he, hk, hint, hsum⟩ := GlobalTheory.exists_tuple_normalisation_charts o Ω hinj J t ht hfin
  obtain ⟨i, hi⟩ := ht
  obtain ⟨k, hzk⟩ := hk i
  have hL : ∀ y ∈ Algebra.adjoin o (Set.range fun l => z l / t i ^ e),
      y ∈ Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = z j / z i}) := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact Subfield.subset_closure (Or.inr ⟨k, j, by rw [hzk]⟩)
    | algebraMap a => exact Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  obtain ⟨M, hM, hP⟩ := GlobalTheory.T.exists_projectiveClosure_isProjOver o Ω n z ⟨k, by rw [hzk]; exact pow_ne_zero _ hi⟩ (by
    refine top_unique fun x _ => ?_
    obtain ⟨a, ha, ha0, h⟩ := exists_mul_isIntegral_chart t hi hfin x
    have h1 := hL _ ((hint i hi _).2 h)
    have h2 := hL _ ((hint i hi a).2 (isIntegral_algebraMap
      (R := Algebra.adjoin o (Set.range fun j => t j / t i)) (x := ⟨a, ha⟩)))
    have h3 := div_mem h1 h2
    rwa [mul_div_cancel_left₀ _ ha0] at h3)
  exact ⟨M, isNm_of_isCl_veronese o Ω M J t e n z he hM hk hint hsum, hP⟩

end GlobalTheory.ZH
