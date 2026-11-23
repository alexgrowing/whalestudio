import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCycAwayHomComplex

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.CycLift

open Polynomial

theorem exists_injective_hom {n : ℕ} (hn : n ≠ 0) {V : Type} [CommRing V] [IsDomain V] [CharZero V]
    {u : V} (hu : IsPrimitiveRoot u n) (hnV : IsUnit (n : V)) :
    ∃ f : cycAway n →+* V, Function.Injective f ∧ f (zetaAway n) = u := by
  have hp := Nat.pos_of_ne_zero hn
  let L := FractionRing V
  have hinj : Function.Injective (algebraMap V L) := IsFractionRing.injective V L
  haveI : CharZero L := charZero_of_injective_algebraMap hinj
  have hz : IsPrimitiveRoot (zetaAway n : ℂ) n := Complex.isPrimitiveRoot_exp n hn
  have hi : IsIntegral ℚ (zetaAway n : ℂ) := (hz.isIntegral hp).tower_top
  let K := IntermediateField.adjoin ℚ {(zetaAway n : ℂ)}
  have hle : cycAway n ≤ K.toSubfield.toSubring := by
    refine Subring.closure_le.2 ?_
    rintro x (rfl | rfl)
    · exact IntermediateField.mem_adjoin_simple_self ℚ _
    · exact K.inv_mem (natCast_mem K n)
  have huL : IsPrimitiveRoot (algebraMap V L u) n := hu.map_of_injective hinj
  have hr : algebraMap V L u ∈ (minpoly ℚ (zetaAway n : ℂ)).aroots L := by
    rw [← cyclotomic_eq_minpoly_rat hz hp, mem_aroots]
    refine ⟨cyclotomic_ne_zero n ℚ, ?_⟩
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact huL.isRoot_cyclotomic hp
  let g : K →ₐ[ℚ] L := (IntermediateField.algHomAdjoinIntegralEquiv ℚ hi).symm ⟨_, hr⟩
  have hg : g (IntermediateField.AdjoinSimple.gen ℚ (zetaAway n : ℂ)) = algebraMap V L u :=
    IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hi ⟨_, hr⟩
  let f₀ : cycAway n →+* L := g.toRingHom.comp (Subring.inclusion hle)
  have hf₀ : Function.Injective f₀ := g.toRingHom.injective.comp (Subring.inclusion_injective hle)
  have hζ : f₀ (zetaAway n) = algebraMap V L u := hg
  have hmem : ∀ x, f₀ x ∈ (algebraMap V L).range := by
    rintro ⟨x, hx⟩
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨u, hζ.symm⟩
      · refine ⟨↑hnV.unit⁻¹, ?_⟩
        have e : (n : cycAway n) * ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ = 1 :=
          Subtype.ext (by simpa using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn : (n : ℂ) ≠ 0))
        have e₁ := congrArg f₀ e
        rw [map_mul, map_natCast, map_one] at e₁
        have e₂ : (n : L) * algebraMap V L ↑hnV.unit⁻¹ = 1 := by
          rw [← map_natCast (algebraMap V L) n, ← map_mul, hnV.mul_val_inv, map_one]
        exact mul_left_cancel₀ (left_ne_zero_of_mul_eq_one e₂) (e₂.trans e₁.symm)
    | zero => exact Set.mem_of_eq_of_mem (map_zero f₀) (zero_mem _)
    | one => exact Set.mem_of_eq_of_mem (map_one f₀) (one_mem _)
    | add x y hx hy ihx ihy => exact (map_add f₀ ⟨x, hx⟩ ⟨y, hy⟩) ▸ add_mem ihx ihy
    | neg x hx ih => exact (map_neg f₀ ⟨x, hx⟩) ▸ neg_mem ih
    | mul x y hx hy ihx ihy => exact (map_mul f₀ ⟨x, hx⟩ ⟨y, hy⟩) ▸ mul_mem ihx ihy
  let e := RingEquiv.ofBijective (algebraMap V L).rangeRestrict
    ⟨fun a b h => hinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  have he : ∀ y, algebraMap V L (e.symm y) = y := fun y => congrArg Subtype.val (e.apply_symm_apply y)
  refine ⟨e.symm.toRingHom.comp (f₀.codRestrict _ hmem),
    e.symm.injective.comp (fun a b h => hf₀ (congrArg Subtype.val h)), hinj ?_⟩
  rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, he]
  exact hζ

end GlobalTheory.CycLift
