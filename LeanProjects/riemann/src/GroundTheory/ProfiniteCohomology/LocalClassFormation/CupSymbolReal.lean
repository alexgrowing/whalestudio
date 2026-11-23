import Mathlib
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbol
import GroundTheory.ProfiniteCohomology.CyclicCupBrauer
import GroundTheory.ProfiniteCohomology.CyclicCup
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory groupCohomology IntermediateField GroundTheory.GroupCoh

attribute [local instance 2000] Rep.hV2 Submodule.module Submodule.Quotient.module

section Comparison

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Fintype G]

theorem cohomologyToGroupCohomology_cupCharClassProf (A : Rep ℤ G) [IsDiscreteRep A]
    (χ : Additive G →ₜ+ QZ) (a : A.ρ.invariants) :
    (cohomologyToGroupCohomology A 2).hom ((cupCharClassProf A χ).hom a) =
      (cupCharClass A (charAdd χ)).hom a := by
  obtain ⟨w, hw, hwc⟩ := exists_cocycle_cupCharClassProf A χ a
  rw [← hw, cupCharClass_apply_charCocycle]
  have e := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (cochainsComplexι A) 2) w
  refine e.trans ?_
  change (groupCohomology.π A 2).hom _ = (groupCohomology.π A 2).hom ((isoCocycles₂ A).inv.hom _)
  congr 1
  apply (ModuleCat.mono_iff_injective ((inhomogeneousCochains A).iCycles 2)).1 inferInstance
  have e1 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i (cochainsComplexι A) 2) w
  refine e1.trans ?_
  rw [isoCocycles₂_inv_comp_iCocycles_apply]
  funext v
  exact hwc v

variable [DiscreteTopology G] [IsCyclic G]

theorem cupCharClassProf_surjective (A : Rep ℤ G) [IsDiscreteRep A] (χ : Additive G →ₜ+ QZ)
    (hχ : Function.Injective χ) : Function.Surjective (cupCharClassProf A χ).hom := by
  intro x
  have hinj : Function.Injective (cohomologyToGroupCohomology A 2).hom := by
    rw [← cohomologyIsoGroupCohomology_hom]
    exact (ModuleCat.mono_iff_injective _).1 inferInstance
  have hχ' : Function.Injective (charAdd χ) := QZ.toAddCircle.injective.comp hχ
  obtain ⟨a, ha⟩ := cupCharClass_surjective (A := A) (charAdd χ) hχ'
    ((cohomologyToGroupCohomology A 2).hom x)
  exact ⟨a, hinj (by rw [cohomologyToGroupCohomology_cupCharClassProf, ha])⟩

end Comparison

section OrderTwo

variable {G : Type} [Group G] [Fintype G]

theorem eq_of_ne_one_of_card_eq_two (h : Fintype.card G = 2) {g g' : G} (hg : g ≠ 1) (hg' : g' ≠ 1) :
    g = g' := by
  classical
  by_contra hne
  have h3 : ({1, g, g'} : Finset G).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hne]
    simp [Ne.symm hg, Ne.symm hg']
  have := Finset.card_le_univ ({1, g, g'} : Finset G)
  omega

theorem char_eq_half_of_card_eq_two (h : Fintype.card G = 2) (χ : Additive G →+ QZ) {g : G}
    (hg : χ (Additive.ofMul g) ≠ 0) : χ (Additive.ofMul g) = QZ.mk (1 / 2) := by
  have h2 : (2 : ℕ) • χ (Additive.ofMul g) = 0 := by
    rw [← map_nsmul, ← ofMul_pow, ← h, pow_card_eq_one, ofMul_one, map_zero]
  obtain ⟨m, hm⟩ := QZ.exists_eq_nsmul_mk_one_div (by norm_num) h2
  rw [hm] at hg ⊢
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
  · exfalso
    apply hg
    rw [mul_nsmul]
    have := QZ.nsmul_mk_one_div 2
    rw [this, nsmul_zero]
  · rw [add_nsmul, one_nsmul, mul_nsmul]
    have := QZ.nsmul_mk_one_div 2
    rw [this, nsmul_zero, zero_add]
    norm_num

end OrderTwo

section Quadratic

variable (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] [FiniteDimensional F Ω] [IsGalois F Ω]

theorem coe_toMul_norm_galUnitsZ (m : Additive Ωˣ) :
    (((Additive.toMul ((galUnitsZ F Ω).ρ.norm m) : Ωˣ) : Ω)) =
      algebraMap F Ω (Algebra.norm F ((Additive.toMul m : Ωˣ) : Ω)) := by
  rw [Algebra.norm_eq_prod_automorphisms, Representation.norm, LinearMap.sum_apply, toMul_sum,
    Units.coe_prod]
  exact Finset.prod_congr rfl fun σ _ => coe_galUnitsHom_apply F Ω σ _

theorem unitsInvariant_mem_normRangeInvariants_iff (a : Fˣ) :
    unitsInvariant F Ω a ∈ normRangeInvariants (galUnitsZ F Ω) ↔
      (a : F) ∈ Set.range (Algebra.norm F : Ω → F) := by
  rw [mem_normRangeInvariants_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨((Additive.toMul m : Ωˣ) : Ω), (algebraMap F Ω).injective ?_⟩
    rw [← coe_toMul_norm_galUnitsZ, hm]
    rfl
  · rintro ⟨z, hz⟩
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [Algebra.norm_zero] at hz
      exact a.ne_zero hz.symm
    refine ⟨Additive.ofMul (Units.mk0 z hz0), ?_⟩
    apply Additive.toMul.injective
    apply Units.ext
    refine (coe_toMul_norm_galUnitsZ F Ω _).trans ?_
    change algebraMap F Ω (Algebra.norm F z) = algebraMap F Ω a
    rw [hz]

theorem exists_unitsInvariant_eq (u : (galUnitsZ F Ω).ρ.invariants) : ∃ a : Fˣ, unitsInvariant F Ω a = u := by
  have hfix : ∀ σ : Gal(Ω/F), σ ((Additive.toMul (u : Additive Ωˣ) : Ωˣ) : Ω) =
      ((Additive.toMul (u : Additive Ωˣ) : Ωˣ) : Ω) := fun σ => by
    have := congrArg (fun v : Additive Ωˣ => ((Additive.toMul v : Ωˣ) : Ω)) (u.2 σ)
    exact (coe_galUnitsHom_apply F Ω σ _).symm.trans this
  have hfix' : ∀ σ : Gal(Ω/F), σ (((Additive.toMul (u : Additive Ωˣ) : Ωˣ)⁻¹ : Ωˣ) : Ω) =
      (((Additive.toMul (u : Additive Ωˣ) : Ωˣ)⁻¹ : Ωˣ) : Ω) := fun σ => by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hfix]
  obtain ⟨x, hx⟩ := (IsGalois.mem_range_algebraMap_iff_fixed _).2 hfix
  obtain ⟨y, hy⟩ := (IsGalois.mem_range_algebraMap_iff_fixed _).2 hfix'
  refine ⟨⟨x, y, (algebraMap F Ω).injective ?_, (algebraMap F Ω).injective ?_⟩, Subtype.ext ?_⟩
  · rw [map_mul, hx, hy, map_one, Units.mul_inv]
  · rw [map_mul, hx, hy, map_one, Units.inv_mul]
  · apply Additive.toMul.injective
    apply Units.ext
    exact hx

omit [FiniteDimensional F Ω] [IsGalois F Ω] in
theorem unitsInvariant_mul (a b : Fˣ) :
    unitsInvariant F Ω (a * b) = unitsInvariant F Ω a + unitsInvariant F Ω b := by
  exact Subtype.ext (congrArg Additive.ofMul (map_mul (Units.map (algebraMap F Ω : F →* Ω)) a b))

end Quadratic

section QuadraticInv

variable (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] [FiniteDimensional F Ω] [IsGalois F Ω]

theorem galCupClass_eq_zero_of_mem_range_norm (χ : Additive Gal(Ω/F) →ₜ+ QZ) {a : Fˣ}
    (ha : (a : F) ∈ Set.range (Algebra.norm F : Ω → F)) : galCupClass F Ω χ a = 0 := by
  have hinj : Function.Injective (cohomologyToGroupCohomology (galUnitsZ F Ω) 2).hom := by
    rw [← cohomologyIsoGroupCohomology_hom]
    exact (ModuleCat.mono_iff_injective _).1 inferInstance
  apply hinj
  rw [map_zero, galCupClass, cohomologyToGroupCohomology_cupCharClassProf]
  exact cupCharClass_eq_zero_of_mem _ _ ((unitsInvariant_mem_normRangeInvariants_iff F Ω a).2 ha)

theorem galCupClass_eq_zero_iff_of_injective (χ : Additive Gal(Ω/F) →ₜ+ QZ)
    (hχ : Function.Injective χ) (a : Fˣ) :
    galCupClass F Ω χ a = 0 ↔ (a : F) ∈ Set.range (Algebra.norm F : Ω → F) := by
  have hχ' : Function.Injective (charAdd χ) := QZ.toAddCircle.injective.comp hχ
  have := isCyclic_of_injective_char (charAdd χ) hχ'
  have hinj : Function.Injective (cohomologyToGroupCohomology (galUnitsZ F Ω) 2).hom := by
    rw [← cohomologyIsoGroupCohomology_hom]
    exact (ModuleCat.mono_iff_injective _).1 inferInstance
  rw [← unitsInvariant_mem_normRangeInvariants_iff, ← cupCharClass_eq_zero_iff (charAdd χ) hχ',
    ← cohomologyToGroupCohomology_cupCharClassProf, ← map_zero (cohomologyToGroupCohomology _ 2).hom,
    hinj.eq_iff]
  rfl

open Classical in

noncomputable def quadraticInvFun (x : cohomology (galUnitsZ F Ω) 2) : QZ :=
  if x = 0 then 0 else QZ.mk (1 / 2)

omit [FiniteDimensional F Ω] in
theorem quadraticInvFun_zero : quadraticInvFun F Ω 0 = 0 := by
  simp [quadraticInvFun]

omit [FiniteDimensional F Ω] in
theorem quadraticInvFun_of_ne_zero {x : cohomology (galUnitsZ F Ω) 2} (hx : x ≠ 0) :
    quadraticInvFun F Ω x = QZ.mk (1 / 2) := by
  simp [quadraticInvFun, hx]

theorem quadraticInvFun_galCupClass (h2 : Module.finrank F Ω ≤ 2) (χ : Additive Gal(Ω/F) →ₜ+ QZ)
    (a : Fˣ) (g : Gal(Ω/F)) (hg : g = 1 ↔ (a : F) ∈ Set.range (Algebra.norm F : Ω → F)) :
    quadraticInvFun F Ω (galCupClass F Ω χ a) = χ (Additive.ofMul g) := by
  by_cases ha : (a : F) ∈ Set.range (Algebra.norm F : Ω → F)
  · rw [hg.2 ha, ofMul_one, map_zero, galCupClass_eq_zero_of_mem_range_norm F Ω χ ha,
      quadraticInvFun_zero]
  have hg1 : g ≠ 1 := fun h => ha (hg.1 h)
  have hcard : Fintype.card Gal(Ω/F) = 2 := by
    have h1 : Fintype.card Gal(Ω/F) = Module.finrank F Ω := by
      rw [← Nat.card_eq_fintype_card]
      exact IsGalois.card_aut_eq_finrank F Ω
    have h3 : 1 < Fintype.card Gal(Ω/F) := Fintype.one_lt_card_iff.2 ⟨g, 1, hg1⟩
    omega
  by_cases hχg : χ (Additive.ofMul g) = 0
  · have hχ0 : χ = 0 := by
      ext x
      by_cases hx : Additive.toMul x = 1
      · rw [show x = Additive.ofMul 1 from hx ▸ rfl, ofMul_one, map_zero]
        rfl
      · rw [show x = Additive.ofMul g from eq_of_ne_one_of_card_eq_two hcard hx hg1 ▸ rfl, hχg]
        rfl
    rw [hχg, hχ0]
    change quadraticInvFun F Ω ((cupCharClassProf (galUnitsZ F Ω) 0).hom _) = 0
    rw [cupCharClassProf_zero, quadraticInvFun_zero]
  · have hχinj : Function.Injective χ := (injective_iff_map_eq_zero χ).2 fun x hx => by
      by_contra hne
      have hx1 : Additive.toMul x ≠ 1 := fun h => hne (by rw [show x = Additive.ofMul 1 from h ▸ rfl,
        ofMul_one])
      exact hχg (by rw [← eq_of_ne_one_of_card_eq_two hcard hx1 hg1]; exact hx)
    rw [quadraticInvFun_of_ne_zero F Ω (fun h => ha ((galCupClass_eq_zero_iff_of_injective F Ω χ
      hχinj a).1 h))]
    exact (char_eq_half_of_card_eq_two hcard χ.toAddMonoidHom hχg).symm

end QuadraticInv

section QuadraticHom

theorem QZ.mk_half_ne_zero : QZ.mk (1 / 2) ≠ 0 := by
  rw [Ne, QZ.mk_eq_zero_iff]
  rintro ⟨n, hn⟩
  have h2 : (2 * n : ℚ) = 1 := by rw [hn]; norm_num
  have h3 : (2 * n : ℤ) = 1 := by exact_mod_cast h2
  omega

theorem QZ.mk_half_add_mk_half : QZ.mk (1 / 2) + QZ.mk (1 / 2) = 0 := by
  rw [← two_nsmul]
  have := QZ.nsmul_mk_one_div 2
  norm_num at this
  exact this

variable (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] [FiniteDimensional F Ω] [IsGalois F Ω]

omit [IsGalois F Ω] in
theorem card_gal_le_two (h2 : Module.finrank F Ω ≤ 2) : Fintype.card Gal(Ω/F) ≤ 2 := by
  exact (AlgEquiv.card_le (F := F) (K := Ω)).trans h2

open Classical in

noncomputable def quadraticChar (h2 : Module.finrank F Ω ≤ 2) : Additive Gal(Ω/F) →ₜ+ QZ where
  toFun x := if Additive.toMul x = 1 then 0 else QZ.mk (1 / 2)
  map_zero' := by simp
  map_add' x y := by
    by_cases hx : Additive.toMul x = 1
    · have : Additive.toMul (x + y) = Additive.toMul y := by rw [toMul_add, hx, one_mul]
      simp [hx, this]
    by_cases hy : Additive.toMul y = 1
    · have : Additive.toMul (x + y) = Additive.toMul x := by rw [toMul_add, hy, mul_one]
      simp [hy, this]
    have hcard : Fintype.card Gal(Ω/F) = 2 := by
      have := card_gal_le_two F Ω h2
      have h3 : 1 < Fintype.card Gal(Ω/F) := Fintype.one_lt_card_iff.2 ⟨_, 1, hx⟩
      omega
    have hxy : Additive.toMul (x + y) = 1 := by
      rw [toMul_add, ← eq_of_ne_one_of_card_eq_two hcard hx hy, ← sq, ← hcard, pow_card_eq_one]
    simp only [hxy, hx, hy, if_true, if_false]
    exact QZ.mk_half_add_mk_half.symm
  continuous_toFun := continuous_of_discreteTopology

omit [IsGalois F Ω] in
open Classical in
theorem quadraticChar_injective (h2 : Module.finrank F Ω ≤ 2) :
    Function.Injective (quadraticChar F Ω h2) := by
  refine (injective_iff_map_eq_zero (quadraticChar F Ω h2)).2 fun x hx => ?_
  by_contra hne
  have h1 : Additive.toMul x ≠ 1 := fun h => hne (by rw [show x = Additive.ofMul 1 from h ▸ rfl, ofMul_one])
  change (if Additive.toMul x = 1 then 0 else QZ.mk (1 / 2)) = 0 at hx
  rw [if_neg h1] at hx
  exact QZ.mk_half_ne_zero hx

noncomputable def quadraticInv (h2 : Module.finrank F Ω ≤ 2)
    (hN : ∀ a b : Fˣ, (a : F) ∉ Set.range (Algebra.norm F : Ω → F) →
      (b : F) ∉ Set.range (Algebra.norm F : Ω → F) → ((a * b : Fˣ) : F) ∈ Set.range (Algebra.norm F : Ω → F)) :
    cohomology (galUnitsZ F Ω) 2 →+ QZ where
  toFun := quadraticInvFun F Ω
  map_zero' := quadraticInvFun_zero F Ω
  map_add' x y := by
    by_cases hx : x = 0
    · rw [hx, zero_add, quadraticInvFun_zero, zero_add]
    by_cases hy : y = 0
    · rw [hy, add_zero, quadraticInvFun_zero, add_zero]
    have hχ := quadraticChar_injective F Ω h2
    have := isCyclic_of_injective_char (charAdd (quadraticChar F Ω h2))
      (QZ.toAddCircle.injective.comp hχ)
    obtain ⟨u, rfl⟩ := cupCharClassProf_surjective (galUnitsZ F Ω) _ hχ x
    obtain ⟨v, rfl⟩ := cupCharClassProf_surjective (galUnitsZ F Ω) _ hχ y
    obtain ⟨a, rfl⟩ := exists_unitsInvariant_eq F Ω u
    obtain ⟨b, rfl⟩ := exists_unitsInvariant_eq F Ω v
    have ha : (a : F) ∉ Set.range (Algebra.norm F : Ω → F) := fun h =>
      hx (galCupClass_eq_zero_of_mem_range_norm F Ω _ h)
    have hb : (b : F) ∉ Set.range (Algebra.norm F : Ω → F) := fun h =>
      hy (galCupClass_eq_zero_of_mem_range_norm F Ω _ h)
    have hab : (cupCharClassProf (galUnitsZ F Ω) (quadraticChar F Ω h2)).hom (unitsInvariant F Ω a) +
        (cupCharClassProf (galUnitsZ F Ω) (quadraticChar F Ω h2)).hom (unitsInvariant F Ω b) = 0 := by
      rw [← map_add, ← unitsInvariant_mul]
      exact galCupClass_eq_zero_of_mem_range_norm F Ω _ (hN a b ha hb)
    rw [hab, quadraticInvFun_zero, quadraticInvFun_of_ne_zero F Ω hx,
      quadraticInvFun_of_ne_zero F Ω hy, QZ.mk_half_add_mk_half]

theorem quadraticInv_apply (h2 : Module.finrank F Ω ≤ 2) (hN) (x : cohomology (galUnitsZ F Ω) 2) :
    quadraticInv F Ω h2 hN x = quadraticInvFun F Ω x :=
  rfl

theorem quadraticInv_injective (h2 : Module.finrank F Ω ≤ 2) (hN) :
    Function.Injective (quadraticInv F Ω h2 hN) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  by_contra hne
  rw [quadraticInv_apply, quadraticInvFun_of_ne_zero F Ω hne] at hx
  exact QZ.mk_half_ne_zero hx

theorem quadraticInv_galCupClass (h2 : Module.finrank F Ω ≤ 2) (hN) (χ : Additive Gal(Ω/F) →ₜ+ QZ)
    (a : Fˣ) (g : Gal(Ω/F)) (hg : g = 1 ↔ (a : F) ∈ Set.range (Algebra.norm F : Ω → F)) :
    quadraticInv F Ω h2 hN (galCupClass F Ω χ a) = χ (Additive.ofMul g) :=
  quadraticInvFun_galCupClass F Ω h2 χ a g hg

end QuadraticHom

end GroundTheory.ProfCoh
