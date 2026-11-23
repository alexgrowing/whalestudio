import Mathlib
import GroundTheory.TateCohomology.TateTheorem
import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.IntScalars
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory Limits groupCohomology

variable {Γ : Type} [Group Γ] [Fintype Γ]

theorem additive_addMonoidHom_int_eq_zero (f : Additive Γ →+ ℤ) : f = 0 := by
  refine AddMonoidHom.ext fun g => ?_
  have h : (Nat.card (Additive Γ) : ℤ) * f g = 0 := by
    rw [← nsmul_eq_mul, ← map_nsmul, card_nsmul_eq_zero', map_zero]
  exact (mul_eq_zero.1 h).resolve_left (Nat.cast_ne_zero.2 Nat.card_pos.ne')

theorem isZero_groupCohomology_one_trivial_int :
    IsZero (groupCohomology (Rep.trivial ℤ Γ ℤ) 1) := by
  refine IsZero.of_iso ?_ (H1IsoOfIsTrivial (Rep.trivial ℤ Γ ℤ))
  refine @ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun f g => ?_⟩
  rw [additive_addMonoidHom_int_eq_zero f, additive_addMonoidHom_int_eq_zero g]

theorem subsingleton_groupCohomology_three_of_tate_int (M : Rep ℤ Γ) (u : groupCohomology M 2)
    (h1 : ∀ S : Subgroup Γ, IsZero (groupCohomology (Rep.res S.subtype M) 1))
    (h2 : ∀ S : Subgroup Γ,
      addOrderOf (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype M)) 2 u) = Nat.card S)
    (h3 : ∀ (S : Subgroup Γ) (y : groupCohomology (Rep.res S.subtype M) 2),
      ∃ m : ℤ, y = m • groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype M)) 2 u) :
    Subsingleton (groupCohomology M 3) := by
  have hT1 : IsZero (tateCohomology (Rep.trivial ℤ Γ ℤ) ((1 : ℕ) : ℤ)) :=
    isZero_groupCohomology_one_trivial_int.of_iso
      ((TateCohomology.isoGroupCohomology 1).app (Rep.trivial ℤ Γ ℤ))
  have hT3 : IsZero (tateCohomology M (((1 : ℕ) : ℤ) + 2)) :=
    hT1.of_iso (GroundTheory.GroupCoh.tateTheoremIsoTop M u h1 h2 h3 _).symm
  have e3 : (((1 : ℕ) : ℤ) + 2) = ((3 : ℕ) : ℤ) := by norm_num
  rw [e3] at hT3
  exact ModuleCat.subsingleton_of_isZero
    (hT3.of_iso ((TateCohomology.isoGroupCohomology 3).app M).symm)

theorem subsingleton_groupCohomology_three_of_tate (M : Rep.{0} (ULift.{0} ℤ) Γ)
    (u : groupCohomology M 2)
    (h1 : ∀ S : Subgroup Γ, IsZero (groupCohomology (Rep.res S.subtype M) 1))
    (h2 : ∀ S : Subgroup Γ,
      addOrderOf ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype M)) 2).hom u) = Nat.card S)
    (h3 : ∀ (S : Subgroup Γ) (y : groupCohomology (Rep.res S.subtype M) 2),
      ∃ m : ℤ, y = m • (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype M)) 2).hom u) :
    Subsingleton (groupCohomology M 3) := by
  have H := subsingleton_groupCohomology_three_of_tate_int (uliftIntToIntRep M)
    (groupCohomologyULiftIntAddEquiv M 2 u) (fun S => ?_) (fun S => ?_) (fun S y => ?_)
  · exact (groupCohomologyULiftIntAddEquiv M 3).injective.subsingleton
  · have : Subsingleton (groupCohomology (Rep.res S.subtype M) 1) :=
      ModuleCat.subsingleton_of_isZero (h1 S)
    have : Subsingleton (groupCohomology (uliftIntToIntRep (Rep.res S.subtype M)) 1) :=
      (groupCohomologyULiftIntAddEquiv (Rep.res S.subtype M) 1).symm.injective.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  · have e := groupCohomologyULiftIntAddEquiv_map_subtype M S 2 u
    change addOrderOf ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (uliftIntToIntRep M))) 2).hom
      (groupCohomologyULiftIntAddEquiv M 2 u)) = Nat.card S
    rw [← e, AddEquiv.addOrderOf_eq]
    exact h2 S
  · obtain ⟨m, hm⟩ := h3 S ((groupCohomologyULiftIntAddEquiv (Rep.res S.subtype M) 2).symm y)
    refine ⟨m, ?_⟩
    change y = m • (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (uliftIntToIntRep M))) 2).hom
      (groupCohomologyULiftIntAddEquiv M 2 u)
    rw [← groupCohomologyULiftIntAddEquiv_map_subtype, ← map_zsmul, ← hm, AddEquiv.apply_symm_apply]

end GroundTheory.ProfCoh
