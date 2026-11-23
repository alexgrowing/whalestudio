import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSysFFMemFinitePerpProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsNormPull
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

namespace GlobalTheory

theorem thetaSys_sum_perp_char_eq_zero :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (F : Type) [Field F] (ζ : F), IsPrimitiveRoot ζ ((S.r * S.N) ^ 2) → ∀ (H : AddSubgroup S.Gam) [Fintype (S.perp H)] (a : S.Gam), a ∉ H → ∑ t : S.perp H, ζ ^ (S.r * S.N * (eStd S.g _ (t : S.Gam) a).val) = 0 := by
  intro o Ω _ _ _ _ S F _ ζ hζ H _ a ha
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have : NeZero ((S.r * S.N) ^ 2) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
  have hω : IsPrimitiveRoot (ζ ^ (S.r * S.N)) (S.r * S.N) :=
    hζ.pow (NeZero.pos _) (by ring)
  let χ : AddChar (ZMod (S.r * S.N)) F := AddChar.zmodChar _ hω.pow_eq_one
  have hχ : ∀ b, χ b = 1 → b = 0 := fun b hb =>
    ((AddChar.zmodChar_primitive_of_primitive_root _ hω).zmod_char_eq_one_iff _ b).mp hb
  let f : S.perp H →+ ZMod (S.r * S.N) :=
    { toFun := fun t => eStd S.g _ (t : S.Gam) a
      map_zero' := by simp [eStd]
      map_add' := fun x y => by
        simp only [eStd, AddSubgroup.coe_add, Pi.add_apply, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring }
  have hne : χ.compAddMonoidHom f ≠ 1 := by
    intro h
    apply ha
    rw [← (thetaSys_FF_mem_finite_perp_proj o Ω S).2.2.1 H]
    intro t ht
    have h1 : f ⟨t, ht⟩ = 0 := hχ _ (DFunLike.congr_fun h ⟨t, ht⟩)
    have h2 : eStd S.g _ t a = 0 := h1
    rw [ThetaProj.eStd_swap, h2, neg_zero]
  have h0 : ∑ t : S.perp H, χ (f t) = 0 := AddChar.sum_eq_zero_of_ne_one hne
  rw [← h0]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [pow_mul]
  rfl

end GlobalTheory
