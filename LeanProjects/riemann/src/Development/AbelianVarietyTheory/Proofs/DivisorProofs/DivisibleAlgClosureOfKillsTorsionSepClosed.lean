import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAbelianVarietyTorsionSepClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAbelianVarietyTorsionSepClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeDimensionAbelianVarietyField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectivePointsLargerFieldGalois
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianVarietyTorsionFiniteEndomorphismDivisible
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SepClosedDivisible

theorem divisible_algClosure : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ m : ℕ, (m : K) ≠ 0 → ∀ f : A ⟶ A, IsMonHom f → (∀ x : ptOver K Ω ⟶ A, x ^ m = 1 → x ≫ f = 1) → ∃ h : (Over.pullback (spMap (algebraMap K (AlgebraicClosure Ω)))).obj A ⟶ (Over.pullback (spMap (algebraMap K (AlgebraicClosure Ω)))).obj A, IsMonHom h ∧ (Over.pullback (spMap (algebraMap K (AlgebraicClosure Ω)))).map f = h ^ m := by
  intro K Ω _ _ _ _ A _ hA m hm f hf hkill
  set L := AlgebraicClosure Ω
  set t : Sp L ⟶ Sp K := spMap (algebraMap K L) with ht
  let j : Ω →ₐ[K] L := IsScalarTower.toAlgHom K Ω L
  have hmL : (m : L) ≠ 0 := by
    intro h; apply hm; apply (algebraMap K L).injective; simpa using h
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (by simp)
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim K A hA
  have hcΩ := GlobalTheory.SepClosedTorsion.card_torsion_sepClosed K Ω A hA g hg m hm
  have hcL := GlobalTheory.SepClosedTorsion.card_torsion_eq (Ω := Ω) (Ω' := L) A hA hm
  have hpos : m ^ (2 * g) ≠ 0 := pow_ne_zero _ hm0
  haveI : Finite {x : ptOver K L ⟶ A // x ^ m = 1} := Nat.finite_of_card_ne_zero (by rw [← hcL, hcΩ]; exact hpos)
  let emb : (ptOver K Ω ⟶ A) →* (ptOver K L ⟶ A) := MonoidHom.mk' (fun x => ptOverMap j ≫ x) fun x y => MonObj.comp_mul _ x y
  have hemb : Function.Injective emb := by
    intro x y e
    have := epi_ptOverMap j
    exact Over.OverMorphism.ext ((cancel_epi (ptOverMap j).left).1
      (by simpa using congrArg (fun q => q.left) (show ptOverMap j ≫ x = ptOverMap j ≫ y from e)))
  let emb' : {x : ptOver K Ω ⟶ A // x ^ m = 1} → {x : ptOver K L ⟶ A // x ^ m = 1} :=
    fun x => ⟨emb x.1, by rw [← map_pow, x.2, map_one]⟩
  have hemb' : Function.Injective emb' := fun x y e => Subtype.ext (hemb (congrArg Subtype.val e))
  have hbij := hemb'.bijective_of_nat_card_le hcL.ge
  have step1 : ∀ y : ptOver K L ⟶ A, y ^ m = 1 → y ≫ f = 1 := by
    intro y hy
    obtain ⟨x, hx⟩ := hbij.2 ⟨y, hy⟩
    have hx' : ptOverMap j ≫ x.1 = y := congrArg Subtype.val hx
    rw [← hx', Category.assoc, hkill x.1 x.2, MonObj.comp_one]
  have hgp : IsGrpPullback ((Over.pullback t).obj A) A t (pullback.fst A.hom t) := isGrpPullback_pullback A t
  have hB : IsAbelianScheme ((Over.pullback t).obj A) := GlobalTheory.isAbelianScheme_pullback_obj t A hA
  obtain ⟨e, he⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hgp (𝟙 (Sp L)) t (Category.id_comp t).symm
  have hFf : IsMonHom ((Over.pullback t).map f) := inferInstance
  refine (GlobalTheory.TorsionDivisible.finite_torsion_and_divisible L _ hB m hmL).2 _ hFf ?_
  intro x hx
  apply e.injective
  have h1 : e x ^ m = 1 := by rw [← map_pow, hx, map_one]
  have h2 : e x ≫ f = 1 := step1 (e x) h1
  rw [map_one, ← h2]
  apply Over.OverMorphism.ext
  rw [he, Over.comp_left, Over.comp_left, he]
  simp
  rw [pullback.lift_fst]

end GlobalTheory.SepClosedDivisible

end
