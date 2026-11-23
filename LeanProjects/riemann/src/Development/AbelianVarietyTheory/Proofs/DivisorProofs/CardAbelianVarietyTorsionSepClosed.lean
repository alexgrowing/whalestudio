import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsUnconditional
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnramifiedExtTorsionPointsGoodReduction
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SepClosedTorsion

def ptOverHomEquiv {K L : Type} [Field K] [Field L] [Algebra K L] (X : Over (Sp K)) :
    (ptOver K L ⟶ X) ≃ {x : Sp L ⟶ X.left // x ≫ X.hom = spMap (algebraMap K L)} where
  toFun y := ⟨y.left, Over.w y⟩
  invFun x := Over.homMk x.1 x.2
  left_inv y := Over.OverMorphism.ext rfl
  right_inv x := rfl

theorem isUnit_natCast_top {K : Type} [Field K] {m : ℕ} (hm : (m : K) ≠ 0) : IsUnit (m : Γ(Sp K, ⊤)) := by
  simpa using (isUnit_iff_ne_zero.2 hm).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

theorem card_torsion_eq {K Ω Ω' : Type} [Field K] [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra K Ω']
    [IsSepClosed Ω] [IsSepClosed Ω'] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A) {m : ℕ}
    (hm : (m : K) ≠ 0) :
    Nat.card {x : ptOver K Ω ⟶ A // x ^ m = 1} = Nat.card {x : ptOver K Ω' ⟶ A // x ^ m = 1} := by
  obtain ⟨-, hfin, het⟩ := GrpTangent.finiteEtale_mulN_torsion A (hG := hA) (isUnit_natCast_top hm)
  rw [← Nat.card_congr (GlobalTheory.TorsionUnram.torsionEquiv A m _), ← Nat.card_congr (GlobalTheory.TorsionUnram.torsionEquiv A m _),
    Nat.card_congr (ptOverHomEquiv _), Nat.card_congr (ptOverHomEquiv _)]
  obtain ⟨z⟩ : Nonempty (Sp Ω) := inferInstance
  obtain ⟨z'⟩ : Nonempty (Sp Ω') := inferInstance
  rw [(FinEt.card_points_eq_finrank (torsion A m).hom (spMap (algebraMap K Ω)) z).2,
    (FinEt.card_points_eq_finrank (torsion A m).hom (spMap (algebraMap K Ω')) z').2]
  haveI : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  rw [Subsingleton.elim (spMap (algebraMap K Ω) z) (spMap (algebraMap K Ω') z')]

theorem card_torsion_algClosed {K L : Type} [Field K] [Field L] [IsAlgClosed L] [Algebra K L]
    (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A) {g : ℕ} (hg : SmoothOfRelativeDimension g A.hom)
    {m : ℕ} (hm : (m : K) ≠ 0) :
    Nat.card {x : ptOver K L ⟶ A // x ^ m = 1} = m ^ (2 * g) := by
  let t : Sp L ⟶ Sp K := spMap (algebraMap K L)
  letI : GrpObj ((Over.pullback t).obj A) := Functor.grpObjObj
  have hgp : IsGrpPullback ((Over.pullback t).obj A) A t (pullback.fst A.hom t) := isGrpPullback_pullback A t
  have hab : IsAbelianScheme ((Over.pullback t).obj A) := GlobalTheory.isAbelianScheme_pullback_obj t A hA
  have hdim : SmoothOfRelativeDimension g ((Over.pullback t).obj A).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hgp.1 hg
  obtain ⟨e, -⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hgp (𝟙 (Sp L)) t (Category.id_comp t).symm
  have hmL : (m : L) ≠ 0 := by
    intro h
    apply hm
    apply (algebraMap K L).injective
    simpa using h
  rw [← GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional L _ g m hab hdim hmL]
  exact Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun x => by
      change x ^ m = 1 ↔ e x ^ m = 1
      rw [← map_pow, map_eq_one_iff e e.injective]).symm

theorem card_torsion_sepClosed : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ g : ℕ, SmoothOfRelativeDimension g A.hom → ∀ m : ℕ, (m : K) ≠ 0 → Nat.card {x : ptOver K Ω ⟶ A // x ^ m = 1} = m ^ (2 * g) := by
  intro K Ω _ _ _ _ A _ hA g hg m hm
  rw [card_torsion_eq (Ω' := AlgebraicClosure Ω) A hA hm]
  exact card_torsion_algClosed A hA hg hm

end GlobalTheory.SepClosedTorsion
