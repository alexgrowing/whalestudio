import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionEqAndWeilIsOfIsHolTo
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EpsPtScaleZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv

open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix Filter Topology MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open scoped ContDiff
open scoped CategoryTheory.Obj MonObj

namespace GlobalTheory.ExpCompare

theorem isHolTo_const {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}} (x : Sp ℂ ⟶ X) :
    IsHolTo (Set.univ : Set V) fun _ => x := fun U f =>
  ⟨by simpa only [Set.mem_univ, true_and] using isOpen_const, differentiableOn_const _⟩

theorem exists_equiv_of_exp : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S) (d : P.RiemannData y) (g : ℕ)
    (e : (Fin g → ℂ) → (Over.mk y ⟶ P.A)), (∀ z w, e (z + w) = e z * e w) → Function.Surjective e →
    IsHolTo Set.univ (fun z => (e z).left) →
    (∀ v : epsPt y ⟶ P.A, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left) →
    (∀ w, ∃! v : epsPt y ⟶ P.A, IsDerivAt0 (fun z => (e z).left) w v.left) →
    ∃ T : (Fin g → ℂ) ≃L[ℂ] (Fin P.g → ℂ), ∀ z, (e z).left = (d.u.ex (T z)).left ≫ d.φ := by
  intro S P y d g e hadd honto hhol h1 h2
  obtain ⟨Φ, hΦ⟩ := LiePull.exists_pushEquiv d.isPull (𝟙_ (Over (Sp ℂ))) y (Category.id_comp _).symm
  obtain ⟨t1, t2⟩ := UnifTangent.riemannData_tangent S P y d
  have hG : ∀ z, (Φ.symm (e z)).left ≫ d.φ = (e z).left := fun z => by
    rw [← hΦ, MulEquiv.apply_symm_apply]
  have hGhol : IsHolTo Set.univ fun z => (Φ.symm (e z)).left := by
    refine HolTorsion.isHolTo_of_isPullback d.isPull.1 ?_ ?_
    · exact HolTorsion.isHolTo_congr hhol fun z _ => hG z
    · exact HolTorsion.isHolTo_congr (isHolTo_const (𝟙 _)) fun z _ => Over.w (Φ.symm (e z))
  obtain ⟨F, hF, -⟩ := existsUnique_linear_lift_of_isHolTo d.B
    (PolPull.isAbelianScheme_of_isGrpPullback P.isAb d.isPull) d.L P.g g d.u t1 t2 (fun z => Φ.symm (e z))
    (fun z w => by rw [hadd, map_mul]) hGhol
  have hFe : ∀ z, (e z).left = (d.u.ex (F z)).left ≫ d.φ := fun z => by rw [hF, hG]
  haveI := d.u.discrete
  have hsurj : LinearMap.range F = ⊤ := AHWeil.eq_top_of_add_discrete d.u.Λ _ fun w => by
    obtain ⟨z, hz⟩ := honto (Φ (d.u.ex w))
    refine ⟨⟨w - F z, (d.u.ker _).1 ?_⟩, z, by simp⟩
    have h := d.u.ex_add (w - F z) (F z)
    rw [sub_add_cancel, hF, hz, MulEquiv.symm_apply_apply] at h
    exact mul_eq_right.1 h.symm
  have hu : IsHolTo Set.univ fun z => (d.u.ex z).left ≫ d.φ :=
    HolTorsion.isHolTo_comp (c := fun z => (d.u.ex z).left)
      (fun U f => by simpa only [Set.mem_univ, true_and] using d.u.hol U f) d.φ
  have hd : ∀ w v, IsDerivAt0 (fun z => (e z).left) w v ↔
      IsDerivAt0 (fun z => (d.u.ex z).left ≫ d.φ) (F w) v := fun w v => by
    rw [funext hFe]
    exact PointUnif.deriv_linear hu F
  have hinj : Function.Injective F := fun w w' h => by
    obtain ⟨v, hv, -⟩ := h2 w
    exact (h1 v hv.1).unique hv ((hd _ _).2 (h ▸ (hd _ _).1 hv))
  exact ⟨(LinearEquiv.ofBijective F ⟨hinj, LinearMap.range_eq_top.1 hsurj⟩).toContinuousLinearEquiv, hFe⟩

end GlobalTheory.ExpCompare
