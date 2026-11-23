import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsE8WeightedBundle
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.E8Fibration

theorem isProd_pullback_iso : ∀ {S S' : Scheme.{0}} (f : S' ⟶ S) {A B : Over S} [GrpObj A] [GrpObj B] (pr : Fin 8 → (A ⟶ B)), E8Fibration.IsProd pr → ∀ (P : Over S') [GrpObj P] (i : (Over.pullback f).obj A ≅ P), IsMonHom i.hom → E8Fibration.IsProd (fun a => i.inv ≫ (Over.pullback f).map (pr a)) := by
  intro S S' f A B _ _ pr hpr P _ i hi
  obtain ⟨hmon, huniv⟩ := hpr
  refine ⟨fun a => ?_, fun T y => ?_⟩
  · haveI := hmon a
    infer_instance
  · let adj := Over.mapPullbackAdj f
    obtain ⟨x', hx', hu⟩ := huniv ((Over.map f).obj T) (fun a => (adj.homEquiv T B).symm (y a))
    refine ⟨adj.homEquiv T A x' ≫ i.hom, fun a => ?_, fun x hx => ?_⟩
    · simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [← Adjunction.homEquiv_naturality_right, hx' a, Equiv.apply_symm_apply]
    · have h1 : (adj.homEquiv T A).symm (x ≫ i.inv) = x' := by
        apply hu
        intro a
        rw [← Adjunction.homEquiv_naturality_right_symm, Category.assoc, hx a]
      rw [← h1, Equiv.apply_symm_apply, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end GlobalTheory.Poinc.Sep.E8Fibration

end
