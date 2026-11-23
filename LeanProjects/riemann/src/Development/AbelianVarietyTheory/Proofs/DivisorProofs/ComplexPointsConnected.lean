import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PreconnectedSpacePtsOfIsIntegral
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.Mean4O

theorem connectedSpace_pts : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (σ : F →+* ℂ), ConnectedSpace (Pts Y σ) := by
  intro F _ _ Y σ
  have hI : IsIntegral (pullback Y.str (spMap σ)) :=
    GeometricallyIntegral.geometrically_isIntegral (f := Y.str) (spMap σ) _ _ (IsPullback.of_hasPullback Y.str (spMap σ))
  have hP := GlobalTheory.OpenSubgroupPts.preconnectedSpace_pts_of_isIntegral (pullback.snd Y.str (spMap σ))
  let f : GlobalTheory.Points.Pts (pullback.snd Y.str (spMap σ)) → Pts Y σ := fun y =>
    ⟨y.1 ≫ pullback.fst _ _, by rw [Category.assoc, pullback.condition, ← Category.assoc, y.2, Category.id_comp]⟩
  have hc : Continuous f := ((GlobalTheory.Points.continuous_comp (C := ℂ) (pullback.fst Y.str (spMap σ))).comp continuous_subtype_val).subtype_mk _
  have hs : Function.Surjective f := fun z =>
    ⟨⟨pullback.lift z.1 (𝟙 _) (by rw [z.2, Category.id_comp]), pullback.lift_snd _ _ _⟩,
      Subtype.ext (pullback.lift_fst _ _ _)⟩
  obtain ⟨z⟩ : Nonempty (Pts Y σ) := inferInstance
  obtain ⟨y, -⟩ := hs z
  have : ConnectedSpace (GlobalTheory.Points.Pts (pullback.snd Y.str (spMap σ))) := ⟨⟨y⟩⟩
  exact hs.connectedSpace hc

end GlobalTheory.Mean4O
