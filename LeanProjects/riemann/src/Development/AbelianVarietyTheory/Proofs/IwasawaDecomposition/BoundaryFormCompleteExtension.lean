import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcPeriod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedUniformization
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryFormBaseChangeDvrStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.TraitCharRestrict

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t),
    IsCN R → P.TorsionIso →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V →
    ∀ ψ : R →+* V, Function.Injective ψ → ¬ (∀ r ∈ maximalIdeal R, ψ r ∈ maximalIdeal V) →
    ∀ (T : CDVR) (f : V →+* T.V), Function.Injective f → IsLocalHom f →
    ∀ u : SAB H (Sp T.V), SABMap u t (spMap f ≫ spMap ψ) → ∀ (P' : PELUnif (maximalIdeal T.V) u),
    ∃ r : P.D.toPre.X →ₗ[𝓞 E] P'.D.toPre.X, Function.Surjective r ∧
      ∀ y, ∃ (a : R) (b : T.V), PsiCoord P.D.toPre y a ∧ PsiCoord P'.D.toPre (r y) b ∧ Associated (f (ψ a)) b := by
  intro E _ _ _ H R _ _ _ t P hR hT V _ _ _ hV ψ hψ hnl T f hf hfl u hu P'
  have hg : ¬ IsLocalHom (f.comp ψ) := by
    intro hloc
    apply hnl
    intro r hr
    by_contra h
    have h1 : IsUnit (ψ r) := by
      by_contra h2
      exact h ((mem_maximalIdeal _).2 h2)
    have h2 : IsUnit ((f.comp ψ) r) := h1.map f
    exact ((mem_maximalIdeal _).1 hr) (hloc.map_nonunit r h2)
  have hsp : spMap (f.comp ψ) = spMap f ≫ spMap ψ := by
    simp only [spMap, ← Spec.map_comp]
    rfl
  have hT' : CDvr T.V := ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨ρ, hρ, hc⟩ := GlobalTheory.T.boundary_form_base_change_dvr E H R t P hR hT T.V hT' (f.comp ψ) (hf.comp hψ) hg u
    (by rw [hsp]; exact hu) P'
  refine ⟨ρ, hρ, fun y => ?_⟩
  haveI : CharZero R := hR.2.2.2
  obtain ⟨⟨a, ha, -⟩, -⟩ := GlobalTheory.PsiCoordLocal.main R P.D hR.2.1 y
  obtain ⟨⟨b, hb, -⟩, -⟩ := GlobalTheory.PsiCoordLocal.main T.V P'.D inferInstance (ρ y)
  exact ⟨a, b, ha, hb, hc y a b ha hb⟩

end GlobalTheory.TraitCharRestrict
